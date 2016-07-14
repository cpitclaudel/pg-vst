;;; pg-vst.el --- Proof General extensions for Princeton's VST  -*- lexical-binding: t; -*-

;; Copyright (C) 2016  Clément Pit-Claudel

;; Author: Clément Pit-Claudel <clement@clem-w50-mint>
;; Keywords: languages

;; This file is not part of GNU Emacs.

;; Permission is hereby granted, free of charge, to any person obtaining a copy
;; of this software and associated documentation files (the "Software"), to deal
;; in the Software without restriction, including without limitation the rights
;; to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
;; copies of the Software, and to permit persons to whom the Software is
;; furnished to do so, subject to the following conditions:

;; The above copyright notice and this permission notice shall be included in all
;; copies or substantial portions of the Software.

;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;; IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;; FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;; AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;; LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
;; OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
;; SOFTWARE.

;;; Commentary:

;; This file adds VST-specific support to Proof General.  See the README for
;; more information.

;;; Code:

(require 'cc-cmds)

(defgroup pg-vst nil
  "VST support in Proof General."
  :group 'pg)

;;; C formatting

(defun pg-vst--format-raw (any)
  (insert (format "%s" any)))

(defun pg-vst--format-ident (id)
  (insert
   (replace-regexp-in-string
    "^_+" ""
    (replace-regexp-in-string
     "\\(.*\\)%positive" "$\\1"
     (symbol-name id) t)
    t)))

(defun pg-vst--format-unop (unop)
  (pg-vst--format-raw (pcase unop
                        (`Onotbool "!")
                        (`Onotint "~")
                        (`Oneg "-")
                        (`Oabsfloat "__builtin_fabs"))))

(defun pg-vst--format-binop (binop)
  (pg-vst--format-raw (pcase binop
                        (`Oadd "+")
                        (`Osub "-")
                        (`Omul "*")
                        (`Odiv "/")
                        (`Omod "%")
                        (`Oand "&")
                        (`Oor "|")
                        (`Oxor "^")
                        (`Oshl "<<")
                        (`Oshr ">>")
                        (`Oeq "==")
                        (`One "!=")
                        (`Olt "<")
                        (`Ogt ">")
                        (`Ole "<=")
                        (`Oge ">="))))

(defun pg-vst--format-int (int)
  (pg-vst--format-raw (pcase int
                        (`(Int.repr ,num) num)
                        (any any))))

(defun pg-vst--format-float (float)
  (pg-vst--format-raw float))

(defun pg-vst--format-float32 (float32)
  (pg-vst--format-raw float32))

(defun pg-vst--format-int64 (int64)
  (pg-vst--format-raw int64))

(defun pg-vst--split-list (delim elems)
  (let ((output nil)
        (acc nil))
    (while elems
      (pcase (pop elems)
        ((pred (equal delim))
         (push (nreverse acc) output)
         (setq acc nil))
        (atom
         (push atom acc))))
    (nreverse (cons (nreverse acc) output))))

(defun pg-vst--coq-list-to-list-1 (seq)
  (pcase seq
    ((or `(cons ,hd ,tl) `(,hd :: . ,tl))
     (cons hd (pg-vst--coq-list-to-list tl)))
    ((pred vectorp)
     (pg-vst--split-list ':: (append seq nil)))))

(defun pg-vst--coq-list-to-list (seq)
  (mapcar (lambda (x) (pcase x (`(,x) x) (_ x)))
          (pg-vst--coq-list-to-list-1 seq)))

;; (pg-vst--coq-list-to-list '(a :: b :: c :: nil))
;; (pg-vst--coq-list-to-list '[a :: b :: c])
;; (pg-vst--coq-list-to-list '[a :: b c d :: e])
;; (pg-vst--coq-list-to-list '[b c d])

(defun pg-vst--format-type (type)
  (pcase type
    (`tvoid (pg-vst--format-raw "void"))
    (`tschar (pg-vst--format-raw "schar"))
    (`tuchar (pg-vst--format-raw "uchar"))
    (`tshort (pg-vst--format-raw "short"))
    (`tushort (pg-vst--format-raw "ushort"))
    (`tint (pg-vst--format-raw "int"))
    (`tuint (pg-vst--format-raw "uint"))
    (`tbool (pg-vst--format-raw "bool"))
    (`tlong (pg-vst--format-raw "long"))
    (`tulong (pg-vst--format-raw "ulong"))
    (`tfloat (pg-vst--format-raw "float"))
    (`tdouble (pg-vst--format-raw "double"))
    (`(tptr ,type) "*" (pg-vst--format-type type))
    (`(tarray ,type ,size) (pg-vst--format-type type) (pg-vst--format-raw "[") (pg-vst--format-raw size) (pg-vst--format-raw "]"))
    (any (pg-vst--format-raw any))))

(defun pg-vst--format-expr (expr)
  (pcase expr
    (`(Econst_int ,int ,_type)
     (pg-vst--format-int int))
    (`(Econst_float ,float ,_type)
     (pg-vst--format-float float))
    (`(Econst_single ,float32 ,_type)
     (pg-vst--format-float32 float32))
    (`(Econst_long ,int64 ,_type)
     (pg-vst--format-int64 int64))
    (`(Evar ,ident ,_type)
     (pg-vst--format-ident ident))
    (`(Etempvar ,ident ,_type)
     (pg-vst--format-ident ident))
    (`(Ederef ,expr ,_type)
     (pg-vst--format-raw "*(")
     (pg-vst--format-expr expr)
     (pg-vst--format-raw ")"))
    (`(Eaddrof ,expr ,_type)
     (pg-vst--format-raw "&(")
     (pg-vst--format-expr expr)
     (pg-vst--format-raw ")"))
    (`(Eunop ,unary_operation ,expr ,_type)
     (pg-vst--format-unop unary_operation)
     (pg-vst--format-raw "(")
     (pg-vst--format-expr expr)
     (pg-vst--format-raw ")"))
    (`(Ebinop ,binary_operation ,expr1 ,expr2 ,_type)
     (pg-vst--format-raw "(")
     (pg-vst--format-expr expr1)
     (pg-vst--format-raw " ")
     (pg-vst--format-binop binary_operation)
     (pg-vst--format-raw " ")
     (pg-vst--format-expr expr2)
     (pg-vst--format-raw ")"))
    (`(Ecast ,expr ,type)
     (pg-vst--format-raw "(")
     (pg-vst--format-type type)
     (pg-vst--format-raw ")")
     (pg-vst--format-expr expr))
    (`(Efield ,expr ,ident ,_type)
     (pcase expr
       (`(Ederef ,expr ,_type)
        (pg-vst--format-expr expr))
       (_ "!!??"))
     (pg-vst--format-raw "->")
     (pg-vst--format-ident ident))
    (`(Esizeof ,_type1 ,_type2)
     (pg-vst--format-raw "!! SIZEOF")
     (pg-vst--format-raw expr))
    (`(Ealignof ,_type1 ,_type2)
     (pg-vst--format-raw "!! ALIGNOF")
     (pg-vst--format-raw expr))))

(defun pg-vst--format-stmt (prog)
  (pcase prog
    (`Sskip
     (insert "skip;"))
    (`(Sassign ,lv ,rv)
     (pg-vst--format-expr lv)
     (pg-vst--format-raw " = ")
     (pg-vst--format-expr rv)
     (pg-vst--format-raw ";"))
    (`(Sset ,ident ,expr)
     (pg-vst--format-ident ident)
     (pg-vst--format-raw " = ")
     (pg-vst--format-expr expr)
     (pg-vst--format-raw ";"))
    (`(Scall ,opt_ident ,expr ,consed_exprs)
     (pcase opt_ident
       (`(Some ,ident)
        (pg-vst--format-ident ident)
        (pg-vst--format-raw " = ")))
     (pg-vst--format-expr expr)
     (pg-vst--format-raw "(") ;; FIXME map
     (let ((exprs (pg-vst--coq-list-to-list consed_exprs)))
       (while exprs
         (pg-vst--format-expr (pop exprs))
         (when exprs
           (pg-vst--format-raw ", "))))
     (pg-vst--format-raw ")")
     (pg-vst--format-raw ";"))
    (`(Sbuiltin ,_opt_ident ,_external_function ,_typelist ,_exprs)
     (pg-vst--format-raw "!!BUILTIN")
     (pg-vst--format-raw ";"))
    (`(Ssequence ,st1 ,st2)
     (pg-vst--format-stmt st1)
     (pg-vst--format-raw "\n")
     (pg-vst--format-stmt st2))
    (`(Sifthenelse ,test ,tbranch ,fbranch)
     (pg-vst--format-raw "if (")
     (pg-vst--format-expr test)
     (pg-vst--format-raw ") {\n")
     (pg-vst--format-stmt tbranch)
     (pg-vst--format-raw "\n} else {\n")
     (pg-vst--format-stmt fbranch)
     (pg-vst--format-raw "\n}"))
    (`(Sloop ,_statement1 ,_statement2)
     (pg-vst--format-raw "!!LOOP"))
    (`(Sbreak)
     (pg-vst--format-raw "break;"))
    (`(Scontinue)
     (pg-vst--format-raw "continue;"))
    (`(Sreturn ,opt_expr)
     (pg-vst--format-raw "return")
     (pcase opt_expr
       (`(Some ,expr)
        (pg-vst--format-raw " ")
        (pg-vst--format-expr expr)))
     (pg-vst--format-raw ";"))
    (`(Sswitch ,_expr ,_labeled_statements)
     (pg-vst--format-raw "!!SWITCH"))
    (`(Slabel ,_label ,_statement)
     (pg-vst--format-raw "!!LABEL"))
    (`(Sgoto ,_label)
     (pg-vst--format-raw "!!GOTO"))
    (`(Swhile ,expr ,statement)
     (pg-vst--format-raw "while (")
     (pg-vst--format-expr expr)
     (pg-vst--format-raw ") {\n")
     (pg-vst--format-stmt statement)
     (pg-vst--format-raw "\n}"))
    (`(,wrapped)
     (pg-vst--format-stmt wrapped))
    (any
     (error "Unrecognized form %S" any))))

;;; Goal display

(defface pg-vst-c-face
  '((((type tty) (class mono)) :inherit region)
    (t :inherit nil :weight normal :slant normal))
  "Face applied to C code in VST mode."
  :group 'vst)

(defface pg-vst-spacer-face
  '((((type tty) (class mono)) :inherit region)
    (t :inherit region :height 5 :line-height 1.5))
  "Face of the thin line around C code in VST mode."
  :group 'vst)

(defun pg-vst--convert-font-lock-faces ()
  "Replace face properties by font-lock-face properties."
  (goto-char (point-min))
  (while (not (eobp))
    (let ((pos (point)))
      (goto-char (next-single-property-change pos 'face nil (point-max)))
      (put-text-property pos (point) 'font-lock-face (get-text-property pos 'face)))))

(defun pg-vst--add-prefix (prefix skip)
  "Add PREFIX to each line after the first SKIP ones."
  (goto-char (point-min))
  (forward-line skip)
  (while (not (eobp))
    (insert prefix)
    (forward-line 1)))

(defun pg-vst--format-buffer-as-c (&optional prefix)
  (setq prefix (or prefix ""))
  (delay-mode-hooks (c-mode))
  (c-set-style "java")
  (c-indent-region (point-min) (point-max) t)
  (if (fboundp 'font-lock-ensure) (font-lock-ensure)
    (with-no-warnings (font-lock-fontify-buffer)))
  (pg-vst--add-prefix "" 0)
  (font-lock-append-text-property (point-min) (point-max) 'face 'pg-vst-c-face)
  (pg-vst--convert-font-lock-faces)
  (pg-vst--add-prefix prefix 1))

(defun pg-vst--format-prog (prog prefix)
  (with-temp-buffer
    (pg-vst--format-stmt prog)
    (insert "\n")
    (pg-vst--format-buffer-as-c prefix)
    (buffer-string)))

;; (require 'dash)
;;
;; (defun company-coq--ask-prover-then-rewind (&rest cmds)
;;   "Run CMDS, then rewind to state before running them."
;;   (unless proof-shell-busy
;;     (-when-let* ((statenum (car (coq-last-prompt-info-safe))))
;;       (unwind-protect
;;           (let* ((proof-shell-eager-annotation-start nil)
;;                  (proof-shell-eager-annotation-end nil)
;;                  (retval nil)) ;; Disable capture of urgent messages
;;             (dolist (cmd cmds retval)
;;               (setq retval (company-coq-ask-prover-swallow-errors cmd))))
;;         (company-coq-ask-prover (format "BackTo %d." statenum))))))

(defvar pg-vst--overlay-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "<mouse-1>") #'pg-vst--kill-overlay)
    (define-key map (kbd "<mouse-3>") #'pg-vst--kill-overlay)
    map))

(defun pg-vst--parse (prog)
  "Parse CLight program PROG.
PROG must be wrapped in [[[__PROG__ ]]].  The only difficulty
beyond parsing sexps is parsing lists of elements."
  (pcase-dolist (`(,from . ,to) '((";" . " :: ") ("[" . "  [ ") ("]" . "  ] ")))
    (setq prog (replace-regexp-in-string
                (regexp-quote from) (replace-quote to) prog)))
  (cdr (append (aref (aref (read prog) 0) 0) nil)))

(pg-vst--parse "[[[__PROG__ (Seq [1;Seq a [1;2];3] (1 :: 2 :: 3 :: nil) (Argh (urgh [2])))]]]")

(defun pg-vst--add-overlays ()
  "Add VST overlays to current buffer, if needed."
  (save-excursion
    (goto-char (point-min))
    (while (search-forward "[[[__PROG__" nil t)
      (dotimes (_ 3) (backward-up-list))
      (let* ((prefix (make-string (current-indentation) ?\s))
             (beg (progn (skip-syntax-backward "-") (point)))
             (end (progn (forward-list) (skip-syntax-forward "-") (point)))
             (prog (buffer-substring beg end))
             (sexp (pg-vst--parse prog))
             (sep (propertize "\n" 'font-lock-face 'pg-vst-spacer-face))
             (sep-prefix "")
             (c-prog (concat "\n" sep-prefix sep
                             prefix (pg-vst--format-prog sexp prefix)
                             sep-prefix sep prefix))
             (ov (make-overlay beg end)))
        (overlay-put ov 'pg-vst t)
        (overlay-put ov 'keymap pg-vst--overlay-map)
        (overlay-put ov 'help-echo (buffer-substring-no-properties beg end))
        (overlay-put ov 'display c-prog)))))

;; FIXME imported from company-coq
(defmacro pg-vst--with-point-at-click (evt &rest body)
  "Set buffer, window, and point from EVT, then run BODY."
  (declare (indent defun)
           (debug t))
  `(let* ((--position (event-start ,evt))
          (--window (posn-window --position))
          (--buffer (window-buffer --window)))
     (with-selected-window --window
       (with-current-buffer --buffer
         (goto-char (posn-point --position))
         ,@body))))

(defun pg-vst--kill-overlay (evt)
  "Kill overlay pointed to by mouse event EVT."
  (interactive "e")
  (pg-vst--with-point-at-click evt
    (dolist (ov (overlays-at (point)))
      (when (overlay-get ov 'pg-vst)
        (delete-overlay ov)))))

(defun pg-vst--update-goals (&optional inhibit)
  "Add VST overlays to goals buffer.
With non-nil INHIBIT, remove them instead."
  (when (buffer-live-p proof-goals-buffer)
    (with-current-buffer proof-goals-buffer
      (dolist (ov (overlays-in (point-min) (point-max)))
        (when (overlay-get ov 'pg-vst)
          (delete-overlay ov)))
      (unless inhibit
        (pg-vst--add-overlays)))))

(defun pg-vst--delayed-output-hook ()
  "Possibly add VST overlays to current buffer."
  (unless (memq 'no-goals-display proof-shell-delayed-output-flags)
    (pg-vst--update-goals)))

;;; Syntax highlighting

(defconst pg-vst-symbols '(("|--" . ?\⟝)
                     ("-o" . ?⊸)
                     ("|>" . ?▹)
                     ("!!" . ?‼)))

(defconst pg-vst-keywords '("DECLARE" "WITH" "OF" "PRE" "POST" "PROP" "LOCAL"
                      "SEP" "EX" "ALL" "ENTAIL")
  "VST-specific keywords.")

(defconst pg-vst-keywords-regexp (regexp-opt pg-vst-keywords 'symbols)
  "Regexp matching VST-specific keywords.")

(defconst pg-vst-font-lock-form `((,pg-vst-keywords-regexp . font-lock-builtin-face))
  "Font-lock keywords for VST.")

(defun pg-vst-register-keywords ()
  "Ensure that VST's keywords are properly highlighted."
  (font-lock-add-keywords nil pg-vst-font-lock-form))

(defun pg-vst-unregister-keywords ()
  "Remove VST-specific highlighting."
  (font-lock-remove-keywords nil pg-vst-font-lock-form))

;;; Minor mode

(defvar pg-vst-mode nil)

(defun pg-vst--refresh-font-lock ()
  "Recompute font-locking for current buffer."
  (when (and (fboundp 'prettify-symbols-mode) prettify-symbols-mode)
    (prettify-symbols-mode -1)
    (prettify-symbols-mode))
  (if (fboundp 'font-lock-ensure)
      (progn (font-lock-flush) (font-lock-ensure))
    (with-no-warnings (font-lock-fontify-buffer))))

;;;###autoload
(define-minor-mode pg-vst-mode
  "VST-specific extensions for PG."
  :global t
  :lighter " VST"
  (let ((hook-fn (if pg-vst-mode #'add-hook #'remove-hook))
        (kwd-fn (if pg-vst-mode #'pg-vst-register-keywords #'pg-vst-unregister-keywords))
        (symbols (if pg-vst-mode (append prettify-symbols-alist pg-vst-symbols)
                   (cl-set-difference prettify-symbols-alist pg-vst-symbols
                                      :test #'equal))))
    (funcall hook-fn 'coq-mode-hook #'pg-vst-register-keywords)
    (funcall hook-fn 'coq-goals-mode-hook #'pg-vst-register-keywords)
    (funcall hook-fn 'coq-response-mode-hook #'pg-vst-register-keywords)
    (funcall hook-fn 'proof-shell-handle-delayed-output-hook #'pg-vst--delayed-output-hook)
    (dolist (buf (buffer-list))
      (with-current-buffer buf
        (when (memq major-mode '(coq-mode coq-response-mode coq-goals-mode))
          (setq-local prettify-symbols-alist symbols)
          (funcall kwd-fn)
          (pg-vst--refresh-font-lock)))))
  (pg-vst--update-goals (not pg-vst-mode)))

(provide 'pg-vst)
;;; pg-vst.el ends here
