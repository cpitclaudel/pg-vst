======================================================================
 PG-VST: Proof General extensions for the Verified Software Toolchain
======================================================================

What is it?
===========

.. image:: pg-vst.gif


How do I use it?
================

* Clone this repo::

    git clone https://github.com/cpitclaudel/pg-vst/ ~/.emacs.d/lisp/pg-vst/

* Register the package by adding the following to your ``.emacs``::

    (with-eval-after-load 'coq
      (load-file "~/.emacs.d/lisp/pg-vst/pg-vst.el")
      (add-hook #'coq-mode-hook #'pg-vst-mode))

* Enable PG-VST in a Coq session with ``M-x pg-vst-mode``.  You'll need to add the following to your file first, though (after ``Require Import floyd.proofauto.``)::

    (** <PG-VST> **)
    Definition __PG_VST_TOGGLE__ :=
      (* Global switch: do we want to massage the goal for PG-VST? *)
      True.

    Ltac __is_transparent symbol :=
      (* Fail is ‘symbol’ is opaque; otherwise, do nothing. *)
      match goal with
      | _ => let __ := (eval unfold symbol in symbol) in idtac
      | _ => fail 1 symbol "is not transparent"
      end.

    Ltac __pg_vst_post_processor :=
      (* If __PG_VST_TOGGLE__ is opaque, unfold abbreviated [statement]s; otherwise, do nothing. *)
      first [ __is_transparent __PG_VST_TOGGLE__ |
              repeat match goal with
                     | [ H := abbreviate : statement |- _ ] =>
                       unfold abbreviate in H; unfold H; clear H
                     end ].

    Notation "'__PG_VST_SEMAX__'  A B  '[[[__PROG__'  P  ']]]'  C" :=
      (* This notation wraps ‘P’ in easily-detectable tags.
           PG-VST opens the corresponding scope in the background. *)
      (semax A B P C) (at level 200) : __pg_vst_scope.

    Open Scope __pg_vst_scope.
    Opaque __PG_VST_TOGGLE__.

    Ltac abbreviate_semax ::=
     match goal with
     | |- semax _ _ _ _ =>
            simplify_Delta;
            unfold_abbrev';
            match goal with |- semax ?D _ ?C ?P =>
               abbreviate D : tycontext as Delta;
                abbreviate P : ret_assert as POSTCONDITION;
                match C with
                | Ssequence ?C1 ?C2 =>
                   (* use the next 3 lines instead of "abbreviate"
                      in case C1 contains an instance of C2 *)
                    let MC := fresh "MORE_COMMANDS" in
                    pose (MC := @abbreviate _ C2);
                    change C with (Ssequence C1 MC);
                    match C1 with
                    | Swhile _ ?C3 => abbreviate C3 as LOOP_BODY
                    | _ => idtac
                    end
                | Swhile _ ?C3 => abbreviate C3 as LOOP_BODY
                | _ => idtac
                end
            end
     | |- _ |-- _ => unfold_abbrev_ret
     | |- _ => idtac
     end;
     clear_abbrevs;
     (*build_Struct_env;*)
     simpl typeof;
     __pg_vst_post_processor.
    (** </PG-VST> **)

  (Hopefully this snippet can be simplified if there's interest in using this code).

Try it on ``progs/verif-reverse.v`` in VST's source tree!

How does this work?
===================

A special notation is used to make C snippets easy to locate within the ``semax`` construct; with this notation in place, each time a new goal is displayed, PG-VST makes a pass on the goals, extracts each C snippet, pretty-prints the AST, syntax-highlights and indents the resulting C code with Emacs' C mode, and inserts the results in the goals buffer.

The pretty-printer only supports a subset of VST's C at the moment; it should be easy to extend it.
