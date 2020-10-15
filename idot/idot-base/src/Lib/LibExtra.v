(** remove printing ~ *)

Set Implicit Arguments.

Require Export Coq.Program.Basics.
From TLC Require Export LibVar LibLN.

Require Export LibExtraProgram.
Require Export LibExtraList.
Require Export LibExtraFset.
Require Export LibExtraVar.
Require Export LibExtraEnv.
Require Export LibExtraBool.
Require Export LibExtraSubstFvar.

Module Nat := PeanoNat.Nat.

Ltac intros_fun_ext :=
  repeat (apply fun_ext_dep; intro).
