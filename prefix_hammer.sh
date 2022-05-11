#!/usr/bin/env sh

read -r -d '' VAR << EOM
From Hammer Require Import Hammer.

Ltac auto_eval_try_ind base_tac := 
  multimatch goal with 
  | |- forall (X: _), _ => 
    intros X; auto_eval_try_ind base_tac
  | |- ?X -> _ => 
    intros X; auto_eval_try_ind base_tac
  | |- forall (X: _), _ => 
    induction X; intros; base_tac
  | |- ?X -> _ => 
    induction X; intros; base_tac
  | _ => base_tac
  end.

Ltac auto_eval_wrapper base := 
  try base; 
  auto_eval_try_ind base.

Set Hammer ATPLimit 3.

EOM

echo "$VAR"

mv $1 $1.temp; echo "$VAR" > $1; cat $1.temp >> $1; rm $1.temp