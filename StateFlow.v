From Coq Require Import ssreflect.
Require Import List.

Inductive state_diag :=
| POWERON
| IDLE : nat -> state_diag
| DETECT : nat -> state_diag.

Inductive input_port :=
| INPUT : bool -> bool -> bool -> input_port.

Variables reset_IDLE reset_DETECT : nat.

Definition transition (s : state_diag) (p : input_port) :=
  match s, p with
  | POWERON, INPUT _  _ _ => IDLE reset_IDLE
  | IDLE n, INPUT false true _ => match n with
                              | O => DETECT reset_DETECT
                              | S O => DETECT reset_DETECT
                              | S m => IDLE m
                              end
  | IDLE _, INPUT true _ _ => IDLE reset_IDLE
  | IDLE _, INPUT _ false _ => IDLE reset_IDLE
  | DETECT n, INPUT false _ true => match n with
                                    | O => IDLE reset_IDLE
                                    | S O => IDLE reset_IDLE
                                    | S m => DETECT m
                                    end
  | DETECT _, INPUT true _ _ => DETECT reset_DETECT
  | DETECT _, INPUT _ _ false => DETECT reset_DETECT 
end.


Fixpoint block_states (s : state_diag) (ts : list input_port) :=
  match ts with
  | nil => nil
  | x :: xs =>
    let cur_state := transition s x in
    cur_state :: block_states cur_state xs
  end.


Definition block_output (s : state_diag) :=
  match s with
  | DETECT _ => true
  | _ => false
  end.

Definition block_outputs (ts : list input_port) :=
  map block_output (block_states POWERON ts).
