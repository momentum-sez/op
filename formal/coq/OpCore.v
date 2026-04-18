(* Op Core — Coq scaffold.
   Placeholder for the mechanized core calculus.
   The target obligations are listed in formal/README.md. *)

(* Minimal scaffold: the type of Op base sorts. *)
Inductive OpSort : Type :=
  | Unit
  | Bool
  | Int
  | String
  | EntityRef
  | JurisdictionRef
  | MoneyAmount
  | ContentDigest
  | CallbackEvent.

(* Placeholder lemma: reflexivity of sort equality. *)
Theorem op_sort_refl : forall s : OpSort, s = s.
Proof. intros s. reflexivity. Qed.
