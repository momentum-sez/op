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

(** * Decidable equality + distinctness (2026-04-20) *)

Lemma op_sort_eq_dec : forall s1 s2 : OpSort, {s1 = s2} + {s1 <> s2}.
Proof. decide equality. Qed.

(** The nine base sort constructors are all pairwise distinct. *)
Lemma op_sort_ctors_partial_distinct :
  Unit <> Bool /\
  Bool <> Int /\
  Int <> String /\
  String <> EntityRef /\
  EntityRef <> JurisdictionRef /\
  JurisdictionRef <> MoneyAmount /\
  MoneyAmount <> ContentDigest /\
  ContentDigest <> CallbackEvent.
Proof. repeat split; discriminate. Qed.

(** Sort equality is symmetric. *)
Lemma op_sort_eq_symm : forall (s1 s2 : OpSort), s1 = s2 -> s2 = s1.
Proof. intros s1 s2 H. symmetry. exact H. Qed.

(** Sort equality is transitive. *)
Lemma op_sort_eq_trans :
  forall (s1 s2 s3 : OpSort), s1 = s2 -> s2 = s3 -> s1 = s3.
Proof. intros s1 s2 s3 H1 H2. rewrite H1. exact H2. Qed.
