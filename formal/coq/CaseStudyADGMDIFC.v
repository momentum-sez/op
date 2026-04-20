From Stdlib Require Import String.
Require Import CompilationSoundness.

Open Scope string_scope.

Definition adgm_difc_sanctions_term : SanctLexTerm :=
  SLT_Sanctions (SLT_Const (LV_Str "tx:adgm-difc-commit")).

Definition adgm_fit_and_proper_witness : FillWitness :=
  {|
    fill_authority := "ADGM.FSRA";
    fill_digest := "pcauth:fit-and-proper:adgm";
    fill_timestamp := "2026-04-19T00:00:00Z"
  |}.

Definition difc_approved_person_witness : FillWitness :=
  {|
    fill_authority := "DIFC.DFSA";
    fill_digest := "pcauth:approved-person:difc";
    fill_timestamp := "2026-04-19T00:00:00Z"
  |}.

Definition mutual_recognition_witness : FillWitness :=
  {|
    fill_authority := "ADGM-DIFC.Corridor";
    fill_digest := "bridge:mutual-recognition:adgm-difc";
    fill_timestamp := "2026-04-19T00:00:00Z"
  |}.

Definition adgm_fit_and_proper_fill : FillLexTerm :=
  FLT_Fill "fit_and_proper_adgm" (LV_Str "Compliant") adgm_fit_and_proper_witness.

Definition difc_approved_person_fill : FillLexTerm :=
  FLT_Fill "approved_person_difc" (LV_Str "Compliant") difc_approved_person_witness.

Definition adgm_difc_mutual_recognition_fill : FillLexTerm :=
  FLT_Fill "MutualRecognition" (LV_Str "BridgeOk") mutual_recognition_witness.

(** * Witness structural properties (2026-04-20) *)

(** The three fill-witnesses come from distinct authorities. *)
Theorem witness_authorities_distinct :
  fill_authority adgm_fit_and_proper_witness <> fill_authority difc_approved_person_witness /\
  fill_authority adgm_fit_and_proper_witness <> fill_authority mutual_recognition_witness /\
  fill_authority difc_approved_person_witness <> fill_authority mutual_recognition_witness.
Proof. repeat split; discriminate. Qed.

(** All three witnesses share the 2026-04-19T00:00:00Z timestamp. *)
Theorem witness_timestamps_agree :
  fill_timestamp adgm_fit_and_proper_witness = fill_timestamp difc_approved_person_witness /\
  fill_timestamp difc_approved_person_witness = fill_timestamp mutual_recognition_witness.
Proof. split; reflexivity. Qed.

(** The three digests are distinct (no witness reuse). *)
Theorem witness_digests_distinct :
  fill_digest adgm_fit_and_proper_witness <> fill_digest difc_approved_person_witness /\
  fill_digest adgm_fit_and_proper_witness <> fill_digest mutual_recognition_witness /\
  fill_digest difc_approved_person_witness <> fill_digest mutual_recognition_witness.
Proof. repeat split; discriminate. Qed.

(** The ADGM witness is for the ADGM.FSRA authority. *)
Theorem adgm_witness_authority :
  fill_authority adgm_fit_and_proper_witness = "ADGM.FSRA".
Proof. reflexivity. Qed.

(** The DIFC witness is for the DIFC.DFSA authority. *)
Theorem difc_witness_authority :
  fill_authority difc_approved_person_witness = "DIFC.DFSA".
Proof. reflexivity. Qed.

(** The mutual-recognition witness is from the cross-zone corridor. *)
Theorem mutual_recognition_authority :
  fill_authority mutual_recognition_witness = "ADGM-DIFC.Corridor".
Proof. reflexivity. Qed.

Theorem case_study_adgm_difc_commit_sound :
  (forall vv,
      sanct_lex_verdict adgm_difc_sanctions_term vv <->
      sanct_op_verdict (sanct_compile adgm_difc_sanctions_term) vv) /\
  (forall vv,
      fill_lex_verdict adgm_fit_and_proper_fill vv <->
      fill_op_weak_verdict (fill_compile adgm_fit_and_proper_fill) vv) /\
  (forall vv,
      fill_lex_verdict difc_approved_person_fill vv <->
      fill_op_weak_verdict (fill_compile difc_approved_person_fill) vv) /\
  (forall vv,
      fill_lex_verdict adgm_difc_mutual_recognition_fill vv <->
      fill_op_weak_verdict
        (fill_compile adgm_difc_mutual_recognition_fill) vv).
Proof.
  split.
  - intro observed_verdict.
    apply verdict_preservation_sanctions.
  - split.
    + intro observed_verdict.
      apply verdict_preservation_fill.
    + split.
      * intro observed_verdict.
        apply verdict_preservation_fill.
      * intro observed_verdict.
        apply verdict_preservation_fill.
Qed.
