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
