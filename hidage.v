(******************************************************************************)
(*                                                                            *)
(*          Burghal Hidage: Anglo-Saxon Garrison Arithmetic                   *)
(*                                                                            *)
(*     Formalizes King Alfred's formula for fortress defense: one hide        *)
(*     provides one man, four men garrison one pole of wall. Encodes all      *)
(*     33 burhs; proves Winchester correlation within 1% of archaeology.      *)
(*                                                                            *)
(*     "A king's raw materials and instruments of rule are a well-peopled     *)
(*      land, and he must have men of prayer, men of war, and men of work."   *)
(*     -- Alfred the Great, c. 888                                            *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: December 31, 2025                                                *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.
Require Import Lia.
Import ListNotations.

Open Scope Q_scope.

(* ========================================================================== *)
(*                         ANGLO-SAXON LINEAR MEASURES                        *)
(* ========================================================================== *)

(*
   The Burghal Hidage uses the following units:

   1 pole (perch, rod) = 16½ feet = 5.0292 metres
   1 furlong = 40 poles = 220 yards = 660 feet
   1 chain = 4 poles = 22 yards = 66 feet

   The document states:
   - 4 men garrison 1 pole of wall
   - 1 hide provides 1 man
   - Therefore: 4 hides maintain 1 pole of wall
   - 80 hides maintain 20 poles
   - 160 hides maintain 1 furlong (40 poles)
*)

(* Conversion constants as rationals for precision *)
Definition feet_per_pole : Q := 33 # 2.        (* 16.5 feet *)
Definition metres_per_pole : Q := 50292 # 10000. (* 5.0292 metres *)
Definition poles_per_furlong : Q := 40.
Definition men_per_pole : Q := 4.
Definition hides_per_man : Q := 1.

(* Derived: hides per pole *)
Definition hides_per_pole : Q := men_per_pole * hides_per_man.  (* = 4 *)

(* ========================================================================== *)
(*                           THE GARRISON FORMULA                             *)
(* ========================================================================== *)

(*
   Core formula from the Burghal Hidage:

   "If every hide is represented by one man, then every pole of wall
    can be manned by four men."

   This gives us:
     wall_length_in_poles = hides / 4
     garrison_size = hides
     wall_length_in_feet = hides * (16.5 / 4) = hides * 4.125
     wall_length_in_metres = hides * (5.0292 / 4) = hides * 1.2573
*)

(* Convert hides to garrison size (trivial: 1:1 ratio) *)
Definition hides_to_garrison (hides : Q) : Q := hides.

(* Convert hides to wall length in poles *)
Definition hides_to_poles (hides : Q) : Q := hides / hides_per_pole.

(* Convert poles to hides *)
Definition poles_to_hides (poles : Q) : Q := poles * hides_per_pole.

(* Convert hides to wall length in feet *)
Definition hides_to_feet (hides : Q) : Q :=
  (hides / hides_per_pole) * feet_per_pole.

(* Convert hides to wall length in metres *)
Definition hides_to_metres (hides : Q) : Q :=
  (hides / hides_per_pole) * metres_per_pole.

(* Convert wall length in metres to required hides *)
Definition metres_to_hides (metres : Q) : Q :=
  (metres / metres_per_pole) * hides_per_pole.

(* ========================================================================== *)
(*                              BURH RECORDS                                  *)
(* ========================================================================== *)

(* A burh record contains name, hidage, and optional measured wall length *)
Record Burh := mkBurh {
  burh_name : string;
  burh_hides : nat;
  burh_measured_metres : option Q  (* Archaeological measurement if known *)
}.

(* The 33 burhs of the Burghal Hidage, listed clockwise around Wessex *)
Definition eorpeburnan := mkBurh "Eorpeburnan" 324 None.
Definition hastings := mkBurh "Hastings" 500 None.
Definition lewes := mkBurh "Lewes" 1300 None.
Definition burpham := mkBurh "Burpham" 720 None.
Definition chichester := mkBurh "Chichester" 1500 None.  (* Roman reuse *)
Definition portchester := mkBurh "Portchester" 500 None.
Definition southampton := mkBurh "Southampton" 150 None.
Definition winchester := mkBurh "Winchester" 2400 (Some (3000 # 1)). (* ~3000m measured *)
Definition wilton := mkBurh "Wilton" 1400 None.
Definition chisbury := mkBurh "Chisbury" 700 None.
Definition shaftesbury := mkBurh "Shaftesbury" 700 None.  (* B manuscripts *)
Definition christchurch := mkBurh "Christchurch" 470 None.  (* "500 less 30" *)
Definition wareham := mkBurh "Wareham" 1600 None.
Definition bridport := mkBurh "Bridport" 760 None.  (* "800 less 40" *)
Definition exeter := mkBurh "Exeter" 734 None.  (* Roman reuse, "34 and 700" *)
Definition halwell := mkBurh "Halwell" 300 None.
Definition lydford := mkBurh "Lydford" 140 None.  (* "150 less 10" *)
Definition pilton := mkBurh "Pilton" 360 None.  (* "400 less 40" *)
Definition watchet := mkBurh "Watchet" 513 None.  (* "500 and 13" *)
Definition axbridge := mkBurh "Axbridge" 400 None.
Definition lyng := mkBurh "Lyng" 100 None.  (* Smallest *)
Definition langport := mkBurh "Langport" 600 None.
Definition bath := mkBurh "Bath" 1000 None.
Definition malmesbury := mkBurh "Malmesbury" 1200 None.
Definition cricklade := mkBurh "Cricklade" 1500 None.
Definition oxford := mkBurh "Oxford" 1400 None.  (* 1300-1500 disputed *)
Definition wallingford := mkBurh "Wallingford" 2400 None.  (* Largest with Winchester *)
Definition buckingham := mkBurh "Buckingham" 1600 None.  (* Mercian *)
Definition sashes := mkBurh "Sashes" 1000 None.
Definition eashing := mkBurh "Eashing" 600 None.
Definition southwark := mkBurh "Southwark" 1800 None.
Definition worcester := mkBurh "Worcester" 1200 None.  (* B appendix *)
Definition warwick := mkBurh "Warwick" 2400 None.  (* B appendix *)

(* Complete list of all 33 burhs *)
Definition all_burhs : list Burh := [
  eorpeburnan; hastings; lewes; burpham; chichester;
  portchester; southampton; winchester; wilton; chisbury;
  shaftesbury; christchurch; wareham; bridport; exeter;
  halwell; lydford; pilton; watchet; axbridge;
  lyng; langport; bath; malmesbury; cricklade;
  oxford; wallingford; buckingham; sashes; eashing;
  southwark; worcester; warwick
].

(* ========================================================================== *)
(*                            BASIC COMPUTATIONS                              *)
(* ========================================================================== *)

(* Sum all hides across burhs *)
Definition sum_hides (burhs : list Burh) : nat :=
  fold_left (fun acc b => (acc + burh_hides b)%nat) burhs 0%nat.

(* Total hides in the Burghal Hidage *)
Definition total_hides : nat := sum_hides all_burhs.

(* Predicted wall length for a burh in metres *)
Definition predicted_wall_metres (b : Burh) : Q :=
  hides_to_metres (Z.of_nat (burh_hides b) # 1).

(* ========================================================================== *)
(*                           FORMULA CONSISTENCY                              *)
(* ========================================================================== *)

(* The formula is self-consistent: converting hides to poles and back *)
Lemma hides_poles_roundtrip : forall h : Q,
  ~ h == 0 ->
  poles_to_hides (hides_to_poles h) == h.
Proof.
  intros h Hnonzero.
  unfold poles_to_hides, hides_to_poles, hides_per_pole.
  unfold men_per_pole, hides_per_man.
  field.
Qed.

(* 4 hides per pole is the core ratio *)
Lemma hides_per_pole_value : hides_per_pole == 4.
Proof.
  unfold hides_per_pole, men_per_pole, hides_per_man.
  reflexivity.
Qed.

(* 80 hides for 20 poles (as stated in the document) *)
Lemma twenty_poles_eighty_hides : poles_to_hides 20 == 80.
Proof.
  unfold poles_to_hides, hides_per_pole, men_per_pole, hides_per_man.
  reflexivity.
Qed.

(* 160 hides for 1 furlong (40 poles) *)
Lemma furlong_hides : poles_to_hides poles_per_furlong == 160.
Proof.
  unfold poles_to_hides, poles_per_furlong, hides_per_pole.
  unfold men_per_pole, hides_per_man.
  reflexivity.
Qed.

(* ========================================================================== *)
(*                        WINCHESTER VERIFICATION                             *)
(* ========================================================================== *)

(*
   Winchester: 2400 hides
   Predicted wall: 2400 / 4 * 5.0292 = 3017.52 metres
   Measured wall: ~3000 metres
   Error: < 1%
*)

Definition winchester_predicted : Q := predicted_wall_metres winchester.

(* Compute the predicted value *)
Lemma winchester_predicted_value :
  winchester_predicted == (2400 # 1) * (50292 # 10000) / 4.
Proof.
  unfold winchester_predicted, predicted_wall_metres, hides_to_metres.
  unfold hides_per_pole, men_per_pole, hides_per_man, metres_per_pole.
  simpl. reflexivity.
Qed.

(* The predicted value is approximately 3017.52 metres *)
(* 2400 * 50292 / 40000 = 120700800 / 40000 = 3017.52 *)

Definition winchester_measured : Q := 3000 # 1.

(* Error calculation: |predicted - measured| / measured *)
Definition winchester_error : Q :=
  let pred := (2400 # 1) * (50292 # 10000) / 4 in
  let meas := 3000 # 1 in
  (pred - meas) / meas.

(* The error is less than 1% (0.01) *)
(* Error = (3017.52 - 3000) / 3000 = 17.52 / 3000 ≈ 0.00584 *)
Lemma winchester_error_small : winchester_error < (1 # 100).
Proof.
  unfold winchester_error.
  (* Compute: ((2400 * 50292 / 40000) - 3000) / 3000 *)
  (* = (3017.52 - 3000) / 3000 = 17.52 / 3000 = 0.00584 *)
  (* 0.00584 < 0.01 *)
  reflexivity.
Qed.

(* ========================================================================== *)
(*                           TOTAL ASSESSMENT                                 *)
(* ========================================================================== *)

(*
   The sum of all hidage assessments is approximately 27,000-32,000 depending
   on manuscript tradition. Hill's established text gives ~27,071 hides for
   the 30 core Wessex burhs; including Mercian appendices raises this higher.
*)

(* Garrison size equals hides: one man per hide *)
Lemma garrison_equals_hides : forall h, hides_to_garrison h == h.
Proof.
  intros h. unfold hides_to_garrison. reflexivity.
Qed.

(* ========================================================================== *)
(*                            BURH PROPERTIES                                 *)
(* ========================================================================== *)

(* All burhs have positive hidage *)
Lemma all_burhs_positive_hides :
  Forall (fun b => (burh_hides b > 0)%nat) all_burhs.
Proof.
  unfold all_burhs.
  repeat (constructor; [simpl; lia |]). constructor.
Qed.

(* Lyng is the smallest burh (100 hides) *)
Definition smallest_burh : Burh := lyng.

Lemma lyng_smallest :
  Forall (fun b => (burh_hides smallest_burh <= burh_hides b)%nat) all_burhs.
Proof.
  unfold all_burhs, smallest_burh, lyng.
  repeat (constructor; [simpl; lia |]). constructor.
Qed.

(* Winchester, Wallingford, and Warwick are the largest (2400 hides each) *)
Definition largest_hides : nat := 2400.

Lemma winchester_largest : burh_hides winchester = largest_hides.
Proof. reflexivity. Qed.

Lemma wallingford_largest : burh_hides wallingford = largest_hides.
Proof. reflexivity. Qed.

Lemma warwick_largest : burh_hides warwick = largest_hides.
Proof. reflexivity. Qed.

Lemma no_burh_exceeds_largest :
  Forall (fun b => (burh_hides b <= largest_hides)%nat) all_burhs.
Proof.
  unfold all_burhs, largest_hides.
  repeat (constructor; [simpl; lia |]). constructor.
Qed.

(* ========================================================================== *)
(*                         MANNING DENSITY                                    *)
(* ========================================================================== *)

(*
   Each defender covers 1/4 pole = 4.125 feet ≈ 1.26 metres
*)

Definition feet_per_defender : Q := feet_per_pole / men_per_pole.
Definition metres_per_defender : Q := metres_per_pole / men_per_pole.

Lemma feet_per_defender_value : feet_per_defender == (33 # 8).
Proof.
  unfold feet_per_defender, feet_per_pole, men_per_pole.
  reflexivity.
Qed.

(* 33/8 = 4.125 feet per defender *)

Lemma metres_per_defender_value : metres_per_defender == (50292 # 40000).
Proof.
  unfold metres_per_defender, metres_per_pole, men_per_pole.
  reflexivity.
Qed.

(* 50292/40000 = 1.2573 metres per defender *)

(* ========================================================================== *)
(*                      MINIMUM VIABLE BURH                                   *)
(* ========================================================================== *)

(*
   Lyng at 100 hides is the smallest. Does it provide viable defense?
   Wall length: 100 / 4 * 5.0292 = 125.73 metres
   This is approximately a square fort of 31m per side - viable.
*)

Definition lyng_predicted_wall : Q := predicted_wall_metres lyng.

Lemma lyng_wall_positive : lyng_predicted_wall > 0.
Proof.
  unfold lyng_predicted_wall, predicted_wall_metres.
  unfold hides_to_metres, lyng, hides_per_pole.
  unfold men_per_pole, hides_per_man, metres_per_pole.
  simpl.
  reflexivity.
Qed.

(* Lyng's 100 hides gives 25 poles = ~126 metres of wall *)
Lemma lyng_poles : hides_to_poles (100 # 1) == 25.
Proof.
  unfold hides_to_poles, hides_per_pole, men_per_pole, hides_per_man.
  reflexivity.
Qed.

(* ========================================================================== *)
(*                          LIST PROPERTIES                                   *)
(* ========================================================================== *)

(* Number of burhs in the system *)
Lemma burh_count : List.length all_burhs = 33%nat.
Proof.
  reflexivity.
Qed.

(* The burhs are listed in document order (clockwise around Wessex) *)
(* This is implicit in the definition of all_burhs *)

(* ========================================================================== *)
(*                    EXTRACTION AND COMPUTATION                              *)
(* ========================================================================== *)

(* For computational verification, we can extract to OCaml/Haskell *)

(* Compute predicted wall for any burh *)
Definition compute_wall_metres (b : Burh) : Q :=
  let h := Z.of_nat (burh_hides b) # 1 in
  h * metres_per_pole / hides_per_pole.

(* Verify formula matches for Winchester *)
Lemma winchester_compute_check :
  compute_wall_metres winchester == winchester_predicted.
Proof.
  unfold compute_wall_metres, winchester_predicted, predicted_wall_metres.
  unfold hides_to_metres, winchester.
  simpl.
  reflexivity.
Qed.

(* ========================================================================== *)
(*                              END OF FILE                                   *)
(* ========================================================================== *)
