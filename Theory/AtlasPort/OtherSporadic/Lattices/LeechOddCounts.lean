/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechOddCounts.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Adapted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechOddExhaustion
public import Mathlib.Data.Fintype.Powerset

/-!
Counting odd coordinate profiles with no magnitude-five coordinate or exactly one.
Magnitude supports and Golay residues recover the parameters, giving injective counting formulas.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators

theorem signChange_square (c : BinaryWord) (x : IntegerCoordinates) (i : Omega) :
    signChange c x i * signChange c x i = x i * x i := by
  by_cases h : c i = 0 <;> simp [signChange,h]

theorem signedOddProfile_three_support (T F : Finset Omega) (hTF : Disjoint T F) (c : golay) :
    oddThreeSupport (signedOddProfile T F c) = T := by
  ext i
  simp only [oddThreeSupport,Finset.mem_filter,Finset.mem_univ,true_and,signedOddProfile,signChange_square]
  have h : i ∈ T → i ∈ F → False := fun ht hf => Finset.disjoint_left.mp hTF ht hf
  simp only [oddProfileBase]
  split_ifs <;> norm_num <;> tauto

theorem signedOddProfile_five_support (T F : Finset Omega) (hTF : Disjoint T F) (c : golay) :
    oddFiveSupport (signedOddProfile T F c) = F := by
  ext i
  simp only [oddFiveSupport,Finset.mem_filter,Finset.mem_univ,true_and,signedOddProfile,signChange_square]
  have h : i ∈ T → i ∈ F → False := fun ht hf => Finset.disjoint_left.mp hTF ht hf
  simp only [oddProfileBase]
  split_ifs <;> norm_num <;> tauto

abbrev NoFiveParameters (t : ℕ) := {T : Finset Omega // T.card = t} × golay

def noFiveVector (t : ℕ) (p : NoFiveParameters t) : IntegerCoordinates := signedOddProfile p.1.val ∅ p.2

theorem noFiveVector_injective (t : ℕ) : Function.Injective (noFiveVector t) := by
  intro p q h
  have hT := congrArg oddThreeSupport h
  simp only [noFiveVector,signedOddProfile_three_support _ ∅ (by simp)] at hT
  have hc := congrArg (fun x => halfResidue x 1) h
  simp only [noFiveVector,signedOddProfile_residue] at hc
  exact Prod.ext (Subtype.ext hT) (Subtype.ext hc)

def oddNoFiveVectors (t : ℕ) : Finset IntegerCoordinates := Finset.univ.image (noFiveVector t)

theorem oddNoFiveVectors_card (t : ℕ) : (oddNoFiveVectors t).card = (Nat.choose 24 t) * 4096 := by
  rw [oddNoFiveVectors,Finset.card_image_of_injective _ (noFiveVector_injective t),Finset.card_univ]
  have hc : Fintype.card golay = 4096 := by rw [← Nat.card_eq_fintype_card,golay_card]
  simp [NoFiveParameters,Fintype.card_finset_len,hc,Omega,HexIndex]

abbrev AwayFrom (a : Omega) := {i : Omega // i ≠ a}
abbrev OneFiveParameters (a : Omega) (t : ℕ) := {T : Finset (AwayFrom a) // T.card = t} × golay

def oneFiveSupport (a : Omega) (T : Finset (AwayFrom a)) : Finset Omega :=
  T.map (Function.Embedding.subtype _)

theorem oneFiveSupport_disjoint (a : Omega) (T : Finset (AwayFrom a)) :
    Disjoint (oneFiveSupport a T) {a} := by
  apply Finset.disjoint_singleton_right.mpr
  intro h
  obtain ⟨i,_,hi⟩ := Finset.mem_map.mp h
  exact i.prop hi

def oneFiveVector (a : Omega) (t : ℕ) (p : OneFiveParameters a t) : IntegerCoordinates :=
  signedOddProfile (oneFiveSupport a p.1.val) {a} p.2

theorem oneFiveVector_injective (a : Omega) (t : ℕ) : Function.Injective (oneFiveVector a t) := by
  intro p q h
  have hT := congrArg oddThreeSupport h
  simp only [oneFiveVector,signedOddProfile_three_support _ _ (oneFiveSupport_disjoint _ _)] at hT
  have hc := congrArg (fun x => halfResidue x 1) h
  simp only [oneFiveVector,signedOddProfile_residue] at hc
  exact Prod.ext (Subtype.ext (Finset.map_injective _ hT)) (Subtype.ext hc)

def oddOneFiveVectorsAt (a : Omega) (t : ℕ) : Finset IntegerCoordinates :=
  Finset.univ.image (oneFiveVector a t)

theorem oddOneFiveVectorsAt_card (a : Omega) (t : ℕ) :
    (oddOneFiveVectorsAt a t).card = (Nat.choose 23 t) * 4096 := by
  rw [oddOneFiveVectorsAt,Finset.card_image_of_injective _ (oneFiveVector_injective a t),Finset.card_univ]
  have hc : Fintype.card golay = 4096 := by rw [← Nat.card_eq_fintype_card,golay_card]
  have ha : Fintype.card (AwayFrom a) = 23 := by
    change Fintype.card {i : Omega // i ≠ a} = 23
    simp [Fintype.card_subtype_compl,Omega,HexIndex]
  simp [OneFiveParameters,Fintype.card_finset_len,hc,ha]

def oddOneFiveVectors (t : ℕ) : Finset IntegerCoordinates :=
  Finset.univ.biUnion (fun a : Omega => oddOneFiveVectorsAt a t)

theorem oddOneFiveVectors_disjoint (t : ℕ) (a b : Omega) (hab : a ≠ b) :
    Disjoint (oddOneFiveVectorsAt a t) (oddOneFiveVectorsAt b t) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨q,_,he⟩ := Finset.mem_image.mp hy
  have h := congrArg oddFiveSupport he
  simp only [oneFiveVector,signedOddProfile_five_support _ _ (oneFiveSupport_disjoint _ _)] at h
  exact hab (Finset.singleton_injective h.symm)

theorem oddOneFiveVectors_card (t : ℕ) :
    (oddOneFiveVectors t).card = 24 * (Nat.choose 23 t) * 4096 := by
  rw [oddOneFiveVectors,Finset.card_biUnion]
  · simp [oddOneFiveVectorsAt_card,Omega,HexIndex]
    ring
  · intro a _ b _ hab
    exact oddOneFiveVectors_disjoint t a b hab

theorem odd_minimal_shape_card : (oddNoFiveVectors 1).card = 98304 := by
  rw [oddNoFiveVectors_card]; norm_num [Nat.choose]

theorem odd_six_shape_cards : (oddNoFiveVectors 3).card = 8290304 ∧
    (oddOneFiveVectors 0).card = 98304 := by
  rw [oddNoFiveVectors_card,oddOneFiveVectors_card]; norm_num [Nat.choose]

theorem odd_eight_shape_cards : (oddNoFiveVectors 5).card = 174096384 ∧
    (oddOneFiveVectors 2).card = 24870912 := by
  rw [oddNoFiveVectors_card,oddOneFiveVectors_card]; norm_num [Nat.choose]

end Atlas.Lattices
