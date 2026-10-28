module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.UnitaryGeometry.TwoPointRoots.ProjectiveTori
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
public import Theory.GroupTheory.Involution.Counting

/-!
# The literal SU₃ commutator torus

The scalar projection maps every Sylow normalizer onto the corresponding
projective normalizer, and its central kernel lies in that normalizer.
Consequently the upstairs normalizer is the full preimage of the downstairs
normalizer (the Sylow subgroup itself is not its full preimage).
Lifting the projective inverted torus through this odd central kernel gives
a cyclic group of order q-1. It is exactly [B ∩ Bᵗ,⟨t⟩] in SU₃ itself.

Source: GLS4, Chapter 4, Lemma 3.2(d), as used for SU₃ in Chapter 2,
Section 16. The special carrier and projection are J.specialSubgroup and
J.specialToProjective throughout.
-/

open Subgroup BenderSuzuki BenderSuzuki.PFAppendixIII BenderSuzuki.PFchapter1section1
open scoped commutatorElement
namespace BenderSuzuki.ZD.RankOneModelGeometry
open _root_.BenderSuzuki.MatrixGroups HermitianForm External
open HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage
open scoped LinearAlgebra.Projectivization
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
  {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2 ^ n) ^ 2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
private instance : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

include hn hcard hfixed hJ in
public theorem unitary_special_inverted_torus (P : Sylow 2 J.specialSubgroup)
    (t : J.specialSubgroup) (ht : IsInvolution t)
    (htB : t ∉ normalizer (P : Set J.specialSubgroup)) :
    ∃ T : Subgroup J.specialSubgroup,
      (T : Set J.specialSubgroup) = {x | x ∈ normalizer (P : Set J.specialSubgroup) ∧
        x ∈ rightConjugate (normalizer (P : Set J.specialSubgroup)) t ∧
        rightConjugateElem x t = x⁻¹} ∧
      IsCyclic T ∧ Nat.card T = 2 ^ n - 1 := by
  let f := J.specialToProjective
  let B := normalizer (P : Set J.specialSubgroup)
  let Q := P.mapSurjective J.specialToProjective_surjective
  have hm : B.map f = normalizer (Q : Set (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    P.normalizer_map_surjective f J.specialToProjective_surjective
  have hkB : f.ker ≤ B := J.specialToProjective_ker_le_center.trans (center_le_normalizer _)
  have hpre : (B.map f).comap f = B := by
    rw [comap_map_eq, sup_eq_left.mpr hkB]
  have htq : IsInvolution (f t) := Theory.GroupTheory.involution_map_of_odd_kernel
    f J.odd_card_specialToProjective_ker ht
  have htout : f t ∉ normalizer (Q : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    intro hh
    apply htB
    rw [← hm] at hh
    change t ∈ B
    rw [← hpre]
    exact hh
  obtain ⟨T, hT, hcT, hTc⟩ := psu_invertedTorus_of_borel J n hn hcard hfixed hJ
    (unitary_projective_borel J hn hcard hfixed hJ Q) (f t) htq htout
  have hiT : ∀ y ∈ T, rightConjugateElem y (f t) = y⁻¹ :=
    fun y hy => ((Set.ext_iff.mp hT y).mp hy).2.2
  obtain ⟨L, hL, hcL, hLc⟩ := invertedTorus_lift_surjective f J.specialToProjective_surjective
    J.specialToProjective_ker_le_center J.odd_card_specialToProjective_ker t T hcT hiT
  have hLset : (L : Set J.specialSubgroup) =
      {x | x ∈ B ∧ x ∈ rightConjugate B t ∧ rightConjugateElem x t = x⁻¹} := by
    ext x
    change x ∈ L ↔ x ∈ B ∧ x ∈ rightConjugate B t ∧ rightConjugateElem x t = x⁻¹
    rw [hL]
    constructor
    · rintro ⟨hx, hi⟩
      have hxB : x ∈ B := by
        have hy := ((Set.ext_iff.mp hT (f x)).mp hx).1
        rw [← hm] at hy
        rw [← hpre]
        exact hy
      refine ⟨hxB, ?_, hi⟩
      refine ⟨x⁻¹, B.inv_mem hxB, ?_⟩
      change t⁻¹ * x⁻¹ * (t⁻¹)⁻¹ = x
      calc
        _ = (rightConjugateElem x t)⁻¹ := by simp [rightConjugateElem, mul_assoc]
        _ = x := by rw [hi, inv_inv]
    · rintro ⟨hxB, hxBt, hi⟩
      refine ⟨(Set.ext_iff.mp hT (f x)).mpr ⟨?_, ?_, ?_⟩, hi⟩
      · rw [← hm]
        exact mem_map_of_mem f hxB
      · rw [← hm]
        obtain ⟨y, hy, he⟩ := hxBt
        refine ⟨f y, mem_map_of_mem f hy, ?_⟩
        change t⁻¹ * y * (t⁻¹)⁻¹ = x at he
        change (f t)⁻¹ * f y * ((f t)⁻¹)⁻¹ = f x
        simpa only [map_mul, map_inv] using congrArg f he
      · simpa [rightConjugateElem] using congrArg f hi
  have hLc' : Nat.card L = 2 ^ n - 1 := hLc.trans hTc
  exact ⟨L, hLset, hcL, hLc'⟩

include hn hcard hfixed hJ in
public theorem unitary_special_commutator_torus (P : Sylow 2 J.specialSubgroup)
    (t : J.specialSubgroup) (ht : IsInvolution t)
    (htB : t ∉ normalizer (P : Set J.specialSubgroup)) :
    IsCyclic (⁅twoPoint (normalizer (P : Set J.specialSubgroup)) t, zpowers t⁆ : Subgroup _) ∧
      Nat.card (⁅twoPoint (normalizer (P : Set J.specialSubgroup)) t, zpowers t⁆ : Subgroup _) = 2 ^ n - 1 ∧
      ∀ x ∈ ⁅twoPoint (normalizer (P : Set J.specialSubgroup)) t, zpowers t⁆,
        rightConjugateElem x t = x⁻¹ := by
  obtain ⟨L, hLset, hcL, hLc⟩ := unitary_special_inverted_torus J hn hcard hfixed hJ P t ht htB
  have hLo : Odd (Nat.card L) := by
    rw [hLc]
    exact Nat.Even.sub_odd (Nat.one_le_pow n 2 (by decide))
      (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  rw [twoPoint_commutator_of_inverted _ L t ht hLset hLo]
  exact ⟨hcL, hLc, fun x hx => ((Set.ext_iff.mp hLset x).mp hx).2.2⟩

end BenderSuzuki.ZD.RankOneModelGeometry
