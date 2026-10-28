module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.BinaryCoverAnalysis
public import Theory.Representation.BinaryNaturalDual.FourActors.PermutationCatalogue.Centralizers
public import Theory.SpecificGroups.BinaryLinear.SixSylowActors.Five.FixedGeometry
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# The actual binary fixed groups containing A₆

In a quasisimple group with central quotient PSL₄(2) or PSL₅(2), an embedded
A₆ has centralizer equal to the center. The double-cover exclusion in degree
four and the trivial multiplier in degree five remove the central cover.
An involution fixing that A₆ is consequently outer.

Transport the original automorphism to the genuine binary linear group. In
degree four, the two outer involution classes have fixed groups S₆ and C₂×S₄;
the latter is too small to contain the supplied A₆. In degree five, the
symmetric-form calculation identifies every outer involution fixed group with
S₆. Transport back gives an equivalence of the original fixed subgroup.

Source: Aschbacher–Smith, Lemma 2.5.19(3), printed pp.561–562, used in the
nonabelian-core branch of 2.5.21 on p.566 of the combined 1 March 2004
manuscript. The containing A₆ is the actual fixed component in that application;
its componenthood is unnecessary for this intrinsic model implication.
-/

public section
open Subgroup Theory.GroupTheory Equiv
open BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents.NonfullA6.BinaryFixed
open CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification
variable {E : Type*} [Group E] [Finite E] [IsQuasisimple E]

private noncomputable def binaryLinearEquiv {D : Type*} [Group D] {n : ℕ}
    (hn : 0 < n) (hm : ClassicalGroup.IsPSL D n 2) : D ≃* LinearGroup n := Classical.choice <| by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = Fintype.card (ZMod 2) := by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hcard
  exact ⟨(e.trans (Atlas.fieldEquivPSL n (FiniteField.ringEquivOfCardEq hc))).trans
    (projectiveEquivLinear hn)⟩

private theorem centerless_outer
    (hm : ClassicalGroup.IsPSL (E ⧸ center E) 4 2 ∨
      ClassicalGroup.IsPSL (E ⧸ center E) 5 2)
    (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup E) (hB : B ≤ a.fixedSubgroup)
    (eB : B ≃* alternatingGroup (Fin 6)) :
    center E = ⊥ ∧ a ∉ MulAut.innerSubgroup E := by
  have hz : center E = ⊥ := by
    rcases hm with hm | hm
    · exact center_eq_bot_four_of_no_six_in_double_cover
        GLS3.Chapter5.SchurPresentation.not_injective_six_to_schurAlternatingGroup_three
        hm B ⟨eB⟩
    · exact center_eq_bot_five_of_trivial_multiplier
        Theory.SpecificGroups.PSL5Two.UniversalCover.universalProjection_ker_eq_bot hm
  refine ⟨hz, ?_⟩
  rintro ⟨x, hx⟩
  have hxC : x ∈ centralizer (B : Set E) := by
    intro y hy
    have hxy : MulAut.conj x y = y := hx.symm ▸ (MulAut.mem_fixedSubgroup a y).mp (hB hy)
    exact (mul_inv_eq_iff_eq_mul.mp hxy).symm
  rw [six_centralizer_eq_center_of_binary_quotient hm B ⟨eB⟩, hz, mem_bot] at hxC
  have ha1 : a = 1 := by simpa only [hxC, map_one] using hx.symm
  simp only [ha1, orderOf_one] at ha
  omega

private noncomputable def fixedEquivOfConjugate {D : Type*} [Group D]
    (a b : MulAut D) (h : IsConj a b) : a.fixedSubgroup ≃* b.fixedSubgroup := Classical.choice <| by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have he : MulAut.congr c a = b := by
    have hh : MulAut.congr c a = c * a * c⁻¹ := by ext x; rfl
    exact hh.trans hc
  exact ⟨(MulAut.fixedSubgroupCongr c a).trans
    (MulEquiv.subgroupCongr (congrArg MulAut.fixedSubgroup he))⟩

omit [Finite E] [IsQuasisimple E] in
private theorem outer_congr {D : Type*} [Group D]
    (e : E ≃* D) (a : MulAut E) (ha : a ∉ MulAut.innerSubgroup E) :
    MulAut.congr e a ∉ MulAut.innerSubgroup D := by
  rintro ⟨x, hx⟩
  obtain ⟨y, hy⟩ := (MulAut.congr_inner_iff e a).mp ⟨x, hx.symm⟩
  exact ha ⟨y, hy.symm⟩

/-- Both binary central-quotient rows identify the original fixed subgroup with S₆. -/
theorem binary_quotient_fixed_equiv_symmetric_six
    (hm : ClassicalGroup.IsPSL (E ⧸ center E) 4 2 ∨
      ClassicalGroup.IsPSL (E ⧸ center E) 5 2)
    (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup E) (hB : B ≤ a.fixedSubgroup)
    (eB : B ≃* alternatingGroup (Fin 6)) :
    Nonempty (a.fixedSubgroup ≃* Perm (Fin 6)) := by
  obtain ⟨hz, hout⟩ := centerless_outer hm a ha B hB eB
  let q : E ≃* E ⧸ center E :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm
  rcases hm with hm | hm
  · let e := q.trans (binaryLinearEquiv (by decide : 0 < 4) hm)
    let b := MulAut.congr e a
    let f := MulAut.fixedSubgroupCongr e a
    have hb : orderOf b = 2 := ((MulAut.congr e).orderOf_eq a).trans ha
    have hbo : b ∉ BinaryNaturalDual.FourActors.inner := outer_congr e a hout
    rcases BinaryNaturalDual.FourActors.outer_involution_conjugacy b hb hbo with ht | ht
    · exact ⟨(f.trans (fixedEquivOfConjugate b _ ht)).trans
        BinaryNaturalDual.FourActors.PermutationCatalogue.transpositionFixedEquiv⟩
    · let d := (f.trans (fixedEquivOfConjugate b _ ht)).trans
        BinaryNaturalDual.FourActors.PermutationCatalogue.tripleTranspositionFixedEquiv
      have hc : Nat.card a.fixedSubgroup = 48 := by
        rw [Nat.card_congr d.toEquiv, Nat.card_prod]
        norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
      have hl : Nat.card B ≤ Nat.card a.fixedSubgroup := card_le_of_le hB
      rw [Nat.card_congr eB.toEquiv, nat_card_alternatingGroup, Nat.card_fin, hc] at hl
      norm_num [Nat.factorial] at hl
  · let e := q.trans (binaryLinearEquiv (by decide : 0 < 5) hm)
    let b := MulAut.congr e a
    have hb : b ^ 2 = 1 := by rw [← map_pow, show a ^ 2 = 1 from ha ▸ pow_orderOf_eq_one a, map_one]
    obtain ⟨m⟩ := BinaryLinear.SixSylowActors.Five.exists_fixedModel b hb (outer_congr e a hout)
    exact ⟨(MulAut.fixedSubgroupCongr e a).trans m.equiv⟩

/-- The A₈ central-quotient row, retaining the original fixed A₆ subgroup. -/
theorem alternating_eight_fixed_equiv_symmetric_six
    (e : (E ⧸ center E) ≃* alternatingGroup (Fin 8))
    (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup E) (hB : B ≤ a.fixedSubgroup)
    (eB : B ≃* alternatingGroup (Fin 6)) :
    Nonempty (a.fixedSubgroup ≃* Perm (Fin 6)) := by
  apply binary_quotient_fixed_equiv_symmetric_six (Or.inl ?_) a ha B hB eB
  exact ⟨ZMod 2, inferInstance, inferInstance, by simp,
    ⟨e.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm⟩⟩

end CFSG.Quasithin.Chapter2.Section05.Overcomponents.NonfullA6.BinaryFixed
