module

public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.RecognitionAlternating
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient
public import Theory.Mathieu.M12.TwoCentralInvolutions.CoverResidual
public import Theory.SpecificGroups.Alternating.EightCentralCoverResidual
public import Theory.SpecificGroups.SU3.FourInvolutionCentralizerFive

/-!
# Fixed residuals in the original opposite-centralizer catalogue

The two-residual of the original component action's fixed subgroup embeds
in the literal C_{O²(H)}(w), of order 48. Central-cover descent consequently
excludes M₁₂ (residual order 96) and A₈ (residual two-core order 32), including
central covers. The norm-one quintic torus excludes PSU₃(4), since the full
fixed-subgroup order divides 384. The actual PSL₄(2) equivalence connects
the alternating exclusion to its catalogue row.

Applying these calculations to the checked original-point catalogue leaves
six Lie alternatives, the L₃(4) central-cover row, the odd rows and M₁₁.
Every remaining model is an actual equivalence or central quotient and the
original conjugation by z, fixed Sylow subgroup and numerical marks survive.
The final quotient recognition and core-collapse assembly remain with
qt-e-14322-core-collapse; no quotient equivalence is assumed here.

Source: Aschbacher--Smith 14.3.22, printed p.999, inspecting the two local
centralizers after 1.1.5(3); refs/quasithin.pdf.
-/

public section
open Subgroup
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G]
open Recognition Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.Candidates.ComponentStructure
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hc : CyclicTIInput F (sourceResidual M Mc)) {z d a : G}
    (s : CubicTriple F (sourceResidual M Mc) z d a)

include hG hempty hM hu hmany hcard e hnot hne hgP hgH hs hc s

theorem source_triple_fixedResidual_card_dvd
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))} {α : MulAut D}
    (hα : ∀ x : D, ((α x : ResidualFusion.C (tripleProduct d a)) : G) = z * (x : G) * z⁻¹) :
    Nat.card (pResidual 2 α.fixedSubgroup) ∣ 48 := by
  let C := ResidualFusion.C (tripleProduct d a)
  let K := localResidual F ⊓ C
  have hfH (x : α.fixedSubgroup) : (x : G) ∈ F.H := by
    rw [F.H_eq_centralizer (by decide) z s.point]
    apply mem_centralizer_singleton_iff.mpr
    have hh := hα (x : D)
    rw [(MulAut.mem_fixedSubgroup _ _).mp x.property] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  let k : α.fixedSubgroup →* F.H :=
    { toFun := fun x => ⟨(x : G), hfH x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let j : pResidual 2 α.fixedSubgroup →* K :=
    { toFun := fun x => ⟨(x : G),
        ⟨mem_map_of_mem F.H.subtype
          (map_pResidual_le 2 k (mem_map_of_mem k x.property)),
          (((x : α.fixedSubgroup) : D) : C).property⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext (Subtype.ext (Subtype.ext (congrArg (fun t : K => (t : G)) hxy))))
  have hd := card_dvd_of_injective j hj
  have hK : Nat.card K = 48 := source_triple_residual_centralizer_card
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s
  exact hK ▸ hd

theorem source_triple_not_mathieuTwelve
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D)
    {α : MulAut D}
    (hα : ∀ x : D, ((α x : ResidualFusion.C (tripleProduct d a)) : G) = z * (x : G) * z⁻¹)
    (ha : TwoCentralInner α) :
    ¬ Nonempty ((D ⧸ pCore 2 D) ≃* Sporadic.Mathieu.M12) := by
  rintro ⟨eD⟩
  let := hD.2
  obtain ⟨_,hZ,_⟩ := source_triple_component_center
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD
  let eZ := (QuotientGroup.quotientMulEquivOfEq hZ).trans eD
  let f := PerfectCentralCovering.centralQuotientCover eZ
  have hk : f.toMonoidHom.ker = center D := PerfectCentralCovering.centralQuotientCover_ker eZ
  have hp : IsPGroup 2 f.toMonoidHom.ker := by rw [hk,hZ]; exact pCore_isPGroup
  obtain ⟨P,hfix⟩ := ha.2.2
  obtain ⟨x,hx⟩ := ha.1
  exact Sporadic.Mathieu.no_mathieuTwelve_cover_of_small_fixedResidual f hk hp α ha.2.1
    ⟨x,hx.symm⟩ P hfix (Nat.le_of_dvd (by decide)
      (source_triple_fixedResidual_card_dvd
        hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hα))

theorem source_triple_not_alternatingEight_quotient
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D)
    {α : MulAut D}
    (hα : ∀ x : D, ((α x : ResidualFusion.C (tripleProduct d a)) : G) = z * (x : G) * z⁻¹)
    (ha : TwoCentralInner α) :
    ¬ Nonempty ((D ⧸ pCore 2 D) ≃* alternatingGroup (Fin 8)) := by
  rintro ⟨eD⟩
  let := hD.2
  obtain ⟨_,hZ,_⟩ := source_triple_component_center
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD
  let eZ := (QuotientGroup.quotientMulEquivOfEq hZ).trans eD
  let f := PerfectCentralCovering.centralQuotientCover eZ
  have hk : f.toMonoidHom.ker = center D := PerfectCentralCovering.centralQuotientCover_ker eZ
  have hp : IsPGroup 2 f.toMonoidHom.ker := by rw [hk,hZ]; exact pCore_isPGroup
  obtain ⟨P,hfix⟩ := ha.2.2
  obtain ⟨x,hx⟩ := ha.1
  exact AlternatingEight.no_eight_cover_of_small_fixedResidual f hk hp α ha.2.1
    ⟨x,hx.symm⟩ P hfix (source_triple_fixedResidual_card_dvd
        hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hα)

omit hG hempty hM hu hmany hcard e hnot hne hgP hgH hs hc s [Finite G] in
theorem source_triple_not_unitaryFour
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D)
    (hDs : IsSimpleGroup D) {α : MulAut D}
    (ha : TwoCentralInner α) (hfc : Nat.card α.fixedSubgroup ∣ 384) :
    ¬ ClassicalGroup.IsPSU D 3 4 := by
  let := hD.2
  let := hDs
  rintro ⟨E,hEfield,hEfinite,J,hcard,hfixed,⟨eD⟩⟩
  let := hEfield
  let := hEfinite
  let := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card
    (f := 4) hcard
  obtain ⟨x,hx⟩ := ha.1
  obtain ⟨t,ht,he,hc⟩ := MulAut.inner_involution_representative
    (center_eq_bot_of_simple_perfect (G := D)) α ha.2.1 ⟨x,hx.symm⟩
  rw [hc,Nat.card_congr
    (Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv eD t).toEquiv] at hfc
  exact (by decide : ¬ 5 ∣ 384)
    ((BenderSuzuki.MatrixGroups.HermitianForm.EvenInvolutionTwoGroup.five_dvd_four_involution_centralizer
      J hcard (FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 2 (by decide) hcard hfixed) (eD t) ((eD.orderOf_eq t).trans ht)).trans hfc)

theorem source_triple_not_linearFour
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D)
    (hDs : IsSimpleGroup D) {α : MulAut D}
    (hα : ∀ x : D, ((α x : ResidualFusion.C (tripleProduct d a)) : G) = z * (x : G) * z⁻¹)
    (ha : TwoCentralInner α) : ¬ ClassicalGroup.IsPSL D 4 2 := by
  rintro ⟨E,hEfield,hEfinite,hE,⟨eD⟩⟩
  let := hD.2
  let := hDs
  let := hEfield
  let := hEfinite
  let := Fintype.ofFinite E
  let aE : E ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hE)
  let b := (eD.trans (Atlas.fieldEquivPSL 4 aE)).trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
  have hp : pCore 2 D = ⊥ := bot_unique
    ((IsQuasisimple.pCore_le_center 2).trans (center_eq_bot_of_simple_perfect (G := D)).le)
  let eQ := ((QuotientGroup.quotientMulEquivOfEq hp).trans
    (QuotientGroup.quotientBot (G := D))).trans b
  exact source_triple_not_alternatingEight_quotient
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hα ha ⟨eQ⟩

/-- The six characteristic-two alternatives surviving the original fixed-subgroup marks. -/
@[expose] def ResidualLieModels (X : Type*) [Group X] : Prop :=
  (∃ f : ℕ, 2 ≤ f ∧ f ≤ 6 ∧ ClassicalGroup.IsPSL X 2 (2^f)) ∨
  Nonempty (X ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1) ∨
  ClassicalGroup.IsPSL X 3 2 ∨ ClassicalGroup.IsPSL X 3 4 ∨
  Nonempty (X ≃* alternatingGroup (Fin 6)) ∨
  Nonempty (X ≃* commutator (Atlas.G2.Model (ZMod 2)))

/-- Genuine models remaining after both alternating actions, PSU₃(4), A₈,
and every central M₁₂ cover have been eliminated. -/
inductive ResidualModels (X : Type*) [Group X] : Prop
  | lie (simple : IsSimpleGroup X) (model : ResidualLieModels X)
  | two_cover (nontrivial_center : center X ≠ ⊥) (center_eq : center X = pCore 2 X)
      (model : ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 3 4)
  | odd (model : ClassicalGroup.IsPSL X 3 3 ∨
      ∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL X 2 p)
  | mathieuEleven (model : Nonempty ((X ⧸ pCore 2 X) ≃* Sporadic.Mathieu.M11))

/-- Apply every residual and fixed-subgroup exclusion to the actual marked component.
The remaining models and the original action are retained for quotient recognition. -/
theorem source_triple_residual_marked_component
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    let C := ResidualFusion.C (tripleProduct d a)
    ∃ (D : Subgroup C) (α : MulAut D) (P : Sylow 2 D),
      IsComponent C D ∧
      (∀ x : D, ((α x : C) : G) = z * (x : G) * z⁻¹) ∧
      ResidualModels D ∧ α ∈ (MulAut.conj (G := D)).range ∧ orderOf α = 2 ∧
      Nat.card P ∣ 128 ∧ (∀ x : P, α (x : D) = x) ∧
      Nat.card α.fixedSubgroup ∣ 384 ∧ Nat.card (pResidual 2 α.fixedSubgroup) ∣ 48 ∧
      ¬128 ∣ Nat.card (D ⧸ pCore 2 D) := by
  intro C
  obtain ⟨D,α,P,hD,hα,hm,hi,ho,hP,hfix,hfc,hsmall⟩ := source_triple_inner_marked_component
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have ha : TwoCentralInner α := ⟨hi,ho,P,hfix⟩
  have hmodels : ResidualModels D := by
    cases hm with
    | lie hsimple hm _ =>
      apply ResidualModels.lie hsimple
      rcases hm with hlin | huni | hsuz | hl2 | hl4 | halt | hg2 | hfour
      · exact Or.inl hlin
      · exact (source_triple_not_unitaryFour hD hsimple ha hfc huni).elim
      · exact Or.inr (Or.inl hsuz)
      · exact Or.inr (Or.inr (Or.inl hl2))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hl4)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl halt))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hg2))))
      · exact (source_triple_not_linearFour
          hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hsimple hα ha hfour).elim
    | two_cover hn hz hm _ => exact .two_cover hn hz hm
    | six σ hσ hm => exact (source_triple_not_alternatingSix
        hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hα σ hσ hm).elim
    | seven σ hσ hm => exact (source_triple_not_alternatingSeven
        hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hα σ hσ hm).elim
    | odd hm _ => exact .odd hm
    | sporadic name hn hm _ =>
      rcases hn with rfl | rfl
      · exact .mathieuEleven hm
      · exact (source_triple_not_mathieuTwelve
          hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hα ha hm).elim
  exact ⟨D,α,P,hD,hα,hmodels,hi,ho,hP,hfix,hfc,
    source_triple_fixedResidual_card_dvd
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hα,hsmall⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
