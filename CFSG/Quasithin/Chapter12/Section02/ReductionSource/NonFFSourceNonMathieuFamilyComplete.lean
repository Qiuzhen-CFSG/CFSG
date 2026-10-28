module
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuFamilyAmbient
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuFamilyRatios
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuFamilyOddSource
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuFamilySporadicSource
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuFamilyExceptionalSourceTriality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuFamilyExceptionalSourceRee
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit

/-!
# The complete non-Mathieu family selection on the chosen orbit

The literal orbit supplies the reduced qrc configuration, its unique maximal
local normalizer and the original Sylow centralizer. Multiple maximal locals
supply an outside parabolic, and the proved TI theorem supplies 3.1.8(2)'s
strict alternative. The symplectic tensor and J₂ numerical equalities are
therefore impossible. Completed cubic source exclusions remove the remaining
odd-linear, exceptional and sporadic cases from the marked A/C catalogue.

The result is SourceFamilies on the unchanged orbit action and component.
Its explicit subgroup-coordinate version retains the central cover, quotient
marking, actual Schur degree and half-field tensor, including degree one.
This discharges the family-selection input of qt-d-1222-nonff-nonmathieu;
the final normalized non-FF argument remains with its existing owner.
The internal Orbit import verifies only the existing covering map's pointwise
conjugation formula, without changing that module's public boundary.
Source: Aschbacher--Smith 3.1.8(2), 3.2.9 and 12.2.2, pp.576,582--583,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuFamily
open NonMathieuAssembly ChapterK.Linear.Recognition ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open scoped MatrixGroups

private theorem families_finrank
    {A E : Type*} [Group A] [Finite A] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] {ρ : Representation (ZMod 2) A E} {Q : Subgroup A}
    (hs : ChapterK.RankOne.SourceHypotheses ρ Q) (d : ℕ)
    (hdim : Module.finrank (ZMod 2) E = d) (hf : SourceFamilies hs) :
    (∃ r : ℕ, 2 ≤ r ∧ ClassicalGroup.IsPSL (Q ⧸ center Q) 2 (2 ^ r)) ∨
    (∃ s : ℕ, 2 ≤ s ∧ ClassicalGroup.IsPSU (Q ⧸ center Q) 3 (2 ^ s)) ∨
    (∃ m : ℕ, 1 ≤ m ∧ Nonempty ((Q ⧸ center Q) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) ∨
    ∃ (B : ChapterB.QuasisimpleSource.BinaryField) (C : LinearCover B 3 Q),
      Nonempty ((Q ⧸ center Q) ≃* PSL(3,B.Carrier)) ∧
        letI := inflated_irreducible ρ C hs.irreducible
        let n := schurDegree (inflated ρ C)
        0 < n ∧ B.degree = 2 * n ∧ d = 9 * n ∧ HasAbsoluteTwistedModel (inflated ρ C) n := by
  rcases hf with h2 | h3 | hsz | ht
  · exact Or.inl h2
  · exact Or.inr (Or.inl h3)
  · exact Or.inr (Or.inr (Or.inl hsz))
  · obtain ⟨B,C,he,hn,hd,hfin,hm⟩ := ht
    exact Or.inr (Or.inr (Or.inr ⟨B,C,he,hn,hd,hdim.symm.trans hfin,hm⟩))

end CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuFamily

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.NonMathieuAssembly

private theorem ratios_le_of_common_cover
    {J A B U W : Type*} [Group J] [Group A] [Group B]
    [AddCommGroup U] [AddCommGroup W] [Module (ZMod 2) U] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A U) (σ : Representation (ZMod 2) B W)
    (hρ : Function.Injective ρ) (hσ : Function.Injective σ)
    (q : J →* A) (hq : Function.Surjective q) (r : J →* B)
    (e : W ≃ₗ[ZMod 2] U)
    (he : ∀ g w, e (σ (r g) w) = ρ (q g) (e w)) :
    (quadraticRatio σ ≤ quadraticRatio ρ) ∧ (cubicRatio σ ≤ cubicRatio ρ) := by
  have hk : q.ker ≤ r.ker := by
    intro g hg
    apply hσ
    ext w
    apply e.injective
    rw [he, MonoidHom.mem_ker.mp hg, map_one, map_one]
    rfl
  let f := q.liftOfSurjective hq ⟨r, hk⟩
  have hf (g : J) : f (q g) = r g := q.liftOfRightInverse_comp_apply _ _ _ g
  have he' (a : A) (v : U) : e.symm (ρ a v) = σ (f a) (e.symm v) := by
    obtain ⟨g, rfl⟩ := hq a
    apply e.injective
    rw [e.apply_symm_apply, hf, he, e.apply_symm_apply]
  have hfi : Function.Injective f := by
    intro a b hab
    apply hρ
    ext v
    apply e.symm.injective
    rw [he', he', hab]
  exact ⟨quadraticRatio_le_of_injective_equivariant ρ σ f hfi e.symm he',
    cubicRatio_le_of_injective_equivariant ρ σ f hfi e.symm he'⟩

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

omit [Finite G] in
private theorem family_orbitHom_conjugation
    (hn : L ⊔ (T : Subgroup G) ≤ normalizer (D.sourceOrbit : Set G))
    (g : (L ⊔ (T : Subgroup G) : Subgroup G)) (w : D.orbitSpace) :
    D.sourceOrbitCoordinates (D.orbitRepresentation (D.orbitHom g) w) =
      ChapterD.UniqueFactor.imageRepresentation (L ⊔ (T : Subgroup G)) D.sourceOrbit hn
        ((ChapterD.UniqueFactor.actionHom (L ⊔ (T : Subgroup G)) D.sourceOrbit hn).rangeRestrict g)
        (D.sourceOrbitCoordinates w) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  exact (D.sourceOrbitCoordinates_apply (D.orbitRepresentation (D.orbitHom g) w)).trans
    (congrArg (fun x : G => (g : G) * x * (g : G)⁻¹)
      (D.sourceOrbitCoordinates_apply w).symm)

/-- Source 3.1.8(2) on the actual TI chosen orbit. -/
theorem sourceOrbit_quadratic_le_two_or_cubic_lt_two_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    quadraticRatio D.orbitRepresentation ≤ 2 ∨ cubicRatio D.orbitRepresentation < 2 := by
  let J := L ⊔ (T : Subgroup G)
  let M := normalizer (L : Set G)
  let Q := ReducedNormal.intrinsicSubspace J D.orbitSpace
  have hW : (⊤ : Subgroup J) ≤ subspaceStabilizer (ReducedNormal.representation J)
      D.orbitSpace := orbitSpan_invariant _ ⊤ D.space
  have hr : IsPReduced 2 Q := by
    change IsPReduced 2 (ReducedNormal.intrinsicSubspace J D.orbitSpace)
    rw [ReducedNormal.intrinsicSubspace_eq]
    exact ReducedNormal.subspaceImage_isPReduced_of_action_core J D.orbitSpace hW
      (D.orbit_twoCore_eq_bot h.toHypothesis1221)
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have hm : IsMaximalTwoLocal M := by
    simpa only [D.localOrbit_eq] using hu.normalizer_maximal
  have hj : J ≤ M := sup_le L.le_normalizer D.sylow_normalizes_component
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N → J ≤ N → N = M := by
    simpa only [D.localOrbit_eq] using hu.normalizer_unique
  have hn : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  obtain ⟨H, hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside
    (Chapter3.hasMaximalOutside_of_many T hmany M hm D.sylow_normalizes_component)
  have hq := Chapter3.qrcHypotheses_of_reduced_join T M L H
    h.maximal_faithful.2.1.2.1 L.le_normalizer hn hj hH Q hr
    (D.orbit_intrinsic_centralizer h.toHypothesis1221)
  change Chapter3.QrcHypotheses T M J H D.sourceOrbit at hq
  have hb := NonMathieuFamily.quadratic_le_two_or_cubic_lt_two hq h.simpleQTKE hm huniq
    D.sourceOrbit_weakClosure_setup.nontrivial (D.sourceOrbit_ti_of_many h hmany hV hnon)
  have ht := ratios_le_of_common_cover
    (ChapterD.UniqueFactor.imageRepresentation J D.sourceOrbit hq.module_normalized)
    D.orbitRepresentation
    (ChapterD.UniqueFactor.imageRepresentation_injective J D.sourceOrbit hq.module_normalized)
    (subspaceImageRepresentation_injective _ _)
    (ChapterD.UniqueFactor.actionHom J D.sourceOrbit hq.module_normalized).rangeRestrict
    (ChapterD.UniqueFactor.actionHom J D.sourceOrbit hq.module_normalized).rangeRestrict_surjective
    D.orbitHom D.sourceOrbitCoordinates (D.family_orbitHom_conjugation hq.module_normalized)
  exact hb.elim (fun hq => Or.inl (ht.1.trans hq)) (fun hc => Or.inr (ht.2.trans_lt hc))

/-- The nonbinary symplectic quotient contradicts the ambient TI bound. -/
theorem sourceOrbit_not_symplectic_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {r : ℕ} (hr : 2 ≤ r)
    (he : ClassicalGroup.IsPSp (D.orbitComponent ⧸ center D.orbitComponent) 2 (2 ^ r)) : False := by
  obtain ⟨hq,hc⟩ := NonMathieuFamily.symplectic_ratios hs hnon hr he
  rcases D.sourceOrbit_quadratic_le_two_or_cubic_lt_two_of_many h hmany hV hnon with hb | hb
  · exact (not_le_of_gt hq) hb
  · exact (ne_of_lt hb) hc

/-- The literal J₂ quotient contradicts the same ambient bound. -/
theorem sourceOrbit_not_janko_two_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (he : Nonempty (D.orbitComponent ⧸ center D.orbitComponent ≃*
      KnownSimple.SporadicName.j2.Carrier)) : False := by
  obtain ⟨hq,hc⟩ := NonMathieuFamily.janko_two_ratios hs he
  rcases D.sourceOrbit_quadratic_le_two_or_cubic_lt_two_of_many h hmany hV hnon with hb | hb
  · exact (not_le_of_gt hq) hb
  · exact (ne_of_lt hb) hc

/-- The marked source families of 3.2.9 on the unchanged chosen orbit.
The tensor alternative retains the positive Schur degree, including one. -/
theorem sourceOrbit_families_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) : SourceFamilies hs := by
  have hm := ChapterB.SourceClassification.quotient_model_of_theoremsAC
    ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremC_knownSimple hs
  cases hm with
  | alternating n hn he =>
    exact NonMathieuFamily.families_of_alternating hs hnon hn (Classical.choice he)
  | odd hm => exact D.sourceOrbit_families_of_odd hs hnon hm
  | bender hm => exact NonMathieuFamily.families_of_bender hs hm
  | linear_binary n hn hm => exact (NonMathieuFamily.binary_linear_excluded hs hnon hn hm).elim
  | sporadic hm =>
    exact (D.sourceOrbit_not_janko_two_of_many h hmany hV hs hnon
      (D.sourceOrbit_sporadic_j2 hs hnm hm)).elim
  | rank_two r hm =>
    cases hm with
    | linear hr he =>
      exact Or.inr (Or.inr (Or.inr (NonMathieuFamily.hermitian_of_linear hs hnon hr he)))
    | symplectic hr he => exact (D.sourceOrbit_not_symplectic_of_many h hmany hV hs hnon hr he).elim
    | g2 hr he => exact (NonMathieuFamily.g2_excluded hs hnon hr he).elim
    | triality hr he => exact (D.sourceOrbit_triality_cubic_false hs hr he).elim
    | ree_f4 m hm _ he => exact (D.sourceOrbit_ree_cubic_false hs hm he).elim
    | symplectic_derived _ he =>
      exact (NonMathieuFamily.alternating_six_seven_excluded hs hnon
        (Or.inl ⟨(Classical.choice he).trans
          Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix⟩)).elim
    | g2_derived _ he => exact (NonMathieuFamily.g2_derived_excluded hs hnon (Classical.choice he)).elim
    | tits _ he => exact (ChapterB.SourceClassification.tits_exclusion hs (Classical.choice he)).elim

open ChapterK.Linear.Recognition ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open scoped MatrixGroups

/-- The source disjunction with its dimension stated on the actual orbit subgroup. -/
theorem sourceOrbit_family_selection_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    (∃ r : ℕ, 2 ≤ r ∧ ClassicalGroup.IsPSL (D.orbitComponent ⧸ center D.orbitComponent) 2 (2 ^ r)) ∨
    (∃ s : ℕ, 2 ≤ s ∧ ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2 ^ s)) ∨
    (∃ m : ℕ, 1 ≤ m ∧ Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) ∨
    ∃ (B : ChapterB.QuasisimpleSource.BinaryField) (C : LinearCover B 3 D.orbitComponent),
      Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier)) ∧
        letI := inflated_irreducible D.orbitRepresentation C hs.irreducible
        let n := schurDegree (inflated D.orbitRepresentation C)
        0 < n ∧ B.degree = 2 * n ∧
          Module.finrank (ZMod 2) (Additive D.sourceOrbit) = 9 * n ∧
          HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n :=
  NonMathieuFamily.families_finrank hs (Module.finrank (ZMod 2) (Additive D.sourceOrbit))
    D.sourceOrbitCoordinates.finrank_eq (D.sourceOrbit_families_of_many h hmany hV hs hnm hnon)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
