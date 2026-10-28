module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianConstituentModels
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedNondegenerateExclusion

/-!
# Closing the original exchanged constituent

The original actor dimension identity completes the selected exchanged pair
and excludes the full-linear alternative, including the exceptional four-space.
The isotropic branch has its literal A₇ action and gives the already excluded
whole S₇ group. For a nondegenerate constituent, the original square form and
point-centralizer bound exclude both constituent-kernel cases.

This applies the general constituent results from the Chapter 14 development
to the unchanged degree-four or degree-five flag. No rank-three ambient input
or constituent recognition premise is imported into the source statement.
Source: Aschbacher--Smith G.11.6 and 12.9.4, printed pp.365--366,859--860.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Chapter14.Section04.CaseOneLarge
namespace OriginalExchanged
open ExchangedGeometry ExchangedIsotropic
variable {D U : Type*} [Group D] [Finite D] [AddCommGroup U]
  [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  {ρ : Representation (ZMod 2) D U} {B : LinearMap.BilinForm (ZMod 2) U}
  {v : U} {W : Submodule (ZMod 2) U} {X : Subgroup D}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : ChapterG.Section10.Hypothesis ρ B v W X X₀)
  (hn : ¬ Group.IsSolvable D) {C : Subgroup D} (hC : IsComponent D C)
  (hm : ⁅C,X⁆ ≠ ⊥) (S : Sylow 2 D)
  (hXS : X ≤ (S : Subgroup D)) (hSX : (S : Subgroup D) ≤ normalizer (X : Set D))
  (hind : (normalizer (C : Set D)).index ≤ 2)
  {I : Submodule (ZMod 2) U}
  (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit C ⊤) X I) (hv : v ∉ I)
include h hn hC hm S hXS hSX hind hI hv in
private theorem complete_data
    (hbalance : 2 * (Group.rank X + 1) = finrank (ZMod 2) U) :
    CompletedData ρ B C X I hI := by
  obtain ⟨hp,hgen,hpair,hfaith⟩ := completion h hn hC hm S hXS hSX hind hI hv hbalance
  refine ⟨hp,hgen,hpair,stabilizer_degree h hn hC hm S hXS hSX hind hI hv hbalance,
    hfaith.1,hfaith.2,?_⟩
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let : Group.IsPerfect H := hC.orbit_isPerfect ⊤
  rcases hI.isIrrPlus.isotropic_or_nondegenerate_of_normal_restriction ρ
    (h.irreducible_of_not_solvable hn) H B h.alternating h.preserves with hiso | hnd
  · exact Or.inr ⟨hiso,faithful_dual_of_isotropic h hn hC hm S hXS hSX
      hind hI hv hbalance hiso⟩
  · exact Or.inl hnd


variable (hc : ExchangedGeometry.CompletedData ρ B C X I hI)
  (hiso : ∀ u ∈ I, ∀ w ∈ I, B u w = 0)
  (hf : Function.Injective
    (invariantSubspace ρ (componentOrbit C ⊤) I hI.invariant).toRepresentation)
open Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
include h hn hC hind hI hc hiso hf in
private theorem isotropic_data
    (cover : Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple D))
    (hns : ¬ Nonempty (Representation.Equiv
      (invariantSubspace ρ (componentOrbit C ⊤) I hI.invariant).toRepresentation
      (invariantSubspace ρ (componentOrbit C ⊤) I hI.invariant).toRepresentation.dual)) :
    IsotropicData ρ C X I hI := by
  let H := componentOrbit C ⊤
  let A := ExchangedAction.actor ρ X I
  let σ := ExchangedAction.imageAction ρ H X I hI.invariant
  let image := ExchangedAction.image ρ H X I hI.invariant
  have he := orbit_eq_component h hn hC hind hI hc hiso hf cover
  have hi := image_single_component_hypothesis h hn hC hind hI hc hiso hf cover
  have hnorm : C.Normal := he ▸ componentOrbit_top_normal C
  refine ⟨he,hnorm,hi,
    ExchangedAction.image_not_selfDual ρ H X I hI.invariant hns,
    ExchangedAction.image_not_surjective ρ H X I hI.invariant hc.1,?_,
    image_carrier_models h hn hC hind hI hc hiso hf cover⟩
  let : (image H).Normal := hi.normal_H
  let : IsIrreducible (σ.comp (image H).subtype) := hi.irreducible
  have hr := hi.toSetup.rank_le_automorphisms (L := image H) (by
    rw [normalizer_eq_top]
    exact le_top)
  let : Group.IsPerfect H := hC.orbit_isPerfect ⊤
  have hd := hI.isIrrPlus.finrank_gt_two ρ H
  change finrank (ZMod 2) I ≤ primeRank 2 (MulAut (image H)) + 2
  omega

end OriginalExchanged
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
open ChapterG.Section11
open Chapter14.Section03.NonabelianSource.Recognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

private theorem original_closure_geometry
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 V] : ClosureGeometry F := by
  let := F.localKernel_tilde_seed_elementary
  have hn : 2 ≤ n := by have := h.rank; omega
  have hJ := h.point_mem_Hz F earlier.alternatives
  exact {
    two := F.localKernel_UH_isPGroup h.source.simpleQTKE L _ F.H hn
      h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
      h.residual (fun _ => ⟨h.naturalMarking⟩) hJ
    frattini_point := F.localKernel_frattini_eq_point h.source.simpleQTKE L _ hn
      h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
      h.residual (fun _ => ⟨h.naturalMarking⟩) (h.flag_escape F earlier.alternatives) hne
    seed_center := F.seed_inf_center_eq_point_of_ambient_natural h.naturalMarking h.rank.1 hne
    tilde_kernel := F.localKernel_eq_pCore h.source.simpleQTKE L _ F.H hn
      h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
      h.residual (fun _ => ⟨h.naturalMarking⟩) rfl
      (h.maximal_unique earlier.structural earlier.uniqueness).2
      (h.seed_centralizer_le earlier.structural earlier.uniqueness) h.centralizer_L hJ }

/-- Both exchanged alternatives are excluded on the original flag, with the
actual square form and point-centralizer bound constructed from the source. -/
theorem nonabelian_exchanged_constituent_impossible
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (preferred : PreferredDimension KnownSimple.IsKnownSimple T n)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (four : NaturalReduction KnownSimple.IsKnownSimple.{u} 4)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hg10 : ChapterG.Section10.Hypothesis F.terminalRepresentation B v (hatSpace F (F.E g))
      (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v})
    (hS : NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)))
    {J : Subgroup F.TerminalHdot} (hJ : IsComponent F.TerminalHdot J)
    (hm : ⁅J,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit J ⊤)
      (F.terminalDot (F.X g)) I)
    (hv : v ∉ I) : False := by
  let := h.chosen.elementary
  obtain ⟨S,hfix,hXS,hnS⟩ := hS
  have hSX := (normal_subgroupOf_iff_le_normalizer hXS).mp hnS
  have hns := nonabelian_hat_not_solvable h hn F hne
  have cover := nonabelian_sqtkCover h F
  have hind := cover.component_normalizer_index_le_two hJ
  obtain ⟨_,_,_,_,_,_,_,_,hd,_,_⟩ :=
    nonabelian_fixed_line_lagrangian modules h hn preferred earlier four F hne g hgP hgH
  have hb : 2 * (Group.rank (F.terminalDot (F.X g)) + 1) =
      finrank (ZMod 2) (Additive F.Uhat) := by
    have ha := IsElementaryAbelian.rank_le_finrank (p := 2) (F.terminalDot (F.X g))
    have hq := Group.rank_le_of_surjective (QuotientGroup.mk'
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
      (QuotientGroup.mk'_surjective _)
    have hb := hg10.dimension_bound.1
    omega
  have hc := OriginalExchanged.complete_data hg10 hns hJ hm S hXS hSX hind hI hv hb
  rcases hc.2.2.2.2.2.2 with hnd | ⟨hiso,hfaith,hdual,_⟩
  · have hgeo := hg10.exchanged_constituent_geometry hns hJ hm S hSX hind hI hv
    have haxis := hg10.exchanged_constituent_not_le_axis hns hJ hm S hSX hind hI hv hc.1
    have models := ExchangedNondegenerate.recognized_data hg10 hns hJ hI hgeo haxis hnd
    have hZ := nonabelian_center_eq_point modules h hn preferred earlier four F hne g hgP hgH
    have hker := nonabelian_hat_kernel_eq_core_of_center_eq h earlier F hZ
    have htwo : IsPGroup 2 F.terminalHatAction.ker := hker ▸ pCore_isPGroup
    have hrank : primeRank 3 F.TerminalHdot ≤ 2 :=
      (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ htwo).trans
        ((h.source.simpleQTKE.twoLocal_sqtk (Gi_twoLocal h F 1 le_rfl)).stronglyQuasithin
          3 Nat.prime_three (by decide))
    have hpoint : primeRank 3 (ChapterG.Section10.pointCentralizer F.terminalRepresentation v) ≤ 1 :=
      nonabelian_point_three_rank_of_center_eq h earlier F hne g hgP hgH v hline hZ
    let c := original_closure_geometry h earlier F hne
    have hn1 : 1 ≤ n := by rcases hn with rfl | rfl <;> decide
    have hn2 : 2 ≤ n := by omega
    let q := centerPointQuadraticForm F c hn1 hZ
    have hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU := disjoint_iff.mpr
      (F.parabolic_displaced_centers hn2 L h.chosen.normalizes c.seed_center g hgP hgH).1
    obtain ⟨hs,hi,hqn⟩ := quadratic_intersection_of_center_point F c hn1 hZ g hdis
    have hqpres : ∀ a u, q (F.terminalRepresentation a u) = q u := by
      intro a u
      obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker a
      exact hi a u.toMul
    obtain ⟨x,_,_,_,_,i,hi0,_,hiW,_⟩ := hgeo
    have hqi : q (⟨i,i.property.1⟩ : I) = 0 := by
      apply hs
      have hh : (i : Additive F.Uhat) ∈ I ⊓ hatSpace F (F.E g) := by
        rw [hiW]
        exact Submodule.subset_span (Set.mem_singleton _)
      exact hh.2
    exact ExchangedKernel.nondegenerate_impossible hg10 hns hJ hm S hSX hind hI hv hc hnd
      ⟨cover⟩ models hrank hpoint hfix q hqn hqpres
      ⟨i,i.property.1⟩ (fun hz => hi0 (congrArg Subtype.val hz)) hqi
  · have hf : Function.Injective (invariantSubspace F.terminalRepresentation
        (componentOrbit J ⊤) I hI.invariant).toRepresentation := fun a b hab => hfaith (Units.ext hab)
    have hi := OriginalExchanged.isotropic_data hg10 hns hJ hind hI hc hiso hf ⟨cover⟩ hdual
    obtain ⟨e⟩ := ExchangedIsotropicModels.component_alternating_seven hg10 hns hJ hI hc hiso hi S hXS hSX
    let eH := (MulEquiv.subgroupCongr hi.1).trans e
    have hdI := ExchangedIsotropicModels.alternating_seven_degree hg10 hns hJ hI hc hf hb eH
    obtain ⟨f,_⟩ := ExchangedIsotropicModels.whole_symmetric_seven hg10 hns hJ hI hc hf hdI.1 eH
    exact point_hat_not_symmetric_seven h hn earlier F hne ⟨f⟩


/-- The original point span is abelian in both source degrees. The selected
constituent is constructed from the same flag and escaping conjugator, and
both its marked and exchanged branches have been discharged. -/
theorem point_span_abelian_of_original
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (preferred : PreferredDimension KnownSimple.IsKnownSimple T n)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (four : NaturalReduction KnownSimple.IsKnownSimple.{u} 4)
    (F : InvariantFlag T V n)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) : IsMulCommutative F.U := by
  by_contra hne
  let := nonabelian_hat_elementary h earlier F hne
  obtain ⟨hX,B,v,hg10,hline,hS,J,hJ,hm,_,I,hI,hmarked | hex⟩ :=
    nonabelian_fixed_line_constituents modules h hn preferred earlier four F hne g hgP hgH
  · let := hX
    exact nonabelian_marked_constituent_impossible modules h hn preferred earlier four
      F hne g hgP hgH hg10 hS hJ hm hI hmarked.1
  · let := hX
    exact nonabelian_exchanged_constituent_impossible modules h hn preferred earlier four
      F hne g hgP hgH hg10 hline hS hJ hm hI hex.1

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
