module
public import CFSG.Quasithin.Chapter3.Section02.LinearThreeFourRecognition
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.FixedSpace
public import CFSG.Quasithin.Chapter3.Section02.ModuleConsequences
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.PSL3FourFaithfulExclusion

/-!
# Fixed-space exclusion for the original PSL₃(4) FSU module

The literal join image has normal component PSL₃(4), two-group quotient
and trivial two-core. The faithful quadratic-ratio exclusion therefore
makes the original orbit module non-FF, without requiring irreducibility.
The source Thompson argument would make that same action FF if the seed
had a nonzero component-fixed vector. Thus the seed, local orbit and full
normalizer orbit all have zero component centralizer.

If the seed equals its local orbit, its Irr⁺ property now gives irreducibility
of the actual component action, with the original conjugation projection.
The moved-seed exclusion and residual application are in Chapter12's
`RankOneModuleGenericExceptionalLinearResidualFSUComplete`.
Source: Aschbacher–Smith 3.2.2(4,6), 3.2.5 and3.2.9, printed pp.579–583,
used in5.1.14, p.638 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
namespace CFSG.Quasithin.Chapter3.Section02.FundamentalSetup
open ChapterD.UniqueFactor ChapterK.Linear.Recognition
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {K : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T K)

include D in
private theorem uniqueness : Chapter1.Section02.NonsolvableUniquenessConclusion T K :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal

omit [Finite G] in
private theorem orbit_eq (hn : (T : Subgroup G) ≤ normalizer (K : Set G)) :
    localOrbit T K = K :=
  le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hn)
    (le_componentOrbit _ _)

omit [Finite G] in
private theorem exists_four_equiv
    (hlinear : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) :
    Nonempty ((K ⧸ pCore 2 K) ≃* PSL(3,E 1)) := by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hlinear
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (E 1) := Fintype.ofFinite _
  let a : F ≃+* E 1 := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,hcard,card_E]
    norm_num)
  exact ⟨e.trans (Atlas.fieldEquivPSL 3 a)⟩

/-- The original orbit action has quadratic ratio greater than two, without irreducibility. -/
theorem linearThreeFour_joinRepresentation_quadraticRatio_gt_two
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hlinear : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) :
    letI := D.module_elementary
    2 < quadraticRatio D.joinRepresentation := by
  let := D.module_elementary
  obtain ⟨e⟩ := exists_four_equiv hlinear
  let := D.componentActionImage_normal hn
  have hm : ClassicalGroup.IsPSL D.componentActionImage 3 4 :=
    ⟨E 1,inferInstance,inferInstance,by simpa using card_E 1,
      ⟨(D.componentQuotientEquiv hn e).symm.trans e⟩⟩
  exact PSL3FourExclusion.quadraticRatio_gt_two_of_faithful
    (D.joinImage_sqtk D.uniqueness hn e
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X)))
    hm (D.joinImage_quotient_isTwoGroup hn)
    (internalActionImage_core_of_reduced _ _
      (D.module_le_core.trans (pCoreIn_le 2 _)) D.join_normalizes_module
      (D.module_reduced D.uniqueness))
    (imageRepresentation_injective _ _ _)

/-- The literal join action on the FSU module is not FF. -/
theorem linearThreeFour_joinRepresentation_notFF
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hlinear : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) :
    letI := D.module_elementary
    ¬ IsFFModule D.joinRepresentation := by
  let := D.module_elementary
  intro hff
  exact not_le_of_gt (D.linearThreeFour_joinRepresentation_quadraticRatio_gt_two hn hlinear)
    (((isFFModule_iff_quadraticRatio_le_one D.joinRepresentation).mp hff).trans (by norm_num))

/-- The multiple-overgroup guard excludes nonzero fixed vectors in the seed. -/
theorem linearThreeFour_seed_centralizer_eq_bot
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hlinear : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) :
    D.seed ⊓ centralizer (K : Set G) = ⊥ := by
  by_contra hc
  exact D.linearThreeFour_joinRepresentation_notFF hn hlinear
    (D.fixedSpace_consequences_of_many hmany (by rwa [orbit_eq hn])).2

/-- The full normalizer orbit retains the same zero component centralizer. -/
theorem linearThreeFour_fullModule_centralizer_eq_bot
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hlinear : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) :
    D.fullModule ⊓ centralizer (K : Set G) = ⊥ := by
  have he := D.fullModule_centralizer_eq_seed_orbit D.uniqueness
  rw [orbit_eq hn, D.linearThreeFour_seed_centralizer_eq_bot hmany hn hlinear] at he
  simpa [componentOrbit] using he

/-- The local Sylow orbit also has zero component centralizer. -/
theorem linearThreeFour_module_centralizer_eq_bot
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hlinear : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) :
    D.moduleSubgroup ⊓ centralizer (K : Set G) = ⊥ := by
  exact bot_unique ((inf_le_inf_right _ (le_componentOrbit D.moduleSubgroup D.maximalLocal)).trans
    (D.linearThreeFour_fullModule_centralizer_eq_bot hmany hn hlinear).le)

/-- The fixed-seed case is irreducible on the original component action. -/
theorem linearThreeFour_irreducible_of_seed_eq_module
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hlinear : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (he : D.seed = D.moduleSubgroup) :
    letI := D.module_elementary
    Representation.IsIrreducible (D.joinRepresentation.comp D.componentActionImage.subtype) := by
  let := D.module_elementary
  let := D.seed_elementary
  let H := localJoin T K
  let X := (localOrbit T K).subgroupOf H
  let ρ := ReducedNormal.representation H
  let I := D.seedSpace
  let τ := (invariantSubspace ρ X I D.homogeneous.invariant).toRepresentation
  have hzero : I ⊓ fixedSpace ρ X = ⊥ := by
    apply bot_unique
    intro v hv
    have hvI : v.toMul.val.val ∈ D.seed :=
      mem_map_of_mem _ (mem_map_of_mem _ hv.1)
    have hvC : v.toMul.val.val ∈ centralizer (K : Set G) := by
      intro k hk
      have hkO : k ∈ localOrbit T K := (orbit_eq hn).symm ▸ hk
      have hh := congrArg (fun w : Additive (ReducedNormal.ModuleGroup H) =>
        w.toMul.val.val) (hv.2 ⟨⟨k,(le_sup_left : localOrbit T K ≤ H) hkO⟩,hkO⟩)
      change k * v.toMul.val.val * k⁻¹ = v.toMul.val.val at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    have h1 := (D.linearThreeFour_seed_centralizer_eq_bot hmany hn hlinear).le ⟨hvI,hvC⟩
    exact Additive.toMul.injective (Subtype.ext (Subtype.ext h1))
  have hi : IsIrreducible τ := by
    apply (Subrepresentation.irreducible_iff_isAtom _).mpr
    refine ⟨?_,?_⟩
    · intro h
      exact D.homogeneous.isIrrPlus.ne_bot ρ (congrArg Subrepresentation.toSubmodule h)
    · intro J hJ
      have hs : X ≤ subspaceStabilizer ρ J.toSubmodule :=
        le_subspaceStabilizer ρ _ (fun x hx v hv => J.apply_mem_toSubmodule ⟨x,hx⟩ hv)
      rcases D.homogeneous.isIrrPlus.eq_or_le_fixedSpace ρ hs hJ.le with hj | hf
      · exact (hJ.ne (Subrepresentation.toSubmodule_injective hj)).elim
      · exact Subrepresentation.toSubmodule_injective
          (bot_unique ((le_inf (show J.toSubmodule ≤ I from hJ.le) hf).trans hzero.le))
  let a : Additive D.seed ≃ₗ[ZMod 2] Additive D.moduleSubgroup :=
    { (MulEquiv.subgroupCongr he).toAdditive with
      map_smul' := ZMod.map_smul (MulEquiv.subgroupCongr he).toAdditive }
  let e : I ≃ₗ[ZMod 2] Additive D.moduleSubgroup :=
    (ReducedNormal.subspaceEquiv H I).trans a
  let b : X ≃* K := (subgroupOfEquivOfLe (show localOrbit T K ≤ H from le_sup_left)).trans
    (MulEquiv.subgroupCongr (orbit_eq hn))
  let q : X →* D.componentActionImage := D.componentProjection.comp b.toMonoidHom
  let σ := D.joinRepresentation.comp D.componentActionImage.subtype
  let f : Representation.RepEquiv τ (σ.comp q) :=
    ⟨e, by intro x; apply LinearMap.ext; intro v; rfl⟩
  exact (irreducible_comp_surjective_iff q
    (D.componentAction.rangeRestrict_surjective.comp b.surjective) σ).mp
      (f.irreducible_euqiv.mp hi)

end CFSG.Quasithin.Chapter3.Section02.FundamentalSetup
