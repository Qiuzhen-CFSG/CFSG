module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.AlternatingPlacement
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree.Descent
public import Theory.SpecificGroups.G2Even.BinaryOuter
public import Theory.SpecificGroups.G2Even.MarkedCover
public import Theory.SpecificGroups.Classical.BinaryDerivedCubicRank
public import Theory.SpecificGroups.FFG2DerivedCenter
public import Theory.AtlasPort.LinearGroups.G2.BinaryProperSylowCore.ThreeRank

/-!
# Excluding the original binary G₂ component

The literal core-to-star covering has a two-group kernel. Since the full
core quotient has trivial two-core, this identifies it with G₂(2)′. Its
outer two-group and three-rank two identify the original component with
O^{3′}(I). In particular the original K lies in C_X(ZS), hence in Mc.
The preceding intrinsic-movement argument excludes X ≤ Mc.

The proper intersection Mc intersect X contains a full Sylow two-subgroup
of X and has three-rank at least two because it contains K. The actual
binary G₂ proper-Sylow-overgroup bound gives three-rank at most one.
This contradiction excludes the binary row while preserving the original
X, R and NI. No full KS placement or new MS classification is assumed.

Source: Aschbacher--Smith original 15.2.23, pp.1116--1117, A.3.18,
pp.51--52, and C.2.7, pp.145--147; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Section01 PlaneUniquenessPreceding PlaneUniquenessPreceding.LinearThree TerminalLinear
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G] {I X R N : Subgroup G}

private noncomputable def binaryG2Cover
    (h : Input KnownSimple.IsKnownSimple I R N X)
    (e : starImage X R X ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    Cover (X ⧸ pCore 2 X) (commutator (Atlas.G2.Model (ZMod 2))) where
  toMonoidHom := e.toMonoidHom.comp (coreToStar h.normalizes)
  surjective := e.surjective.comp (coreToStar_surjective h.normalizes)
  isPerfect := h.quasisimple.toIsPerfect
  ker_le_center := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact coreToStar_ker_central_from_source h

/-- The full core quotient is the actual binary derived G₂ group through
the original star projection; its possible central kernel is discharged. -/
noncomputable def binaryG2CoreEquiv
    (h : Input KnownSimple.IsKnownSimple I R N X)
    (e : starImage X R X ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    (X ⧸ pCore 2 X) ≃* commutator (Atlas.G2.Model (ZMod 2)) := by
  let f := binaryG2Cover h e
  have hk := BenderSuzuki.MatrixGroups.HermitianForm.TernaryPerfectCover.binaryDerived_kernel_isTwoGroup f
  have hi : Function.Injective f.toMonoidHom := by
    apply f.toMonoidHom.ker_eq_bot_iff.mp
    apply bot_unique
    exact (show f.toMonoidHom.ker ≤ pCore 2 (X ⧸ pCore 2 X) from
      le_sSup ⟨inferInstance,hk⟩).trans_eq (pCore_quotient_pCore_eq_bot 2)
  exact MulEquiv.ofBijective f.toMonoidHom ⟨hi,f.surjective⟩

/-- Compatibility with the original map from the selected component. -/
theorem binaryG2CoreEquiv_mk
    (h : Input KnownSimple.IsKnownSimple I R N X)
    (e : starImage X R X ≃* commutator (Atlas.G2.Model (ZMod 2))) (x : X) :
    binaryG2CoreEquiv h e (QuotientGroup.mk' (pCore 2 X) x) =
      e (toStarImage X R x) := by
  change e (coreToStar h.normalizes (QuotientGroup.mk' (pCore 2 X) x)) = _
  rw [coreToStar_mk]

variable {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

include hsource in
/-- The selected binary G₂ component is the original cubic residual of I. -/
theorem binaryG2_eq_threeResidual
    (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    X = (primeToResidual 3 I).map I.subtype := by
  let h := normalized_component_input (hsource := hsource) hI hcore s
  let Y := X.subgroupOf I
  let eY : Y ≃* X := subgroupOfEquivOfLe s.component.1
  let eQ : (Y ⧸ pCore 2 Y) ≃* (X ⧸ pCore 2 X) :=
    QuotientGroup.congr _ _ eY (pCore_map_iso 2 eY)
  let a := eQ.trans (binaryG2CoreEquiv h e)
  let : IsQuasisimple (X ⧸ pCore 2 X) := s.quasisimple
  let : IsQuasisimple (Y ⧸ pCore 2 Y) := IsQuasisimple.of_mulEquiv eQ.symm
  have hz : center (Y ⧸ pCore 2 Y) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have he := ((centerCongr a) ⟨x,hx⟩).property
    change a x ∈ center (commutator (Atlas.G2.Model (ZMod 2))) at he
    rw [Theory.SpecificGroups.g2_derived_two_center_eq_bot,mem_bot] at he
    exact a.map_eq_one_iff.mp he
  have hr : 2 ≤ primeRank 3 (Y ⧸ pCore 2 Y) := by
    rw [primeRank_congr 3 a]
    exact Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2
  have ho : IsPGroup 2 (MulAut.Outer (Y ⧸ pCore 2 Y)) :=
    Atlas.G2.binaryDerived_outer_isTwoGroup.of_equiv (MulAut.outerCongr a).symm
  have hY := s.component.2.eq_primeToResidual_three_of_rank_outer_two hz hr
    ((Chapter1.RadicalExclusions.sqtk_of_mem_H hsource.ambient hI.1).stronglyQuasithin
      3 Nat.prime_three (by decide)) ho
  have hh := congrArg (Subgroup.map I.subtype) hY
  rwa [map_subgroupOf_eq_of_le s.component.1] at hh

include hsource in
/-- Relative normality in the original escaping I follows from the residual identity. -/
theorem binaryG2_normalized
    (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    I ≤ normalizer (X : Set G) := by
  rw [binaryG2_eq_threeResidual (hsource := hsource) hI hcore s e]
  exact I.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image I (primeToResidual 3 I))

include d in
/-- The original K lies in the literal component centralizer of ZS. -/
theorem binaryG2_residual_le_M1
    (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    (pResidual 2 H).map H.subtype ≤ M1 X ZS := by
  refine le_inf ?_ d.residual_centralizes
  rw [binaryG2_eq_threeResidual (hsource := hsource) hI hcore s e]
  exact residual_le_threeResidual d hI

include hsource in
/-- The component itself is generated by its cubic elements. -/
theorem binaryG2_threeResidual_eq_top
    (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    primeToResidual 3 X = ⊤ := by
  let h := normalized_component_input (hsource := hsource) hI hcore s
  let a := binaryG2CoreEquiv h e
  let : IsQuasisimple (X ⧸ pCore 2 X) := s.quasisimple
  let : Group.IsPerfect (X.subgroupOf I) := s.component.2.perfect
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe s.component.1).toMonoidHom)
    (subgroupOfEquivOfLe s.component.1).surjective
  have hr : 2 ≤ primeRank 3 X := by
    have hh : 2 ≤ primeRank 3 (X ⧸ pCore 2 X) := by
      rw [primeRank_congr 3 a]
      exact Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2
    exact hh.trans (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup)
  have hz : primeRank 3 (center (X ⧸ pCore 2 X)) ≤ 1 := by
    let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    apply primeRank_le_of_card_le_prime_pow (n := 1)
    rw [Nat.card_congr (centerCongr a).toEquiv,
      Theory.SpecificGroups.g2_derived_two_center_eq_bot,card_bot]
    norm_num
  have hg := cubic_closure_eq_top_of_twoCore_quasisimple hr hz
  apply top_unique
  rw [←hg]
  apply (closure_le _).mpr
  intro x hx
  change orderOf x = 3 at hx
  apply mem_primeToResidual_of_pow (n := 1)
  simpa only [pow_one,hx] using pow_orderOf_eq_one x

include d in
/-- Intrinsic movement and the original Kc premise exclude containment in Mc. -/
theorem binaryG2_not_le_partner
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    ¬ X ≤ Mc := by
  let h := normalized_component_input (hsource := hsource) hI hcore s
  let : Group.IsPerfect (X.subgroupOf I) := s.component.2.perfect
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe s.component.1).toMonoidHom)
    (subgroupOfEquivOfLe s.component.1).surjective
  intro hx
  exact d.no_normal_perfect_threeResidual horbit hI s.component.1
    (binaryG2_normalized (hsource := hsource) hI hcore s e) hx
    (binaryG2_threeResidual_eq_top (hsource := hsource) hI hcore s e)
    (input_intrinsic_movement h)

include d in
/-- The partner intersection contains a full Sylow subgroup and the original
rank-two K, contradicting the binary G₂ proper-overgroup bound. -/
theorem normalized_binaryG2_false
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  let K := (pResidual 2 H).map H.subtype
  have hK : K ≤ M1 X ZS := binaryG2_residual_le_M1 d hI hcore s e
  have hKX : K ≤ X := hK.trans inf_le_left
  have hKM : K ≤ Mc := hK.trans ((M1_le_partner_intersection d hI s.component.1).trans inf_le_left)
  have hproper : Mc.subgroupOf X ≠ ⊤ := by
    intro he
    exact binaryG2_not_le_partner d horbit hI hcore s e (subgroupOf_eq_top.mp he)
  have hP : ∃ P : Sylow 2 X, (P : Subgroup X) ≤ Mc.subgroupOf X := by
    obtain ⟨R,hR⟩ := d.sylow_in_escape hI
    obtain ⟨Q,hQ⟩ := R.exists_subgroupOf_eq_of_subnormal (X.subgroupOf I) s.component.2.subnormal
    let a := subgroupOfEquivOfLe s.component.1
    refine ⟨Q.mapSurjective (f := a.toMonoidHom) a.surjective,?_⟩
    rintro x ⟨y,hy,rfl⟩
    have hyR : (y : I) ∈ R := by
      change y ∈ (R : Subgroup I).subgroupOf (X.subgroupOf I)
      rwa [← hQ]
    have hyS : ((y : I) : G) ∈ planeSylow T ZS := hR ▸ mem_map_of_mem I.subtype hyR
    exact ((le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_left) hyS
  obtain ⟨P,hP⟩ := hP
  let h := normalized_component_input (hsource := hsource) hI hcore s
  have hu := Atlas.G2.BinaryProperSylowCore.twoCoreQuotient_sylow_overgroup_three_rank_le_one
    (binaryG2CoreEquiv h e) P (Mc.subgroupOf X) hP hproper
  have hl : 2 ≤ primeRank 3 (Mc.subgroupOf X) := by
    have hh := primeRank_mono 3 (show K.subgroupOf X ≤ Mc.subgroupOf X from fun _ hx => hKM hx)
    rw [primeRank_congr 3 (subgroupOfEquivOfLe hKX), residual_rank_two d] at hh
    exact hh
  omega

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
