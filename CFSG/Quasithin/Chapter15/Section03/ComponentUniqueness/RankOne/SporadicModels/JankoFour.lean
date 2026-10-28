module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.SporadicModels.LocalConfiguration
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.Reduction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.NormalFour
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.CharacteristicTwo
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Reduction of the J₄ rank-one obstruction to concrete local calculations

Full automorphism innerness makes the faithful normal component the whole
ambient group. Choose a maximal proper overgroup of the specified local M,
retaining its Sylow two-subgroup. The concrete max1/max2/max4 cover and their
self-centralizing two-cores make this overgroup characteristic two, so the
source maximality of M identifies the two groups. The normal elementary
four-group then transports through the actual local-group equivalence.

The max1 case is discharged by the checked kernel-orbit calculation. Full
innerness, exhaustive maximal-Sylow coverage, characteristic two for max4,
and the normal-four obstructions for max2 and max4 remain explicit inputs.
Thus this is conditional assembly, not the unconditional J₄ exclusion.
No outer-two-group statement or universal max4 pair placement is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the sporadic
paragraph of 15.3.43, printed p.1140, and 1.1.5(3)(f), printed p.502.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.SporadicModels
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem component_eq_top_of_inner {K S M Y V : Subgroup G}
    (c : LocalConfiguration K S M Y V) (e : K ≃* Janko4.Model)
    (hi : Function.Surjective (MulAut.conj : Janko4.Model →* MulAut Janko4.Model)) :
    K = ⊤ := by
  let : K.Normal := c.normal
  apply top_unique
  intro x _
  obtain ⟨k, hk⟩ := hi (MulAut.congr e (MulAut.conjNormal x))
  obtain ⟨k, hk⟩ := (MulAut.congr_inner_iff e (MulAut.conjNormal x)).mp ⟨k, hk.symm⟩
  have hx : x = (k : G) :=
    MulAut.conjNormal_injective_of_centralizer_eq_bot K c.faithful
      (hk.trans MulAut.conjNormal_val.symm)
  exact hx ▸ k.property

omit [Finite G] in
private theorem four_contradiction {K S M Y V : Subgroup G}
    (c : LocalConfiguration K S M Y V) {H : Type*} [Group H]
    (e : M ≃* H)
    (hf : ∀ W : Subgroup H, W.Normal → IsElementaryAbelian 2 W → Nat.card W ≠ 4) :
    False := by
  let : IsElementaryAbelian 2 V := c.plane_elementary
  let : IsElementaryAbelian 2 (V.subgroupOf M) :=
    IsElementaryAbelian.subgroupOf c.plane_le_local
  have hn : ((V.subgroupOf M).map e.toMonoidHom).Normal :=
    c.plane_normal.map e.toMonoidHom e.surjective
  apply hf _ hn (IsElementaryAbelian.map e.toMonoidHom)
  rw [Subgroup.card_map_of_injective e.injective]
  exact (Nat.card_congr (subgroupOfEquivOfLe c.plane_le_local).toEquiv).trans c.plane_card

private theorem local_equiv_of_cover {K S M Y V : Subgroup G}
    (c : LocalConfiguration K S M Y V) (e : G ≃* Janko4.Model)
    {H : Type*} [Group H] {Q : Subgroup Janko4.Model}
    (hMQ : M.map e.toMonoidHom ≤ Q) (f : Q ≃* H)
    (hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H) :
    Nonempty (M ≃* H) := by
  let R := Q.map e.symm.toMonoidHom
  have hR : R.map e.toMonoidHom = Q := by
    simp [R, map_map]
  let eR : R ≃* H := (e.subgroupMap R).trans ((MulEquiv.subgroupCongr hR).trans f)
  have hMR : M ≤ R := by
    simpa [R, map_map] using map_mono (f := e.symm.toMonoidHom) hMQ
  have hchar : Theory.GroupTheory.generalizedFitting R = pCore 2 R :=
    Theory.GroupTheory.generalizedFitting_eq_pCore_of_selfCentralizing 2
      ((Theory.Quasithin.centralizer_pCore_le_iff 2 eR).mpr hc)
  have he : M = R := le_antisymm hMR (c.maximal.2 hchar hMR)
  exact ⟨(MulEquiv.subgroupCongr he).trans eR⟩

open Janko4.LocalStructure.SymmetricLinear
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement

attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
  Janko4.Cardinality.max1Subgroup sourceSubgroup max4Subgroup

/-- Conditional J₄ exclusion with the literal max1 obstruction discharged.
The five remaining model inputs must be proved before the source case is complete. -/
theorem LocalConfiguration.not_janko_four_of_local_structure {K S M Y V : Subgroup G}
    (c : LocalConfiguration K S M Y V) (e : K ≃* Janko4.Model)
    (hi : Function.Surjective (MulAut.conj : Janko4.Model →* MulAut Janko4.Model))
    (hcover : MaximalSylowCover)
    (hc4 : centralizer (pCore 2 max4Subgroup : Set max4Subgroup) ≤ pCore 2 max4Subgroup)
    (hf2 : ∀ W : Subgroup sourceSubgroup,
      W.Normal → IsElementaryAbelian 2 W → Nat.card W ≠ 4)
    (hf4 : ∀ W : Subgroup max4Subgroup,
      W.Normal → IsElementaryAbelian 2 W → Nat.card W ≠ 4) : False := by
  have hK := component_eq_top_of_inner c e hi
  let eG : G ≃* Janko4.Model :=
    Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr hK.symm).trans e)
  obtain ⟨P, hP⟩ := c.sylow
  have hM : M.map eG.toMonoidHom ≠ ⊤ := by
    intro ht
    have he := congrArg (map eG.symm.toMonoidHom) ht
    have : M = ⊤ := by
      simpa [map_map, map_top_of_surjective eG.symm.toMonoidHom eG.symm.surjective] using he
    exact c.proper.ne this
  obtain ⟨Q, hQ, hMQ⟩ := (eq_top_or_exists_le_coatom (M.map eG.toMonoidHom)).resolve_left hM
  have hSQ : ((P.mapSurjective (f := eG.toMonoidHom) eG.surjective) :
      Subgroup Janko4.Model) ≤ Q := by
    change (P : Subgroup G).map eG.toMonoidHom ≤ Q
    rw [hP]
    exact (map_mono c.sylow_le_local).trans hMQ
  rcases hcover (P.mapSurjective eG.surjective) Q hQ hSQ with hf | hf | hf
  · obtain ⟨f⟩ := hf
    obtain ⟨eM⟩ := local_equiv_of_cover (H := Janko4.Cardinality.max1Subgroup
      Janko4.matrixA_mul_self Janko4.matrixB_pow_four) c eG hMQ f
      Janko4.LocalStructure.max1_twoCore_centralizer_le
    apply four_contradiction c eM
    intro W hn _
    let : W.Normal := hn
    exact Janko4.LocalStructure.max1_normal_card_ne_four W
  · obtain ⟨f⟩ := hf
    obtain ⟨eM⟩ := local_equiv_of_cover (H := sourceSubgroup) c eG hMQ f
      Janko4.LocalStructure.max2_twoCore_centralizer_le
    exact four_contradiction c eM hf2
  · obtain ⟨f⟩ := hf
    obtain ⟨eM⟩ := local_equiv_of_cover (H := max4Subgroup) c eG hMQ f hc4
    exact four_contradiction c eM hf4

end CFSG.Quasithin.Chapter15.Section03.RankOne.SporadicModels
