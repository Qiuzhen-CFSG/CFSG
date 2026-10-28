module

public import Stellmacher.Recognition.GTwoSixtyFourModel
public import Theory.SpecificGroups.C4SquareSignSwapInitialEight

/-!
# Initial elementary-eight geometry in the order-64 branch

An elementary eight in the initial core which the supplied Sylow normalizes
lies in the second core and is self-centralizing in the Sylow. Transport to
the marked sign-and-swap model proves both assertions simultaneously.
The actual neighboring-core intersection is elementary of order eight.
Initial-vertex normality and its plane action are separate steps.

Source: Stellmacher (8.6)(a), `refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven SevenSix

/-- The elementary neighboring-core intersection supplied by the actual
case-(a) data already has order eight. -/
public theorem gTwo_card64_elementary_intersection_card
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64) : Nat.card data.D = 8 := by
  let := data.groupK
  let := data.finiteK
  let : IsElementaryAbelian 2 data.D := data.caseA.base.2.2
  let D := data.D.map data.embedding
  let S := (data.sylowIntersection : Subgroup G)
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.map data.embedding
  have hDcore : D ≤ (QAt data.Γ data.criticalPath.a).map data.embedding :=
    Subgroup.map_mono (gTwo_card64_elementary_intersection_le_core data hcard)
  have hDS : D ≤ S := hDcore.trans (gTwo_card64_cores_le_sylow data).1
  let Dn := D.subgroupOf S
  let : IsElementaryAbelian 2 Dn := IsElementaryAbelian.subgroupOf hDS
  obtain ⟨e, _, heQa, _⟩ := gTwo_card64_marked_equiv data hcard
  let Dm := Dn.map e.toMonoidHom
  let : IsElementaryAbelian 2 Dm := IsElementaryAbelian.map e.toMonoidHom
  have hDmcard : Nat.card Dm = Nat.card data.D := by
    rw [Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDS).toEquiv,
      Subgroup.card_map_of_injective data.embedding_injective]
  have hDmcore : Dm ≤ C4SquareSignSwap.inverterCore := by
    rw [← heQa]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono S hDcore)
  rw [← hDmcard]
  exact C4SquareSignSwap.elementary_inverterCore_card_eight_of_gt_four Dm
    (by rw [hDmcard]; exact gTwo_card64_elementary_intersection_card_gt_four data hcard) hDmcore

/-- The marked Sylow puts every normal initial-core eight in the second core
and determines its Sylow centralizer. -/
public theorem gTwo_card64_initial_eight_geometry
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64)
    (U : Subgroup G) [IsElementaryAbelian 2 U] (hU : Nat.card U = 8)
    (hnorm : (data.sylowIntersection : Subgroup G) ≤ Subgroup.normalizer (U : Set G)) :
    letI := data.groupK
    letI := data.finiteK
    U ≤ (QAt data.Γ data.criticalPath.a).map data.embedding →
    U ≤ (QAt data.Γ data.criticalPath.firstStep).map data.embedding ∧
      (data.sylowIntersection : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) = U := by
  let := data.groupK
  let := data.finiteK
  intro hUQa
  let S := (data.sylowIntersection : Subgroup G)
  let Qa := (QAt data.Γ data.criticalPath.a).map data.embedding
  let Qb := (QAt data.Γ data.criticalPath.firstStep).map data.embedding
  obtain ⟨hQaS, _⟩ := gTwo_card64_cores_le_sylow data
  have hUS : U ≤ S := hUQa.trans hQaS
  let Un := U.subgroupOf S
  let : IsElementaryAbelian 2 Un := IsElementaryAbelian.subgroupOf hUS
  let : Un.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUS).mpr hnorm
  obtain ⟨e, _, heQa, heQb⟩ := gTwo_card64_marked_equiv data hcard
  let Um := Un.map e.toMonoidHom
  let : IsElementaryAbelian 2 Um := IsElementaryAbelian.map e.toMonoidHom
  let : Um.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  have hUmcard : Nat.card Um = 8 := by
    rw [Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUS).toEquiv, hU]
  have hUmQa : Um ≤ C4SquareSignSwap.inverterCore := by
    rw [← heQa]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono S hUQa)
  obtain ⟨hUmQb, hUmC⟩ := C4SquareSignSwap.normal_elementary_eight_geometry Um hUmcard hUmQa
  have hUQb : U ≤ Qb := by
    intro u hu
    have heU : e (⟨u, hUS hu⟩ : S) ∈ Um :=
      Subgroup.mem_map_of_mem e.toMonoidHom hu
    have heQ := hUmQb heU
    rw [← heQb] at heQ
    obtain ⟨v, hv, heq⟩ := heQ
    have hvu : v = (⟨u, hUS hu⟩ : S) := e.injective heq
    have hval : (v : G) = u := congrArg Subtype.val hvu
    exact hval ▸ hv
  refine ⟨hUQb, le_antisymm ?_ ?_⟩
  · intro c hc
    let cS : S := ⟨c, hc.1⟩
    have heC : e cS ∈ Subgroup.centralizer (Um : Set C4SquareSignSwap.Model) := by
      apply Subgroup.mem_centralizer_iff.mpr
      rintro _ ⟨u, hu, rfl⟩
      change e u * e cS = e cS * e u
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hc.2 u hu
    rw [hUmC] at heC
    obtain ⟨u, hu, heq⟩ := heC
    have hueq : u = cS := e.injective heq
    have hval : (u : G) = c := congrArg Subtype.val hueq
    exact hval ▸ hu
  · exact le_inf hUS (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance)

end Stellmacher.Recognition
