module

public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexCenter
public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexBarredQuotient
public import Theory.GroupTheory.PGroup.CyclicInvolution

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem eight_six_central_supplement_eq_bot
    {G : Type u} [Group G] [Finite G]
    (htwo : IsPGroup 2 G) (C A : Subgroup G)
    (hcenter : IsCyclic (Subgroup.center G))
    (hcentral : A ≤ Subgroup.center G) (hcard : Nat.card A = 2)
    (hgen : C ⊔ A = ⊤) (hdisjoint : C ⊓ A = ⊥) : C = ⊥ := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ := hcenter
  by_contra hnontrivial
  let _ : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot C).mpr hnontrivial
  let _ : Nontrivial (Subgroup.center C) := (htwo.to_subgroup C).center_nontrivial
  have hcenterTwo := (htwo.to_subgroup C).to_subgroup (Subgroup.center C)
  obtain ⟨exponent, hpositive, hpower⟩ := hcenterTwo.nontrivial_iff_card.mp inferInstance
  obtain ⟨member, hmember⟩ := exists_prime_orderOf_dvd_card'
    (G := Subgroup.center C) 2 (by rw [hpower]; exact dvd_pow_self 2 (by omega))
  have hambient : ((member : C) : G) ∈ Subgroup.center G := by
    have hC : C ≤ Subgroup.centralizer ({((member : C) : G)} : Set G) := by
      intro other hother
      apply Subgroup.mem_centralizer_iff.mpr
      intro value hvalue
      obtain rfl := Set.mem_singleton_iff.mp hvalue
      exact (congrArg Subtype.val
        (Subgroup.mem_center_iff.mp member.property (⟨other, hother⟩ : C))).symm
    have hA : A ≤ Subgroup.centralizer ({((member : C) : G)} : Set G) :=
      hcentral.trans (Subgroup.center_le_centralizer _)
    have hall := hgen ▸ sup_le hC hA
    apply Subgroup.mem_center_iff.mpr
    intro other
    exact (Subgroup.mem_centralizer_iff.mp (hall (Subgroup.mem_top other))
      ((member : C) : G) (Set.mem_singleton _)).symm
  obtain ⟨actor, hactor⟩ := exists_prime_orderOf_dvd_card'
    (G := A) 2 (by rw [hcard])
  have heq : (⟨((member : C) : G), hambient⟩ : Subgroup.center G) =
      ⟨(actor : G), hcentral actor.property⟩ :=
    IsCyclic.eq_of_orderOf_eq_two (by
      simpa only [Subgroup.orderOf_mk, Subgroup.orderOf_coe] using hmember) (by
      simpa only [Subgroup.orderOf_mk, Subgroup.orderOf_coe] using hactor)
  have hboth : ((member : C) : G) ∈ C ⊓ A :=
    ⟨(member : C).property, (congrArg Subtype.val heq).symm ▸ actor.property⟩
  have hone : member = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact Subgroup.mem_bot.mp (hdisjoint ▸ hboth)
  simp [hone] at hmember

public theorem eight_six_core_eq_of_fixed_core_and_cyclic_center
    {G X : Type u} [Group G] [Finite G] [Group X] [Finite X]
    {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q T : Subgroup G)
    (hprevious : previous ∈ neighborhood ctx.Γ ctx.criticalPath.a)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L) (hT : IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a))
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (hindex : QuotientCardEq (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D) 2)
    (hfixed : Q ⊓ Subgroup.centralizer (T : Set G) ≤ D)
    (projection : S →* X) (hsurjective : Function.Surjective projection)
    (hkernel : projection.ker = (QAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf S)
    (hcyclic : IsCyclic (Subgroup.center X)) : Q = QAt ctx.Γ ctx.criticalPath.a := by
  let graph := ctx.Γ
  let path := ctx.criticalPath
  let C := QAt graph path.a ⊓ Subgroup.centralizer (T : Set G)
  let A := VAt graph previous ⊓ QAt graph path.a
  have hsylow := SevenSix.edge_sylow_data ctx.sectionSeven graph path
  have htwo : IsPGroup 2 S := by
    obtain ⟨_, sylow, heq⟩ := hsylow.1
    rw [← heq]
    exact sylow.isPGroup'.map _
  have hgen : (C.subgroupOf S).map projection ⊔
      (A.subgroupOf S).map projection = ⊤ := by
    rw [← eight_six_initial_core_barred_decomposition ctx.sectionSeven graph path
      hlength previous D L Q T hD hL hQ hT data projection hkernel]
    exact eight_six_initial_core_barred_image_top_local ctx hcard hlength
      projection hsurjective hkernel
  have hzero : (C.subgroupOf S).map projection = ⊥ :=
    eight_six_central_supplement_eq_bot (htwo.of_surjective projection hsurjective)
      _ _ hcyclic
      (eight_six_predecessor_barred_image_central ctx.sectionSeven graph path
        hlength previous D L Q hD hL hQ data hindex projection hsurjective hkernel)
      (eight_six_predecessor_barred_image_card ctx.sectionSeven graph path
        hlength previous D hD hindex projection hkernel)
      hgen
      (eight_six_barred_intersection_of_fixed_core ctx.sectionSeven graph path
        previous D L Q T hprevious hD hL hQ data hfixed projection hkernel)
  have hCS : C ≤ S := inf_le_left.trans
    (SevenSix.local_cores_le_edge_sylow ctx.sectionSeven graph path).1
  have hCfirst : C ≤ QAt graph path.firstStep := by
    have hnative := (Subgroup.map_eq_bot_iff (C.subgroupOf S)).mp hzero
    rw [hkernel] at hnative
    intro member hmember
    exact hnative (show (⟨member, hCS hmember⟩ : S) ∈ C.subgroupOf S from hmember)
  have hCQ : C ≤ Q := (le_inf inf_le_left hCfirst).trans
    (eight_six_first_core_intersection_le_core ctx.sectionSeven graph path
      previous D L Q hprevious hL hQ data)
  have hdecomp := eight_six_initial_core_coprime_decomposition ctx.sectionSeven
    graph path previous D L Q T hL hQ hT data
  exact le_antisymm (le_sup_right.trans hdecomp.ge)
    (hdecomp.le.trans (sup_le hCQ le_rfl))

end Stellmacher.SectionEight
