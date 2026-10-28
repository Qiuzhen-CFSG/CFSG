module
public import Theory.SpecificGroups.Alternating.SmallSolvableFive
public import Theory.SpecificGroups.AlternatingSevenCentralCoverControl
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Quintic actors above a perfect central cover of A₇

Let K be a normal perfect subgroup with K/Z(K) isomorphic to A₇. An
order-five subgroup acting faithfully on K cannot generate a solvable group
with a full ambient Sylow two-subgroup. The faithful central-quotient action
maps the actor into A₇, while Sylow restriction and surjective transport
retain a full Sylow of A₇ inside the solvable image. This contradicts the
proved prime-to-five order bound for solvable Sylow overgroups of A₇.

The action kernel is the actual centralizer of K; neither ambient
faithfulness nor an identification of K with its central quotient is assumed.
Source application: Aschbacher--Smith 5.1.13 and 5.2.2, pp.636--638,648--649.
-/

public noncomputable section

open Subgroup
namespace Theory.SpecificGroups.Alternating.SevenSolvablePrimeActors
variable {G : Type*} [Group G] [Finite G]

/-- A quintic actor disjoint from the layer centralizer cannot form a solvable Sylow join. -/
theorem no_five_actor (K E : Subgroup G) [K.Normal] [Group.IsPerfect K]
    (e : K ⧸ center K ≃* alternatingGroup (Fin 7)) (S : Sylow 2 G)
    (hE : Nat.card E = 5) (hd : Disjoint E (centralizer (K : Set G)))
    (hs : Group.IsSolvable (E ⊔ (S : Subgroup G) : Subgroup G)) : False := by
  obtain ⟨f,hker,hK⟩ := AlternatingSevenCentralCover.exists_permutation_action K e
  have hfi : Function.Injective (f.comp E.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro x hx
    have hxk : (x : G) ∈ centralizer (K : Set G) := by
      rw [←hker]
      exact hx
    exact Subtype.ext (mem_bot.mp ((disjoint_iff.mp hd) ▸ ⟨x.property,hxk⟩))
  have hEa : E.map f ≤ alternatingGroup (Fin 7) := by
    rintro _ ⟨x,hx,rfl⟩
    have hp : f x ^ 5 = 1 := by
      have hh := congrArg (fun y : E => f y) (pow_card_eq_one' (x := (⟨x,hx⟩ : E)))
      simpa only [hE,Subgroup.coe_pow,Subgroup.coe_one,map_pow,map_one] using hh
    rw [Equiv.Perm.mem_alternatingGroup]
    have hh := congrArg Equiv.Perm.sign hp
    rcases Int.units_eq_one_or (Equiv.Perm.sign (f x)) with hsign | hsign
    · exact hsign
    · norm_num [map_pow,hsign] at hh
  let J := (E ⊔ (S : Subgroup G)).map f
  let J' := J.subgroupOf (alternatingGroup (Fin 7))
  let : Group.IsSolvable (E ⊔ (S : Subgroup G) : Subgroup G) := hs
  let : Group.IsSolvable J := Group.isSolvable_of_surjective (f.subgroupMap_surjective _)
  let : Group.IsSolvable J' := Group.isSolvable_of_isSolvable_injective
    (f := (alternatingGroup (Fin 7)).subtype.subgroupComap J)
    (fun x y he => Subtype.ext (Subtype.ext (congrArg (fun z : J => (z : Equiv.Perm (Fin 7))) he)))
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal K
  let g : K →* alternatingGroup (Fin 7) := (f.comp K.subtype).codRestrict _ (by
    intro k
    rw [←hK]
    exact mem_map_of_mem f k.property)
  have hg : Function.Surjective g := by
    intro x
    have hx : (x : Equiv.Perm (Fin 7)) ∈ K.map f := hK.symm ▸ x.property
    obtain ⟨k,hk,hkx⟩ := hx
    exact ⟨⟨k,hk⟩,Subtype.ext hkx⟩
  have hPJ : ((P.mapSurjective hg : Sylow 2 (alternatingGroup (Fin 7))) : Subgroup _) ≤ J' := by
    rintro x ⟨y,hy,rfl⟩
    change f (y : G) ∈ J
    apply mem_map_of_mem f
    rw [hP] at hy
    exact (show (S : Subgroup G) ≤ E ⊔ (S : Subgroup G) from le_sup_right) hy
  let E' := (E.map f).subgroupOf (alternatingGroup (Fin 7))
  have hc : Nat.card E' = 5 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hEa).toEquiv]
    have hh : Nat.card (E.map f) = Nat.card E := by
      have heq : (f.comp E.subtype).range = E.map f := by rw [MonoidHom.range_comp,range_subtype]
      rw [←heq]
      exact (Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv).symm
    exact hh.trans hE
  have hEJ : E' ≤ J' := comap_mono (map_mono le_sup_left)
  exact SmallSolvableFive.seven_not_five_dvd J' inferInstance (P.mapSurjective hg) hPJ
    (hc ▸ card_dvd_of_le hEJ)
end Theory.SpecificGroups.Alternating.SevenSolvablePrimeActors
