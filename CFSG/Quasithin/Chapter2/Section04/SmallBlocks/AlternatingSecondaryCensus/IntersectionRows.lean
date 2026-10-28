module
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.NativeSourceAssembly
public import Theory.SpecificGroups.PSL3Three.InvolutionResidual
public import Theory.Mathieu.M11.Properties.InvolutionResidual
public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore

/-!
# Intersection screens in the secondary alternating-five centralizer

The actual intersection with M is a two-group. The PSL3(3) and M11
involution centralizers and the alternating-seven partition stabilizer
contain elements of order three, so their marked intersections are excluded.
The odd-core-free ambient group also excludes the triple alternating-six cover.

Source: Aschbacher--Smith, inspection in 2.4.29, printed pp.545--546.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.SmallBlocks.AlternatingSecondaryCensus
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem involution_centralizer_isTwoGroup
    (H K M : Subgroup G) (hKH : K ≤ H) (hM : IsPGroup 2 (H ⊓ M : Subgroup G))
    (t : K) (hi : K ⊓ M = K ⊓ centralizer ({(t : G)} : Set G)) :
    IsPGroup 2 (centralizer ({t} : Set K)) := by
  let j : centralizer ({t} : Set K) →* (H ⊓ M : Subgroup G) := {
    toFun := fun x => ⟨x,hKH (x : K).property,
      (show (x : G) ∈ K ⊓ M from hi.symm ▸
        ⟨(x : K).property,mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩).2⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  apply hM.of_injective j
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun q : (H ⊓ M : Subgroup G) => (q : G)) h

private theorem gl_two_three_not_twoGroup (h : IsPGroup 2 (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))) : False := by
  have hc : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) = 48 := by
    rw [Matrix.card_GL_field]
    decide
  obtain ⟨n,hn⟩ := h.exists_card_eq
  have hd : 3 ∣ 2 ^ n := by rw [←hn,hc]; decide
  have hh : 3 ∣ 2 := (by decide : Nat.Prime 3).dvd_of_dvd_pow hd
  norm_num at hh

omit [Finite G] in
theorem odd_linear_three_intersection_false
    (H K M : Subgroup G) (hKH : K ≤ H) (hM : IsPGroup 2 (H ⊓ M : Subgroup G))
    (e : K ≃* Matrix.PSL3Three.PSL) (t : K) (ht : orderOf t = 2)
    (hi : K ⊓ M = K ⊓ centralizer ({(t : G)} : Set G)) : False := by
  let eC := (CentralizerSmallKernelTransport.centralizerEquiv e t).trans
    (Matrix.PSL3Three.involutionCentralizerEquivGL (e t) ((e.orderOf_eq t).trans ht))
  exact gl_two_three_not_twoGroup
    ((involution_centralizer_isTwoGroup H K M hKH hM t hi).of_surjective
      eC.toMonoidHom eC.surjective)

omit [Finite G] in
theorem mathieu_eleven_intersection_false
    (H K M : Subgroup G) (hKH : K ≤ H) (hM : IsPGroup 2 (H ⊓ M : Subgroup G))
    (e : K ≃* Sporadic.Mathieu.M11) (t : K) (ht : orderOf t = 2)
    (hi : K ⊓ M = K ⊓ centralizer ({(t : G)} : Set G)) : False := by
  let eC := (CentralizerSmallKernelTransport.centralizerEquiv e t).trans
    (Sporadic.Mathieu.m11InvolutionCentralizerEquivGL (e t) ((e.orderOf_eq t).trans ht))
  exact gl_two_three_not_twoGroup
    ((involution_centralizer_isTwoGroup H K M hKH hM t hi).of_surjective
      eC.toMonoidHom eC.surjective)

theorem triple_alternating_six_row_false (H K : Subgroup G)
    (hK : IsComponent H (K.subgroupOf H)) (hKH : K ≤ H)
    (ho : pPrimeCore 2 H = ⊥)
    (hm : ComponentRefinement.LieType.IsTripleAlternatingSixCover K) : False := by
  let : IsQuasisimple (K.subgroupOf H) := hK.2
  have hb := hK.1.pPrimeCore_eq_bot ho
  have hz := IsQuasisimple.center_eq_pCore hb
  have hp : IsPGroup 2 (center (K.subgroupOf H)) := hz.symm ▸ pCore_isPGroup
  let e := subgroupOfEquivOfLe hKH
  have hc : Nat.card (center (K.subgroupOf H)) = 3 :=
    (Nat.card_congr (centerCongr e).toEquiv).trans hm.2.1
  rcases hp.card_eq_or_dvd with h | h <;> norm_num [hc] at h

private theorem alternating_stabilizer_not_twoGroup
    (h : IsPGroup 2 ComponentRefinement.AlternatingSeven.alternatingStabilizer) : False := by
  let k : ComponentRefinement.AlternatingSeven.A7 :=
    ⟨(Equiv.swap 0 2 * Equiv.swap 2 4) * (Equiv.swap 1 3 * Equiv.swap 3 5),
      by change Equiv.Perm.sign _ = 1; decide⟩
  have hk : k ∈ ComponentRefinement.AlternatingSeven.alternatingStabilizer := by
    rw [ComponentRefinement.AlternatingSeven.mem_alternatingStabilizer]
    decide
  let a : ComponentRefinement.AlternatingSeven.alternatingStabilizer := ⟨k,hk⟩
  have ha : a ^ 3 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change (((Equiv.swap 0 2 * Equiv.swap 2 4) * (Equiv.swap 1 3 * Equiv.swap 3 5)) : Equiv.Perm (Fin 7)) ^ 3 = 1
    decide
  have han : a ≠ 1 := by
    intro he
    have hh := congrArg (fun x : ComponentRefinement.AlternatingSeven.alternatingStabilizer =>
      ((x : ComponentRefinement.AlternatingSeven.A7) : Equiv.Perm (Fin 7)) 0) he
    exact (by decide : ((k : Equiv.Perm (Fin 7)) 0) ≠ 0) hh
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have ho : orderOf a = 3 := orderOf_eq_prime ha han
  obtain ⟨n,hn⟩ := h.exists_orderOf_dvd_pow a
  rw [ho] at hn
  have hd : 3 ∣ 2 := (by decide : Nat.Prime 3).dvd_of_dvd_pow hn
  norm_num at hd

omit [Finite G] in
theorem alternating_seven_intersection_false
    (H K M : Subgroup G) (hKH : K ≤ H) (hM : IsPGroup 2 (H ⊓ M : Subgroup G))
    (e : M.subgroupOf K ≃* ComponentRefinement.AlternatingSeven.alternatingStabilizer) : False := by
  let j : M.subgroupOf K →* (H ⊓ M : Subgroup G) := {
    toFun := fun x => ⟨x,hKH (x : K).property,x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hi : Function.Injective j := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun q : (H ⊓ M : Subgroup G) => (q : G)) he
  exact alternating_stabilizer_not_twoGroup
    ((hM.of_injective j hi).of_surjective e.toMonoidHom e.surjective)

end CFSG.Quasithin.Chapter2.SmallBlocks.AlternatingSecondaryCensus
