module
public import Theory.GroupTheory.SolvableSylowOvergroups.OddActors
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Odd actors detected by orders of Sylow overgroups

An odd actor on a normal centerless group with two-group outer automorphism
quotient maps into its inner group. Intersect the image of the actor-Sylow
join with that inner group. It contains a full Sylow of the normal subgroup,
the actor embeds in it, and its order divides that of the original join.
Thus intrinsic restrictions on orders of Sylow overgroups detect the actor.

Source application: Aschbacher–Smith 5.2.2, printed pp.648–649.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [_root_.Group G] [Finite G]

/-- An odd actor is detected in an actual full-Sylow overgroup whose order
still divides the supplied bound on the original actor-Sylow join. -/
theorem no_odd_actor_of_sylow_order_bound
    (K E : Subgroup G) [K.Normal] (S : Sylow 2 G)
    {p m : ℕ} (ho : Odd p)
    (hz : center K = ⊥) (hout : IsPGroup 2 (MulAut.Outer K))
    (hbound : ∀ (P : Sylow 2 K) (J : Subgroup K), Nat.card J ∣ m →
      (P : Subgroup K) ≤ J → ¬ p ∣ Nat.card J)
    (hE : Nat.card E = p) (hd : Disjoint E (centralizer (K : Set G)))
    (hs : Nat.card (E ⊔ (S : Subgroup G) : Subgroup G) ∣ m) : False := by
  let f : G →* MulAut K := MulAut.conjNormal
  let i : K →* MulAut K := MulAut.conj
  have hi : Function.Injective i := conj_injective_of_center_eq_bot hz
  have hfi (k : K) : f k = i k := by
    ext x
    rfl
  have hEin : E.map f ≤ MulAut.innerSubgroup K := by
    let q := QuotientGroup.mk' (MulAut.innerSubgroup K)
    have hp : IsPGroup p (E.map f) :=
      (IsPGroup.of_card (p := p) (n := 1) (by simpa using hE)).map f
    have hodd := hp.map q
    have h2 := hout.to_subgroup ((E.map f).map q)
    have hb : (E.map f).map q = ⊥ := disjoint_self.mp (hodd.disjoint_of_coprime h2 ho.coprime_two_right)
    simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff (E.map f)).mp hb
  let ec : K ≃* MulAut.innerSubgroup K := MonoidHom.ofInjective hi
  let a : E →* MulAut.innerSubgroup K := (f.comp E.subtype).codRestrict _ (by
    intro e
    exact hEin (mem_map_of_mem f e.property))
  let g : E →* K := ec.symm.toMonoidHom.comp a
  have hg (e : E) : i (g e) = f e := by
    have he := ec.apply_symm_apply (a e)
    exact congrArg Subtype.val he
  have hgi : Function.Injective g := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro x hx
    have hfx : f x = 1 := by rw [←hg x,show g x = 1 from hx,map_one]
    have hxC : (x : G) ∈ centralizer (K : Set G) := by
      rw [←MulAut.conjNormal_ker_eq_centralizer]
      exact hfx
    exact Subtype.ext (mem_bot.mp (hd.le_bot ⟨x.property,hxC⟩))
  let J := (E ⊔ (S : Subgroup G)).map f
  let M := J.comap i
  have hM : Nat.card M ∣ m :=
    (card_dvd_of_injective (i.subgroupComap J)
      (fun x y he => Subtype.ext (hi (congrArg Subtype.val he)))).trans
        (((E ⊔ (S : Subgroup G)).card_map_dvd f).trans hs)
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal K
  have hPM : (P : Subgroup K) ≤ M := by
    intro k hk
    change i k ∈ J
    rw [←hfi k]
    have hkS : (k : G) ∈ S := by
      rw [hP] at hk
      exact hk
    exact mem_map_of_mem f (mem_sup_right hkS)
  have hr : g.range ≤ M := by
    rintro _ ⟨e,rfl⟩
    change i (g e) ∈ J
    rw [hg]
    exact mem_map_of_mem f (mem_sup_left e.property)
  have hc : Nat.card g.range = p :=
    (Nat.card_congr (MonoidHom.ofInjective hgi).toEquiv).symm.trans hE
  exact hbound P M hM hPM (hc ▸ card_dvd_of_le hr)
end Theory.GroupTheory
