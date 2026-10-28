module
public import Theory.GroupTheory.CubicCoreQuotientNormalizer
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Odd actors detected by solvable Sylow overgroups

Let K be a normal centerless subgroup whose outer automorphism group is a
two-group. An odd-order actor disjoint from C_G(K) maps injectively into
Inn(K). If its join with a full ambient Sylow two-subgroup is solvable,
its image lies in a solvable subgroup of K containing the actual Sylow
intersection. Thus an intrinsic order bound on these solvable subgroups
excludes the actor. The ambient action need not be faithful.

Source application: Aschbacher–Smith 5.1.13 and 5.2.2, printed
pp.636–638,648–649, in the odd-characteristic containing-component rows.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [_root_.Group G] [Finite G]

/-- A faithful odd-order actor on a centerless normal subgroup is detected
in a solvable Sylow overgroup of that subgroup when its outer group is a two-group. -/
theorem no_odd_actor_of_solvable_sylow_bound
    (K E : Subgroup G) [K.Normal] (S : Sylow 2 G)
    {p : ℕ} (ho : Odd p)
    (hz : center K = ⊥) (hout : IsPGroup 2 (MulAut.Outer K))
    (hbound : ∀ (P : Sylow 2 K) (J : Subgroup K), Group.IsSolvable J →
      (P : Subgroup K) ≤ J → ¬ p ∣ Nat.card J)
    (hE : Nat.card E = p) (hd : Disjoint E (centralizer (K : Set G)))
    (hs : Group.IsSolvable (E ⊔ (S : Subgroup G) : Subgroup G)) : False := by
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
  let := hs
  let : Group.IsSolvable J := Group.isSolvable_of_surjective (f.subgroupMap_surjective _)
  let : Group.IsSolvable M := Group.isSolvable_of_isSolvable_injective
    (f := i.subgroupComap J) (fun x y he => Subtype.ext (hi (congrArg Subtype.val he)))
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
  exact hbound P M inferInstance hPM (hc ▸ card_dvd_of_le hr)
end Theory.GroupTheory
