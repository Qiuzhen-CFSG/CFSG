module
public import Theory.GroupTheory.SolvableSylowOvergroups.OddActors
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Odd actors on perfect central covers

Faithful descent of automorphisms retains the centralizer kernel when a
normal perfect subgroup is replaced by its central quotient. The odd actor
lands in the inner group of a centerless quotient with two-group outer group.
Its image and a full quotient Sylow lie in a subgroup whose order divides
the original actor–Sylow join. This extends the order obstruction to central
covers without discarding their centers.

Source application: the central M₂₂ cover in Aschbacher–Smith 5.2.2,
printed pp.648–649 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [_root_.Group G] [Finite G]

/-- The actual central-quotient action detects an odd actor in a full-Sylow
overgroup with the original order bound. -/
theorem no_odd_actor_of_central_cover_sylow_order_bound
    {M : Type*} [_root_.Group M] [Finite M]
    (K E : Subgroup G) [K.Normal] [Group.IsPerfect K]
    (e : K ⧸ center K ≃* M) (S : Sylow 2 G)
    {p m : ℕ} (ho : Odd p)
    (hz : center M = ⊥) (hout : IsPGroup 2 (MulAut.Outer M))
    (hbound : ∀ (P : Sylow 2 M) (J : Subgroup M), Nat.card J ∣ m →
      (P : Subgroup M) ≤ J → ¬ p ∣ Nat.card J)
    (hE : Nat.card E = p) (hd : Disjoint E (centralizer (K : Set G)))
    (hs : Nat.card (E ⊔ (S : Subgroup G) : Subgroup G) ∣ m) : False := by
  let f : G →* MulAut M :=
    (MulAut.centralQuotientAction e).comp MulAut.conjNormal
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let i : M →* MulAut M := MulAut.conj
  have hi : Function.Injective i := conj_injective_of_center_eq_bot hz
  have hfi (k : K) : f k = i (q k) := by
    change MulAut.centralQuotientAction e (MulAut.conjNormal (k : G)) = _
    have hk : MulAut.conjNormal (k : G) = MulAut.conj k := by ext x; rfl
    rw [hk,MulAut.centralQuotientAction_conj]
    rfl
  have hker : f.ker = centralizer (K : Set G) := by
    change ((MulAut.centralQuotientAction e).comp (MulAut.conjNormal : G →* MulAut K)).ker = _
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.centralQuotientAction_injective e)]
    exact MulAut.conjNormal_ker_eq_centralizer K
  have hEin : E.map f ≤ MulAut.innerSubgroup M := by
    let q := QuotientGroup.mk' (MulAut.innerSubgroup M)
    have hp : IsPGroup p (E.map f) :=
      (IsPGroup.of_card (p := p) (n := 1) (by simpa using hE)).map f
    have hodd := hp.map q
    have h2 := hout.to_subgroup ((E.map f).map q)
    have hb : (E.map f).map q = ⊥ := disjoint_self.mp (hodd.disjoint_of_coprime h2 ho.coprime_two_right)
    simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff (E.map f)).mp hb
  let ec : M ≃* MulAut.innerSubgroup M := MonoidHom.ofInjective hi
  let a : E →* MulAut.innerSubgroup M := (f.comp E.subtype).codRestrict _ (by
    intro e
    exact hEin (mem_map_of_mem f e.property))
  let g : E →* M := ec.symm.toMonoidHom.comp a
  have hg (e : E) : i (g e) = f e := by
    have he := ec.apply_symm_apply (a e)
    exact congrArg Subtype.val he
  have hgi : Function.Injective g := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro x hx
    have hfx : f x = 1 := by rw [←hg x,show g x = 1 from hx,map_one]
    have hxC : (x : G) ∈ centralizer (K : Set G) := by
      rw [←hker]
      exact hfx
    exact Subtype.ext (mem_bot.mp (hd.le_bot ⟨x.property,hxC⟩))
  let J := (E ⊔ (S : Subgroup G)).map f
  let N := J.comap i
  have hM : Nat.card N ∣ m :=
    (card_dvd_of_injective (i.subgroupComap J)
      (fun x y he => Subtype.ext (hi (congrArg Subtype.val he)))).trans
        (((E ⊔ (S : Subgroup G)).card_map_dvd f).trans hs)
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal K
  have hPM : ((P.mapSurjective hq : Sylow 2 M) : Subgroup M) ≤ N := by
    rintro _ ⟨k,hk,rfl⟩
    change i (q k) ∈ J
    rw [←hfi k]
    have hkS : (k : G) ∈ S := by
      rw [hP] at hk
      exact hk
    exact mem_map_of_mem f (mem_sup_right hkS)
  have hr : g.range ≤ N := by
    rintro _ ⟨e,rfl⟩
    change i (g e) ∈ J
    rw [hg]
    exact mem_map_of_mem f (mem_sup_left e.property)
  have hc : Nat.card g.range = p :=
    (Nat.card_congr (MonoidHom.ofInjective hgi).toEquiv).symm.trans hE
  exact hbound (P.mapSurjective hq) N hM hPM (hc ▸ card_dvd_of_le hr)
end Theory.GroupTheory
