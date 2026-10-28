module
public import Theory.PGroupCore
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Index

/-!
# Cubic normal subgroups in a pair of symmetric groups

The normal cubic base of S₃×S₃ has order nine. Its intersection with a
subgroup has order one, three or nine. The middle case gives the required
normal cubic; in the last case either cubic axis is normal. In the first
case the subgroup embeds in the two-group quotient, so a nontrivial group
with trivial two-core cannot occur.

Source application: Aschbacher--Smith G.10.4--5 and 14.3.15. The original
reducible action embeds in this pair; the no-normal-cubic source argument
then excludes it when the center is the marked point.
-/

open Subgroup
namespace Theory.GroupTheory.SymmetricThreePair
public abbrev Actor := Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)
private abbrev S3 := Equiv.Perm (Fin 3)
private def cubicBase : Subgroup Actor where
  carrier := {x | x.1^3=1 ∧ x.2^3=1}
  one_mem' := by simp
  mul_mem' := by
    have h : ∀ a b : S3, a^3=1 → b^3=1 → (a*b)^3=1 := by decide +kernel
    intro a b ha hb
    exact ⟨h _ _ ha.1 hb.1,h _ _ ha.2 hb.2⟩
  inv_mem' := by
    intro a ha
    exact ⟨by simpa only [Prod.fst_inv,Prod.snd_inv,inv_pow,inv_one] using congrArg Inv.inv ha.1,by simpa only [Prod.fst_inv,Prod.snd_inv,inv_pow,inv_one] using congrArg Inv.inv ha.2⟩
private instance : cubicBase.Normal where
  conj_mem x hx g := by
    exact ⟨by simp only [Prod.fst_mul,Prod.fst_inv,conj_pow,hx.1,mul_one,mul_inv_cancel],
      by simp only [Prod.snd_mul,Prod.snd_inv,conj_pow,hx.2,mul_one,mul_inv_cancel]⟩
private instance : DecidablePred (fun x : Actor => x∈cubicBase) := fun _ =>
  inferInstanceAs (Decidable (_^3=1 ∧ _^3=1))
private theorem base_card : Nat.card cubicBase=9 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel
private theorem actor_card : Nat.card Actor=36 := by
  norm_num [Actor,Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
private def axisGenerator : Actor := (Equiv.swap 0 1 * Equiv.swap 1 2,1)
private theorem axis_order : orderOf axisGenerator=3 := by
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel
private theorem axis_le_base : zpowers axisGenerator≤cubicBase := zpowers_le.mpr (by decide +kernel)
private instance : (zpowers axisGenerator).Normal := by
  apply normal_iff_map_conj_eq.mpr
  intro g
  rw [MonoidHom.map_zpowers]
  change zpowers (g*axisGenerator*g⁻¹)=zpowers axisGenerator
  have h : ∀ a : S3,
      a * axisGenerator.1 * a⁻¹=axisGenerator.1 ∨
      a * axisGenerator.1 * a⁻¹=axisGenerator.1⁻¹ := by decide +kernel
  rcases h g.1 with he | he
  · have hval : g*axisGenerator*g⁻¹=axisGenerator := Prod.ext he (by simp [axisGenerator])
    rw [hval]
  · have hval : g*axisGenerator*g⁻¹=axisGenerator⁻¹ := Prod.ext he (by simp [axisGenerator])
    rw [hval,zpowers_inv]

/-- A nontrivial subgroup of S₃×S₃ with trivial two-core has a normal cubic. -/
public theorem exists_normal_cubic (J : Subgroup Actor) (hne : J≠⊥)
    (hcore : pCore 2 J=⊥) : ∃ C : Subgroup J, C.Normal ∧ Nat.card C=3 := by
  let K := cubicBase.comap J.subtype
  let f : K→*cubicBase := {
    toFun := fun x => ⟨x.val.val,x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b he
    have hv : a.val.val=b.val.val := congrArg (fun x : cubicBase => (x:Actor)) he
    exact Subtype.ext (Subtype.ext hv)
  have hd : Nat.card K∣9 := base_card ▸ card_dvd_of_injective f hf
  have hcases : Nat.card K=1 ∨ Nat.card K=3 ∨ Nat.card K=9 := by
    have hh := Nat.mem_divisors.mpr ⟨hd,by decide⟩
    have he : (9:ℕ).divisors={1,3,9} := by decide
    rwa [he,Finset.mem_insert,Finset.mem_insert,Finset.mem_singleton] at hh
  rcases hcases with h1 | h3 | h9
  · have hK : K=⊥ := card_eq_one.mp h1
    let q := (QuotientGroup.mk' cubicBase).comp J.subtype
    have hq : Function.Injective q := by
      apply (MonoidHom.ker_eq_bot_iff q).mp
      have hk : q.ker=K := by
        ext x
        exact QuotientGroup.eq_one_iff (x:Actor)
      rw [hk,hK]
    have hquot : IsPGroup 2 (Actor⧸cubicBase) := by
      apply IsPGroup.of_card (n:=2)
      have hc := cubicBase.card_mul_index
      rw [base_card,actor_card,index_eq_card] at hc
      omega
    have hJ : IsPGroup 2 J := hquot.of_injective q hq
    have htop : (⊤:Subgroup J)≤pCore 2 J := le_sSup ⟨inferInstance,hJ.to_subgroup ⊤⟩
    rw [hcore] at htop
    let : Subsingleton J := ⟨fun x y => by
      have hx : x=1 := htop (mem_top x)
      have hy : y=1 := htop (mem_top y)
      exact hx.trans hy.symm⟩
    exact (hne (eq_bot_of_subsingleton J)).elim
  · exact ⟨K,inferInstance,h3⟩
  · have hfs : Function.Surjective f :=
      (Nat.bijective_iff_injective_and_card f).mpr ⟨hf,h9.trans base_card.symm⟩ |>.2
    have hBJ : cubicBase≤J := by
      intro x hx
      obtain ⟨y,hy⟩ := hfs ⟨x,hx⟩
      have he : y.val.val=x := congrArg Subtype.val hy
      exact he ▸ y.val.property
    have hAJ := axis_le_base.trans hBJ
    refine ⟨(zpowers axisGenerator).subgroupOf J,inferInstance,?_⟩
    exact (Nat.card_congr (subgroupOfEquivOfLe hAJ).toEquiv).trans
      ((Nat.card_zpowers axisGenerator).trans axis_order)
/-- The finite conclusion retains the original group and faithful map. -/
public theorem exists_normal_cubic_of_injective
    {D : Type*} [Group D] [Finite D] [Nontrivial D]
    (f : D →* Actor) (hf : Function.Injective f) (hcore : pCore 2 D=⊥) :
    ∃ C : Subgroup D, C.Normal ∧ Nat.card C=3 := by
  let e : D≃*f.range := MonoidHom.ofInjective hf
  have hne : f.range≠⊥ := by
    intro hz
    obtain ⟨d,hd⟩ := exists_ne (1:D)
    have hm : f d∈f.range := ⟨d,rfl⟩
    rw [hz,mem_bot] at hm
    exact hd (hf (hm.trans f.map_one.symm))
  have hcore' : pCore 2 f.range=⊥ := by
    rw [← pCore_map_iso 2 e,hcore,Subgroup.map_bot]
  obtain ⟨C,hCn,hCc⟩ := exists_normal_cubic f.range hne hcore'
  refine ⟨C.map e.symm.toMonoidHom,hCn.map _ e.symm.surjective,?_⟩
  exact (card_map_of_injective e.symm.injective).trans hCc
end Theory.GroupTheory.SymmetricThreePair
