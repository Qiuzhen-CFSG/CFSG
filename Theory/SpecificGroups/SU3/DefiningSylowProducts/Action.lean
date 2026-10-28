module
public import Theory.SpecificGroups.SU3.DefiningSylowProducts.Arithmetic
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Logic.Equiv.Option
public import Theory.GroupTheory.SubgroupProductCard
public import Theory.GroupTheory.PResidual.SubnormalSupplement
/-!
# Root-action obstruction to a defining unitary Sylow product

A p-subgroup of order p² or p³ can be conjugated into the literal root
Sylow subgroup. Its action is free away from the root fixed point. Thus an
overgroup orbit is one modulo p² and divides the two-part times |U|;
it is a power of two. The unitary order bound forces this orbit to be one,
contradicting the even index of the point stabilizer containing a full Sylow.
The argument keeps the original subgroup product and conjugates both factors.
-/
public section
open Subgroup MulAction
open scoped Pointwise
namespace UnitaryDefining
theorem free_complement_orbit_dvd
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [Finite X]
    (H U : Subgroup G) (hUH : U ≤ H) (a : X)
    (hfix : ∀ u : U, (u : G) • a = a)
    (hfree : ∀ (u : U) (x : X), x ≠ a → (u : G) • x = x → u = 1) :
    Nat.card U ∣ Nat.card (orbit H a) - 1 := by
  classical
  let : MulAction U (orbit H a) := MulAction.compHom _ (inclusion hUH)
  let a' : orbit H a := ⟨a, mem_orbit_self a⟩
  have hfix' (u : U) : u • a' = a' := Subtype.ext (hfix u)
  let X₀ : SubMulAction U (orbit H a) := {
    carrier := {x | x ≠ a'}
    smul_mem' := by
      intro u x hx he
      apply hx
      apply (MulAction.injective u)
      exact he.trans (hfix' u).symm }
  have hstab (x : X₀) : stabilizer U x = ⊥ := by
    apply (eq_bot_iff_forall _).mpr
    intro u hu
    apply hfree u x.val.val
    · intro he
      exact x.property (Subtype.ext he)
    · exact congrArg (fun y : X₀ => y.val.val) (mem_stabilizer_iff.mp hu)
  have hd : Nat.card U ∣ Nat.card X₀ := by
    let := Fintype.ofFinite (Quotient (orbitRel U X₀))
    rw [Nat.card_congr (selfEquivSigmaOrbitsQuotientStabilizer U X₀), Nat.card_sigma]
    apply Finset.dvd_sum
    intro ω _
    change Nat.card U ∣ (stabilizer U ω.out).index
    rw [hstab, index_bot]
  have hc := Nat.card_congr (Equiv.optionSubtypeNe a')
  let := Fintype.ofFinite (orbit H a)
  simp only [Nat.card_eq_fintype_card, Fintype.card_option] at hc
  simp only [← Nat.card_eq_fintype_card] at hc
  change Nat.card X₀ + 1 = Nat.card (orbit H a) at hc
  rwa [← hc, Nat.add_sub_cancel]


private theorem fixed_product_exclusion
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [Finite X]
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hlarge : 3<p)
    (hG : Nat.card G ∣ (p^3+1)*p^3*(p^2-1))
    (S : Sylow 2 G) (H U : Subgroup G) (hSH : (S:Subgroup G)≤H)
    (hH : Nat.card H=Nat.card S*Nat.card U)
    (hU : Nat.card U=p^2 ∨ Nat.card U=p^3) (hUH : U≤H)
    (a : X) (hfix : ∀u:U,(u:G) • a=a)
    (hfree : ∀(u:U)(x:X),x≠a→(u:G) • x=x→u=1)
    (hindex : 2∣(stabilizer G a).index) : False := by
  have hd := free_complement_orbit_dvd H U hUH a hfix hfree
  have hd2 : p^2∣Nat.card (orbit H a)-1 := by
    rcases hU with hu | hu
    · rwa [hu] at hd
    · exact (pow_dvd_pow p (by decide : 2≤3)).trans (hu ▸ hd)
  have hpos : 0<Nat.card (orbit H a) := by
    let : Nonempty (orbit H a) := ⟨⟨a,mem_orbit_self a⟩⟩
    exact Nat.card_pos
  have hnp : ¬p∣Nat.card (orbit H a) := by
    intro hh
    have hd1 : p∣Nat.card (orbit H a)-1 := (dvd_pow_self p (by decide : 2≠0)).trans hd2
    have hp2 := hp.two_le
    obtain ⟨i,hi⟩ := hh
    obtain ⟨j,hj⟩ := hd1
    have he : p*i=p*j+1 := by omega
    have hm := congrArg (fun n=>n%p) he
    norm_num [Nat.mul_mod,Nat.add_mod,Nat.mod_eq_of_lt hp.one_lt] at hm
  have hcop : Nat.Coprime (Nat.card (orbit H a)) (Nat.card U) := by
    rcases hU with hu | hu <;> rw [hu]
    all_goals exact ((hp.coprime_iff_not_dvd.mpr hnp).symm).pow_right _
  have hi : Nat.card (orbit H a) ∣ Nat.card S*Nat.card U := by
    simpa only [index_stabilizer,←Nat.card_coe_set_eq,hH] using (stabilizer H a).index_dvd_card
  have hdivS := hcop.dvd_of_dvd_mul_right hi
  obtain ⟨k,hk⟩ := IsPGroup.iff_card.mp S.isPGroup'
  have hbound := unitary_order_two_power_bound hlarge ho
    (hk ▸ S.toSubgroup.card_subgroup_dvd_card.trans hG)
  rw [hk] at hdivS
  obtain ⟨j,hjk,hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdivS
  have hone : Nat.card (orbit H a)=1 := by
    rw [hj]
    exact orbit_eq_one hlarge ho (lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hjk) hbound)
      (hj ▸ hd2)
  have hHS : H≤stabilizer G a := by
    intro g hg
    apply mem_stabilizer_iff.mpr
    have : Subsingleton (orbit H a) := (Nat.card_eq_one_iff_unique.mp hone).1
    exact congrArg Subtype.val (Subsingleton.elim
      (⟨g • a,mem_orbit a (⟨g,hg⟩:H)⟩:orbit H a) ⟨a,mem_orbit_self a⟩)
  exact S.not_dvd_index (hindex.trans (index_dvd_of_le (hSH.trans hHS)))
/-- A root group acting freely off one point excludes the full Sylow product. -/
theorem root_action_not_permuting
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [Finite X]
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hlarge : 3<p)
    (hG : Nat.card G ∣ (p^3+1)*p^3*(p^2-1))
    (V : Subgroup G) (hV : Nat.card V=p^3) (a : X)
    (hfix : ∀v:V,(v:G) • a=a)
    (hfree : ∀(v:V)(x:X),x≠a→(v:G) • x=x→v=1)
    (hindex : 2∣(stabilizer G a).index)
    (S : Sylow 2 G) (U : Subgroup G) (hU : Nat.card U=p^2 ∨ Nat.card U=p^3) :
    (U:Set G)*(S:Set G) ≠ (S:Set G)*(U:Set G) := by
  intro hperm
  let : Fact p.Prime := ⟨hp⟩
  have hVp : IsPGroup p V := IsPGroup.of_card hV
  have hp3 : 0<p^3 := pow_pos hp.pos _
  have hVi : V.index∣(p^3+1)*(p^2-1) := by
    have hh := hG
    rw [←V.card_mul_index,hV] at hh
    have hr : (p^3+1)*p^3*(p^2-1)=p^3*((p^3+1)*(p^2-1)) := by ring
    rw [hr] at hh
    exact (Nat.mul_dvd_mul_iff_left hp3).mp hh
  have hnot : ¬p∣V.index := by
    intro hh
    rcases hp.dvd_mul.mp (hh.trans hVi) with h1 | h2
    · have hh1 : (p^3+1)%p=1 := by simp [Nat.add_mod,Nat.pow_mod,Nat.mod_eq_of_lt hp.one_lt]
      have hh0 := Nat.mod_eq_zero_of_dvd h1
      omega
    · have hsub : p^2-1+1=p^2 := Nat.sub_add_cancel (by nlinarith [hp.two_le])
      have hh0 := Nat.mod_eq_zero_of_dvd h2
      have hh := congrArg (fun n=>n%p) hsub
      simp [Nat.add_mod,Nat.pow_mod,hh0,Nat.mod_eq_of_lt hp.one_lt] at hh
  let P : Sylow p G := hVp.toSylow hnot
  have hUp : IsPGroup p U := by
    rcases hU with hu | hu <;> exact IsPGroup.of_card hu
  obtain ⟨T,hUT⟩ := hUp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G T P
  let e := MulAut.conj g
  let S' := S.mapSurjective (f:=e.toMonoidHom) e.surjective
  let U' := U.map e.toMonoidHom
  have hUV : U'≤V := by
    have he : (T:Subgroup G).map e.toMonoidHom=V := congrArg Sylow.toSubgroup hg
    exact he ▸ map_mono hUT
  have hperm' : (U':Set G)*(S':Set G)=(S':Set G)*(U':Set G) := by
    have hh := congrArg (Set.image e) hperm
    change ((U.map e.toMonoidHom):Set G)*(((S:Subgroup G).map e.toMonoidHom):Set G) =
      (((S:Subgroup G).map e.toMonoidHom):Set G)*((U.map e.toMonoidHom):Set G)
    simpa only [Set.image_mul,Subgroup.coe_map,Sylow.coe_coe,MulEquiv.coe_toMonoidHom] using hh
  have hU' : Nat.card U'=p^2 ∨ Nat.card U'=p^3 := by
    change Nat.card (U.map e.toMonoidHom)=p^2 ∨ Nat.card (U.map e.toMonoidHom)=p^3
    rw [card_map_of_injective e.injective]
    exact hU
  have hdis : Disjoint U' (S':Subgroup G) :=
    IsPGroup.disjoint_of_coprime (hUp.map e.toMonoidHom) S'.isPGroup' (Nat.coprime_two_right.mpr ho)
  let H := U'⊔(S':Subgroup G)
  have hH : Nat.card H=Nat.card S'*Nat.card U' := by
    have hh := card_set_mul_mul_card_inf U' (S':Subgroup G)
    rw [disjoint_iff.mp hdis,card_bot,mul_one] at hh
    change Nat.card ((↑H):Set G)=_
    rw [coe_sup_of_set_mul_comm U' S' hperm']
    simpa only [mul_comm] using hh
  apply fixed_product_exclusion p hp ho hlarge hG S' H U' le_sup_right hH hU' le_sup_left a
  · exact fun u=>hfix ⟨u,hUV u.property⟩
  · intro u x hx hh
    exact Subtype.ext (congrArg (fun v:V=>(v:G)) (hfree ⟨u,hUV u.property⟩ x hx hh))
  · exact hindex
end UnitaryDefining
