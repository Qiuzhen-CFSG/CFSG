module
public import Theory.SpecificGroups.SU3.SmallSpecialExtraspecial
public import Theory.GroupAction.Extraspecial27TwoActor

/-!
# Innerness of the actual small special-unitary two-power actors

Restrict the automorphisms preserving an actual Sylow two-subgroup T and
fixing the scalar center to the extraspecial three-core. This restriction
is faithful. The inner image of T is a normal subgroup of order eight.
Adjoining a two-power actor still gives a two-group, whose faithful
center-preserving action on the three-core has order at most eight.
The actor therefore already belongs to that inner image.

This avoids a general automorphism classification: it proves precisely
the innerness needed by the original full-Borel-core action in DGS 6.1.
The scalar kernel and the actual Sylow are retained throughout.
Source: DGS, Groups and Graphs (1985), 6.1 and remark, pp.118--119.
-/

public noncomputable section
open Subgroup MulAction
open scoped Pointwise
namespace BenderSuzuki.MatrixGroups.HermitianForm.SmallThreeCore
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)

/-- Every center-fixing two-power automorphism of SU3(2) preserving an actual Sylow two-subgroup is conjugation by an element of that Sylow. -/
theorem special_inner_of_two_power_center_fixed (hc:Nat.card F=2^2)
    (hconj:∀ x,J.conj x=x^2) (T:Sylow 2 J.specialSubgroup)
    (a:MulAut J.specialSubgroup) {k:ℕ} (ha:a^(2^k)=1)
    (hT:(T:Subgroup J.specialSubgroup).map a.toMonoidHom=T)
    (hz:∀ z∈center J.specialSubgroup,a z=z) :
    ∃ t:T, MulAut.conj (t:J.specialSubgroup)=a := by
  let D := J.specialSubgroup
  let N := pCore 3 D
  let H := stabilizer (MulAut D) (T:Subgroup D) ⊓ fixingSubgroup (MulAut D) (center D:Set D)
  let r : H →* MulAut N := (MulAut.characteristic N).comp H.subtype
  have hr : Function.Injective r := by
    apply (MonoidHom.ker_eq_bot_iff r).mp
    apply (eq_bot_iff_forall _).mpr
    intro b hb
    apply Subtype.ext
    apply special_aut_eq_one_of_core_and_sylow J hc hconj T b.val b.property.1
    intro n hn
    exact congrArg Subtype.val (DFunLike.congr_fun hb (⟨n,hn⟩:N))
  have hfix (b:H) (z:N) (hzN:z∈center N) : r b z=z := by
    apply Subtype.ext
    have hk : z∈(specialCoreProjection J).ker := (special_core_center J hc hconj).le hzN
    exact (mem_fixingSubgroup_iff (MulAut D)).mp b.property.2 z.val
      (J.specialToProjective_ker_le_center (congrArg Subtype.val hk))
  let f : T →* H := ((MulAut.conj : D →* MulAut D).comp (T:Subgroup D).subtype).codRestrict H (by
    intro t
    constructor
    · change (T:Subgroup D).map (MulAut.conj (t:D)).toMonoidHom=T
      apply le_antisymm
      · rintro x ⟨y,hy,rfl⟩
        exact (T:Subgroup D).mul_mem ((T:Subgroup D).mul_mem t.property hy) ((T:Subgroup D).inv_mem t.property)
      · intro x hx
        refine ⟨(t:D)⁻¹*x*t,?_,?_⟩
        · exact (T:Subgroup D).mul_mem ((T:Subgroup D).mul_mem ((T:Subgroup D).inv_mem t.property) hx) t.property
        · simp [MulAut.conj_apply,mul_assoc]
    · apply (mem_fixingSubgroup_iff (MulAut D)).mpr
      intro z hzz
      change (t:D)*z*(t:D)⁻¹=z
      rw [mem_center_iff.mp hzz t.val,mul_inv_cancel_right])
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply (eq_bot_iff_forall _).mpr
    intro t ht
    have he : MulAut.conj (t:D)=1 := congrArg Subtype.val ht
    have hct : (t:D) ∈ centralizer (N:Set D) := by
      intro n hn
      have hh := DFunLike.congr_fun he n
      change (t:D)*n*(t:D)⁻¹=n at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hk := (special_core_centralizer J hc hconj).le hct
    have ht3 : t^3=1 := Subtype.ext (congrArg
      (fun z:J.specialToProjective.ker => (z:D)) (J.specialToProjective_ker_cube ⟨t,hk⟩))
    exact (T.isPGroup'.powEquiv (by decide:Nat.Coprime 2 3)).injective
      (ht3.trans (one_pow 3).symm)
  let I := f.range
  have hI : I.Normal := by
    constructor
    intro x hx b
    obtain ⟨t,rfl⟩ := hx
    have ht : (b:MulAut D) t.val ∈ (T:Subgroup D) := by
      have hm : (T:Subgroup D).map (b:MulAut D).toMonoidHom=T := b.property.1
      exact hm.le (mem_map_of_mem _ t.property)
    refine ⟨⟨(b:MulAut D) t.val,ht⟩,?_⟩
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    change b.val (t:D) * x * (b.val (t:D))⁻¹ =
      b.val ((t:D) * (b.val.symm x) * (t:D)⁻¹)
    simp only [map_mul,map_inv,MulEquiv.apply_symm_apply]
  let := hI
  have hIc : Nat.card I=8 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hf).symm.toEquiv,T.card_eq_multiplicity,
      special_group_card J hc hconj]
    decide +kernel
  let aH:H := ⟨a,⟨hT,(mem_fixingSubgroup_iff (MulAut D)).mpr hz⟩⟩
  let R := I ⊔ zpowers aH
  have hcyc : IsPGroup 2 (zpowers aH) := IsPGroup.of_card_dvd_pow (n:=k) (by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one (show aH^(2^k)=1 from Subtype.ext ha))
  have hR : IsPGroup 2 R := (T.isPGroup'.of_surjective f.rangeRestrict f.rangeRestrict_surjective).to_sup_of_normal_left hcyc
  let rR : R →* MulAut N := r.comp R.subtype
  let := special_core_extraspecial J hc hconj
  have hd : Nat.card R ∣ 8 := MulAut.two_center_preserving_card_dvd_eight hR
    (special_core_card J hc hconj) rR (hr.comp R.subtype_injective) (fun b => hfix b.val)
  have heq : R=I := (eq_of_le_of_card_ge (show I≤R from le_sup_left)
    (by rw [hIc]; exact Nat.le_of_dvd (by decide) hd)).symm
  have hai : aH∈I := heq ▸ (show aH∈R from (show zpowers aH ≤ R from le_sup_right) (mem_zpowers aH))
  obtain ⟨t,ht⟩ := hai
  exact ⟨t,congrArg Subtype.val ht⟩
end BenderSuzuki.MatrixGroups.HermitianForm.SmallThreeCore
