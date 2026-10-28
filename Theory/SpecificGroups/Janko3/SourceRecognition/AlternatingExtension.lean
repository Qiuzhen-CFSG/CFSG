module
public import Theory.SpecificGroups.AlternatingSix.OuterInvolutionExtension.PGLComparison
public import Mathlib.GroupTheory.Complement

/-!
# Recognizing the involutory extension of A₆ containing an element of order eight

If the supplement acted inner, it would be a product of an involution
centralizing A₆ and an involution in A₆. Their commuting product would
have no element of order eight: every permutation of six letters whose
eighth power is one has fourth power one. This proves faithfulness of
the actual conjugation action. The same order-eight witness excludes the
natural S₆ image, and the established exceptional-automorphism comparison
identifies the extension with the literal PGL₂(9) model.

Source: Baumeister, *A geometry for groups of J₃-type* (2007),
Lemma 2.4, p.495. The exceptional automorphism comparison uses the
existing checked GLS III, Proposition 5.2.7 calculation.
-/

public noncomputable section
open Subgroup
open AlternatingSix.ShadowLocal AlternatingSix.OuterInvolutionExtension
namespace Sporadic.Janko3.SourceRecognition

private theorem perm_six_eighth (a : Equiv.Perm (Fin 6)) (ha : a^8=1) : a^4=1 := by
  apply orderOf_dvd_iff_pow_eq_one.mp
  rw [← a.lcm_cycleType, Multiset.lcm_dvd]
  intro n hn
  have hn8 : n ∣ 8 := (Equiv.Perm.dvd_of_mem_cycleType hn).trans
    (orderOf_dvd_of_pow_eq_one ha)
  have hn6 : n ≤ 6 := (Multiset.le_sum_of_mem hn).trans a.sum_cycleType_le
  interval_cases n <;> norm_num at hn8 <;> norm_num

private theorem alternating_six_eighth {H : Type*} [Group H]
    (e : H ≃* alternatingGroup (Fin 6)) (a : H) (ha : a^8=1) : a^4=1 := by
  apply e.injective
  rw [map_pow,map_one]
  apply Subtype.ext
  change ((e a : Equiv.Perm (Fin 6))^4)=1
  apply perm_six_eighth
  change (e a ^ 8 : alternatingGroup (Fin 6)).val = 1
  rw [← map_pow,ha,map_one]
  rfl

private theorem involution_outer_of_eight {H : Type*} [Group H] [Finite H]
    (L : Subgroup H) [L.Normal] (e : L ≃* alternatingGroup (Fin 6))
    (r : H) (hr2 : r^2=1) (hgen : L ⊔ zpowers r = ⊤)
    (x : H) (hx : orderOf x = 8) : r ∉ centralizer (L : Set H) ⊔ L := by
  let C := centralizer (L : Set H)
  have hdis : Disjoint C L := by
    apply disjoint_def.mpr
    intro y hyC hyL
    have hz : e ⟨y,hyL⟩ ∈ center (alternatingGroup (Fin 6)) := by
      apply mem_center_iff.mpr
      intro a
      obtain ⟨a,rfl⟩ := e.surjective a
      rw [← map_mul,← map_mul]
      apply congrArg e
      exact Subtype.ext (hyC a a.property)
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hz
    exact congrArg Subtype.val (e.injective (hz.trans e.map_one.symm))
  intro hr
  obtain ⟨c,hc,l,hl,hcl⟩ := mem_sup_of_normal_right.mp hr
  have hcomm : Commute c l := (mem_centralizer_iff.mp hc l hl).symm
  have hsq : c^2*l^2=1 := by rw [← hcomm.mul_pow,hcl,hr2]
  have hc2L : c^2 ∈ L := by
    rw [eq_inv_of_mul_eq_one_left hsq]
    exact L.inv_mem (L.pow_mem hl 2)
  have hc2 : c^2=1 := disjoint_def.mp hdis (C.pow_mem hc 2) hc2L
  have hgen' : zpowers c ⊔ L = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply sup_le le_sup_right
    apply zpowers_le.mpr
    rw [← hcl]
    exact mul_mem (mem_sup_left (mem_zpowers c)) (mem_sup_right hl)
  have hxmem : x ∈ zpowers c ⊔ L := hgen'.symm ▸ mem_top x
  obtain ⟨d,hd,l,hl,hdx⟩ := mem_sup_of_normal_right.mp hxmem
  have hd2 : d^2=1 := by
    obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp hd
    rw [← zpow_natCast,← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc2, one_zpow]
  have hdC : d ∈ C := (zpowers_le.mpr hc) hd
  have hdl : Commute d l := (mem_centralizer_iff.mp hdC l hl).symm
  have hd4 : d^4=1 := by rw [show 4=2*2 by decide,pow_mul,hd2,one_pow]
  have hd8 : d^8=1 := by rw [show 8=2*4 by decide,pow_mul,hd2,one_pow]
  have hl8 : l^8=1 := by
    have hh : x^8=1 := hx ▸ pow_orderOf_eq_one x
    rw [← hdx,hdl.mul_pow,hd8,one_mul] at hh
    exact hh
  have hl4 : l^4=1 := congrArg Subtype.val
    (alternating_six_eighth e ⟨l,hl⟩ (Subtype.ext hl8))
  have hx4 : x^4=1 := by rw [← hdx,hdl.mul_pow,hd4,hl4,one_mul]
  have hd := orderOf_dvd_of_pow_eq_one hx4
  norm_num [hx] at hd

/-- An alternating-six subgroup, an actual involutory supplement,
and an element of order eight identify the whole extension as PGL₂(9). -/
theorem pgl_nine_of_alternating_involution_eight {H : Type*} [Group H] [Finite H]
    (L : Subgroup H) [L.Normal] (e : L ≃* alternatingGroup (Fin 6))
    (r : H) (hr : orderOf r = 2) (hgen : L ⊔ zpowers r = ⊤)
    (x : H) (hx : orderOf x = 8) :
    Nonempty (H ≃* GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F) := by
  have hrN : r ∈ normalizer (L : Set H) := by rw [normalizer_eq_top]; exact mem_top _
  have hr2 : r^2=1 := hr ▸ pow_orderOf_eq_one r
  have hout := involution_outer_of_eight L e r hr2 hgen x hx
  let a := normalizerAction e ⟨r,hrN⟩
  let E := extensionEquiv e hrN hr hout
  have ha2 : a^2=1 := normalizerAction_sq e hrN hr2
  have hn : a ∉ natural := by
    intro hn
    have hle : AlternatingSix.ShadowLocal.inner ⊔ zpowers a ≤ natural :=
      sup_le inner_le_natural (zpowers_le.mpr hn)
    let y : ↥(L ⊔ zpowers r) := ⟨x,hgen.symm ▸ mem_top x⟩
    have hy8 : orderOf (E y : AutA6) = 8 :=
      (orderOf_coe (E y)).trans ((E.orderOf_eq y).trans ((orderOf_coe y).symm.trans hx))
    obtain ⟨p,hp⟩ := hle (E y).property
    change permutationAction p = (E y : AutA6) at hp
    have hp8 : orderOf p = 8 := by
      rw [← orderOf_injective permutationAction permutationAction_injective, hp]
      exact hy8
    have hp4 := perm_six_eighth p (hp8 ▸ pow_orderOf_eq_one p)
    have hd := orderOf_dvd_of_pow_eq_one hp4
    norm_num [hp8] at hd
  obtain ⟨ec⟩ := exceptional_extension_equiv_canonical a ha2 hn
  obtain ⟨ep⟩ := canonicalExtension_equiv_pgl2
  exact ⟨((Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hgen.symm)).trans E).trans (ec.trans ep)⟩
end Sporadic.Janko3.SourceRecognition
