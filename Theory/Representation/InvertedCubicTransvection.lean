module
public import Theory.GroupTheory.ZStar.OddProductConjugator
public import Theory.Representation.OrderTwoTransvections
public import Stellmacher.SectionOne.OrderTwoSylowInvolutions
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Normality of a cubic subgroup inverted by a binary transvection

In a finite faithful binary action with a Sylow two-subgroup of order two,
one transvection makes every involution a transvection by conjugacy.
The existing three-involution bound then makes the rotation subgroup of
any noncommuting involution pair normal. If t inverts a cubic c, its pair
with ctc⁻¹ has rotation c, proving that the original cubic is normal.

Additional odd-order centralizing factors are permitted; the theorem does
not identify the full odd core. Source application: Aschbacher–Smith,
C.5.13, the A₃-block branch, printed p.162.
-/
public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem rotation_normal_of_three_involutions
    (t u : G) (ht : IsInvolution t) (hu : IsInvolution u)
    (hthree : ∀ {x : G}, IsInvolution x → x = t ∨ x = u ∨ x = u⁻¹*t*u) :
    (zpowers (t*u)).Normal := by
  let K := zpowers (t*u)
  have hti : t⁻¹ = t := inv_eq_self_of_orderOf_eq_two (orderOf_eq_prime ht.2 ht.1)
  have hui : u⁻¹ = u := inv_eq_self_of_orderOf_eq_two (orderOf_eq_prime hu.2 hu.1)
  have htt : t*t = 1 := by simpa only [pow_two] using ht.2
  have huu : u*u = 1 := by simpa only [pow_two] using hu.2
  have htu : t*u ∈ K := mem_zpowers _
  have hut : u*t ∈ K := by
    have hh := K.inv_mem htu
    simpa only [mul_inv_rev,hti,hui] using hh
  have hm (a b : G) (ha : IsInvolution a) (hb : IsInvolution b) : a*b ∈ K := by
    rcases hthree ha with h1 | h1 | h1 <;> rcases hthree hb with h2 | h2 | h2 <;> rw [h1,h2]
    · simpa only [htt] using K.one_mem
    · exact htu
    · have he : t*(u⁻¹*t*u) = (t*u)*(t*u) := by rw [hui]; group
      rw [he]
      exact K.mul_mem htu htu
    · exact hut
    · simpa only [huu] using K.one_mem
    · simpa only [← mul_assoc,mul_inv_cancel,one_mul] using htu
    · have he : (u⁻¹*t*u)*t = (u*t)*(u*t) := by rw [hui]; group
      rw [he]
      exact K.mul_mem hut hut
    · have he : (u⁻¹*t*u)*u = u*t := by simp only [mul_assoc,huu,mul_one,hui]
      rw [he]
      exact hut
    · have he : (u⁻¹*t*u)*(u⁻¹*t*u) = 1 := by
        calc
          _ = u⁻¹*(t*t)*u := by group
          _ = 1 := by rw [htt]; simp
      rw [he]
      exact K.one_mem
  apply normalizer_eq_top_iff.mp
  apply top_unique
  intro g _
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · change (zpowers (t*u)).map (MulAut.conj g).toMonoidHom ≤ K
    rw [MonoidHom.map_zpowers]
    apply zpowers_le.mpr
    rw [map_mul]
    apply hm
    · refine ⟨?_,?_⟩
      · exact fun he => ht.1 ((MulAut.conj g).injective (he.trans (map_one _).symm))
      · rw [← map_pow,ht.2,map_one]
    · refine ⟨?_,?_⟩
      · exact fun he => hu.1 ((MulAut.conj g).injective (he.trans (map_one _).symm))
      · rw [← map_pow,hu.2,map_one]
  · exact (card_map_of_injective (MulAut.conj g).injective).ge

/-- An inverted cubic is normal when all involutions in a faithful binary action
are transvections and the actual Sylow two-subgroup has order two. -/
theorem cubic_normal_of_order_two_sylow_transvections
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ.asGroupHom)
    (S : Sylow 2 G) (hS : Nat.card S = 2)
    (htrans : ∀ {x : G}, IsInvolution x →
      LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom x) ∈
        LinearEquiv.transvections (ZMod 2) V)
    (t c : G) (ht : IsInvolution t) (hc : orderOf c = 3)
    (hinvert : t*c*t⁻¹ = c⁻¹) : (zpowers c).Normal := by
  let u := c*t*c⁻¹
  have hti : t⁻¹ = t := inv_eq_self_of_orderOf_eq_two (orderOf_eq_prime ht.2 ht.1)
  have htt : t*t = 1 := by simpa only [pow_two] using ht.2
  have hc3 : c^3=1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have htu : t*u = c := by
    dsimp [u]
    calc
      _ = (t*c*t⁻¹)*c⁻¹ := by rw [hti]; group
      _ = c⁻¹*c⁻¹ := by rw [hinvert]
      _ = c := by
        apply mul_right_cancel (b := c*c)
        calc
          (c⁻¹*c⁻¹)*(c*c) = 1 := by group
          _ = c*(c*c) := by simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using hc3.symm
  have hu : IsInvolution u := by
    refine ⟨?_,?_⟩
    · intro he
      have hh : t = 1 := by
        have hh := congrArg (fun z => c⁻¹*z*c) he
        simpa only [u,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_left,one_mul,mul_one,inv_mul_cancel] using hh
      exact ht.1 hh
    · change (c*t*c⁻¹)^2=1
      rw [pow_two]
      calc
        _ = c*(t*t)*c⁻¹ := by group
        _ = 1 := by rw [htt]; simp
  have hne : t ≠ u := by
    intro he
    have hh : c=1 := htu.symm.trans (by rw [←he,htt])
    have h13 : 1 = (3 : ℕ) := by simpa only [hh,orderOf_one] using hc
    omega
  have hi := Stellmacher.SectionOne.order_two_sylow_involution_structure S hS
  have hthree : ∀ {x : G}, IsInvolution x → x = t ∨ x = u ∨ x = u⁻¹*t*u :=
    Representation.three_involutions_of_faithful_transvection_representation ρ hρ htrans
    (fun ha hb hab => ⟨hi.1 ha hb hab,(hi.2 ha hb).2⟩) ht hu hne
  have hn := rotation_normal_of_three_involutions t u ht hu hthree
  rwa [htu] at hn
end Subgroup

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
private theorem transvection_conjugate
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (a e : V ≃ₗ[ZMod 2] V) (he : e ∈ LinearEquiv.transvections (ZMod 2) V) :
    a*e*a⁻¹ ∈ LinearEquiv.transvections (ZMod 2) V := by
  rw [LinearEquiv.mem_transvections_iff] at he ⊢
  obtain ⟨f,v,hfv,rfl⟩ := he
  let f' : Module.Dual (ZMod 2) V := f.comp a.symm.toLinearMap
  have hf' : f' (a v) = 0 := by simp [f',hfv]
  refine ⟨f',a v,hf',?_⟩
  apply LinearEquiv.ext
  intro x
  simp [f',LinearMap.transvection.apply]

/-- One actual transvection suffices: the order-two Sylow structure conjugates
every involution to it, before applying the cubic normality argument. -/
theorem cubic_normal_of_order_two_sylow_transvection
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ.asGroupHom)
    (S : Sylow 2 G) (hS : Nat.card S = 2)
    (t c : G) (ht : IsInvolution t) (hc : orderOf c = 3)
    (hinvert : t*c*t⁻¹ = c⁻¹)
    (htrans : LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom t) ∈
      LinearEquiv.transvections (ZMod 2) V) : (zpowers c).Normal := by
  let e : G →* (V ≃ₗ[ZMod 2] V) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp ρ.asGroupHom
  have hall {x : G} (hx : IsInvolution x) :
      LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom x) ∈
        LinearEquiv.transvections (ZMod 2) V := by
    have hp := (Stellmacher.SectionOne.order_two_sylow_involution_structure S hS).2 hx ht
    obtain ⟨g,hg,_⟩ := Glauberman.ZStar.exists_conjugator_of_involutions_mul_odd hx ht hp.2
    change e x ∈ LinearEquiv.transvections (ZMod 2) V
    rw [←hg,map_mul,map_mul,map_inv]
    exact transvection_conjugate (e g) (e t) htrans
  exact cubic_normal_of_order_two_sylow_transvections ρ hρ S hS hall t c ht hc hinvert
end Subgroup
