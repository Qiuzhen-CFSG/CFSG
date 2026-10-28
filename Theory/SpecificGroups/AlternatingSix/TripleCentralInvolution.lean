module
public import Theory.Alternating.OddCentralCovers
public import Theory.Alternating.TripleSixActorInversion
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner
public import Theory.GroupTheory.PPerfectHom

/-!
# Center-fixing involutions of the triple cover of A₆

Schur uniqueness identifies an arbitrary central triple cover with the
actual even hexacode group. Every noninner involution inverts its cubic
center, so an involution fixing that center is inner. Its image on the
central quotient has automorphism centralizer of order 32. Faithfulness
of the perfect central-quotient action therefore makes the original
automorphism centralizer a two-group.

Source: GLS3 5.2.3 and 5.2.7; Aschbacher--Smith, proof of 12.6.26,
printed p.832. The center-fixation premise is discharged at the original
selected component in Chapter12.Section06.NaturalSource.ComponentSix.
-/

public section
open Subgroup Theory.GroupTheory
namespace AlternatingSix.TripleCentralInvolution
variable {B : Type*} [Group B] [Finite B] [IsQuasisimple B]

/-- An involution fixing the actual cubic covering center is inner. -/
theorem inner_of_fixes_center
    (e : B ⧸ center B ≃* alternatingGroup (Fin 6))
    (hc : Nat.card (center B) = 3) (a : MulAut B) (ha : a ^ 2 = 1)
    (hfix : ∀ z ∈ center B, a z = z) : ∃ b : B, a = MulAut.conj b := by
  classical
  by_contra! hout
  obtain ⟨j⟩ := GLS3.Chapter5.OddCentralCovers.triple_six_equiv_hexacode e hc
  let x := MulAut.congr j a
  have hx : x ^ 2 = 1 := by
    change MulAut.congr j a ^ 2 = 1
    rw [←map_pow,ha,map_one]
  have hxo : ∀ b : Atlas.Codes.HexEvenAutomorphisms, x ≠ MulAut.conj b := by
    intro b hb
    apply hout (j.symm b)
    apply (MulAut.congr j).injective
    rw [MulAut.congr_conj,j.apply_symm_apply]
    exact hb
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := center B) 3 (by rw [hc])
  have hi := GLS3.Chapter5.TripleSixActorInversion.hexEven_center_inverted x hx hxo
    (j z) ((centerCongr j z).property)
  have hi' : a z = (z : B)⁻¹ := j.injective (by
    simpa only [x,MulAut.congr_apply,MulEquiv.trans_apply,j.symm_apply_apply,map_inv] using hi)
  rw [hfix z z.property] at hi'
  have hz2 : z ^ 2 = 1 := Subtype.ext (by
    rw [pow_two]
    exact inv_eq_iff_mul_eq_one.mp hi'.symm)
  have hd := orderOf_dvd_of_pow_eq_one hz2
  rw [hz] at hd
  omega

/-- The full automorphism centralizer of such an involution is a two-group. -/
theorem centralizer_isTwoGroup_of_fixes_center
    (e : B ⧸ center B ≃* alternatingGroup (Fin 6))
    (hc : Nat.card (center B) = 3) (a : MulAut B) (ha : orderOf a = 2)
    (hfix : ∀ z ∈ center B, a z = z) :
    IsPGroup 2 (centralizer ({a} : Set (MulAut B))) := by
  obtain ⟨b,hb⟩ := inner_of_fixes_center e hc a (ha ▸ pow_orderOf_eq_one a) hfix
  let q := MulAut.centralQuotientAction e
  let t := e (QuotientGroup.mk' (center B) b)
  have hqa : q a = MulAut.conj t := by rw [hb,MulAut.centralQuotientAction_conj]
  have ht : orderOf t = 2 := by
    have hh : orderOf (MulAut.conj t) = 2 := by
      rw [←hqa,orderOf_injective q (MulAut.centralQuotientAction_injective e),ha]
    rwa [orderOf_injective MulAut.conj AlternatingSix.ShadowLocal.inner_injective] at hh
  have hp : IsPGroup 2 (centralizer ({q a} : Set (MulAut (alternatingGroup (Fin 6))))) := by
    rw [hqa]
    exact IsPGroup.of_card (n := 5)
      (AlternatingSix.ShadowLocal.inner_involution_centralizer_card t ht)
  let f : centralizer ({a} : Set (MulAut B)) →*
      centralizer ({q a} : Set (MulAut (alternatingGroup (Fin 6)))) :=
    (q.comp (centralizer ({a} : Set (MulAut B))).subtype).codRestrict _ (by
      intro x
      apply mem_centralizer_singleton_iff.mpr
      change q x.val * q a = q a * q x.val
      simpa only [MonoidHom.comp_apply,map_mul] using congrArg q (mem_centralizer_singleton_iff.mp x.property))
  exact hp.of_injective f (fun x y he => Subtype.ext
    (MulAut.centralQuotientAction_injective e (congrArg Subtype.val he)))

end AlternatingSix.TripleCentralInvolution
