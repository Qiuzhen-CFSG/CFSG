module
public import Theory.SpecificGroups.Alternating.FiveSylowRadical
-- Internal proof split: publish the conjugation equation for the existing
-- automorphism marking while keeping its implementation opaque to clients.
import all Theory.SpecificGroups.Alternating.FiveExtensionAction

/-!
# Cubic centralizers in an A₅ Sylow stabilizer

The five-letter action of an A₅ Sylow stabilizer fixes a point. An odd
permutation on the remaining four letters cannot centralize a nontrivial
cubic permutation. The finite certificate checks only that four-letter
stabilizer; conjugation transports its result to any chosen point.

This supplies the quotient-action step in Aschbacher--Smith 13.2.7,
printed p.884. The conjugation equation below is an intentional internal
extension of the existing automorphism marking, without exposing its body.
-/

public section
namespace Theory.SpecificGroups.Alternating
/-- The existing automorphism marking sends each permutation to its
literal conjugation action. -/
theorem symmetricAutEquiv_conjNormal (t : Equiv.Perm (Fin 5)) :
    FiveExtensionAction.symmetricAutEquiv t = MulAut.conjNormal t := by rfl

private theorem cubic_odd_fixed_check :
    ∀ (d t : {g : Equiv.Perm (Fin 5) // g 4 = 4}),
      d.val ^ 3 = 1 → t.val.sign ≠ 1 → d.val * t.val = t.val * d.val → d.val = 1 := by
  decide +kernel

theorem cubic_eq_one_of_commutes_odd_fixed
    (i : Fin 5) (d t : Equiv.Perm (Fin 5)) (hd : d i = i) (ht : t i = i)
    (hd3 : d ^ 3 = 1) (htodd : t.sign ≠ 1) (hcomm : d * t = t * d) : d = 1 := by
  let s : Equiv.Perm (Fin 5) := Equiv.swap i 4
  let e := MulAut.conj s
  have hdf : e d 4 = 4 := by
    change s (d (s⁻¹ 4)) = 4
    simp only [s,Equiv.swap_inv,Equiv.swap_apply_right,hd,Equiv.swap_apply_left]
  have htf : e t 4 = 4 := by
    change s (t (s⁻¹ 4)) = 4
    simp only [s,Equiv.swap_inv,Equiv.swap_apply_right,ht,Equiv.swap_apply_left]
  have hpow : e d ^ 3 = 1 := by rw [←map_pow,hd3,map_one]
  have hodd : (e t).sign ≠ 1 := by
    simpa [e,MulAut.conj_apply,mul_comm,mul_left_comm,mul_assoc] using htodd
  have hc : e d * e t = e t * e d := by rw [←map_mul,←map_mul,hcomm]
  exact e.injective ((cubic_odd_fixed_check ⟨e d,hdf⟩ ⟨e t,htf⟩ hpow hodd hc).trans e.map_one.symm)
end Theory.SpecificGroups.Alternating
