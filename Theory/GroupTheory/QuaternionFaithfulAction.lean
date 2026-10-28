module
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.OrderOfElement
/-!
# Faithfulness detected by the quaternion involution

Every nonidentity element of Q₈ is its unique involution or squares to that
involution. Thus a homomorphism detecting the involution is faithful.
This supplies the quaternion action step in Aschbacher--Smith J.3.6.
-/

public section
namespace MonoidHom

/-- Detecting the unique quaternion involution detects the entire kernel. -/
theorem injective_of_quaternion_involution
    {Q A : Type*} [Group Q] [Group A] (f : Q →* A)
    (e : Q ≃* QuaternionGroup 2) (z : Q) (hz : orderOf z=2) (hfz : f z≠1) :
    Function.Injective f := by
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply bot_unique
  intro x hx
  apply Subgroup.mem_bot.mpr
  by_contra hn
  have hfinite : ∀ a b : QuaternionGroup 2, b^2=1 ∧ b≠1 → a≠1 → a=b ∨ a^2=b := by
    decide +kernel
  have he := hfinite (e x) (e z)
    ⟨by rw [← map_pow,(orderOf_eq_prime_iff.mp hz).1,map_one],
     fun hh => (orderOf_eq_prime_iff.mp hz).2 (e.injective (hh.trans (map_one e).symm))⟩
    (fun hh => hn (e.injective (hh.trans (map_one e).symm)))
  rcases he with he | he
  · exact hfz (e.injective he ▸ hx)
  · have hh : x^2=z := e.injective ((map_pow e x 2).trans he)
    exact hfz (by rw [← hh,map_pow,(show f x=1 from hx),one_pow])

end MonoidHom
