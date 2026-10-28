module

public import Theory.GroupAction.QuaternionEight

/-!
# Quaternion embeddings and abelian direct factors

The unique involution of Q₈ is a commutator, so every homomorphism to an
abelian group kills it. Every nontrivial subgroup of Q₈ contains that
involution. Hence an embedding into G × A, with A abelian, remains faithful
after projection to G.

This is the elementary direct-product step in the quaternion-centralizer
calculation used in Aschbacher–Smith 16.4.9(2), printed p.1192.
-/

public section
open Subgroup
namespace QuaternionGroup
variable {G A : Type*} [Group G] [CommGroup A]

/-- Every abelian image kills the quaternion involution. -/
theorem map_a_two_eq_one (f : QuaternionGroup 2 →* A) : f (a 2) = 1 := by
  have he : (a 2 : QuaternionGroup 2) = a 1 * xa 0 * (a 1)⁻¹ * (xa 0)⁻¹ := by decide
  rw [he, map_mul, map_mul, map_mul, map_inv, map_inv]
  rw [mul_right_comm (f (a 1)) (f (xa 0)), mul_inv_cancel, one_mul, mul_inv_cancel]

/-- An abelian direct factor cannot make a nonfaithful Q₈ representation faithful. -/
theorem injective_fst_of_injective_prod (f : QuaternionGroup 2 →* G × A)
    (hf : Function.Injective f) : Function.Injective ((MonoidHom.fst G A).comp f) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  by_contra hk
  have hfst : (f (a 2)).1 = 1 := a_two_mem_of_ne_bot _ hk
  have hsnd : (f (a 2)).2 = 1 := map_a_two_eq_one ((MonoidHom.snd G A).comp f)
  have he : (a 2 : QuaternionGroup 2) = 1 := hf ((Prod.ext hfst hsnd).trans f.map_one.symm)
  exact (by decide : (a 2 : QuaternionGroup 2) ≠ 1) he

end QuaternionGroup
