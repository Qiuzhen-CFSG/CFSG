module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.ActionTransport
public import Theory.Representation.BinaryPermutationMulAction

/-!
Relabel the natural eight-letter action without changing its ambient module
or kernel. Simultaneous conjugation of the permutation actor and the deleted
permutation coordinates preserves compatibility. This permits the actual
Sylow subgroup in [AS, 15.3.25] to use the fixed model coordinates.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.NaturalEightAction
variable {G : Type*} [Group G] {I U : Subgroup G} (a : NaturalEightAction I U)

def relabel (r : Equiv.Perm (Fin 8)) : NaturalEightAction I U where
  normalizes := a.normalizes
  coordinates := a.coordinates.trans (BinaryPermutation.naturalMulAction (Fin 8) r)
  actor := (MulAut.conj r).toMonoidHom.comp a.actor
  onto := (MulAut.conj r).surjective.comp a.onto
  compatible := by
    intro i u
    change BinaryPermutation.naturalMulAction (Fin 8) r
        (a.coordinates (U.normalizerMonoidHom ⟨i,a.normalizes i.property⟩ u)) =
      BinaryPermutation.naturalMulAction (Fin 8) (r * a.actor i * r⁻¹)
        (BinaryPermutation.naturalMulAction (Fin 8) r (a.coordinates u))
    rw [a.compatible]
    change BinaryPermutation.naturalMulAction (Fin 8) r
        (BinaryPermutation.naturalMulAction (Fin 8) (a.actor i) (a.coordinates u)) = _
    simp only [map_mul, map_inv, MulAut.mul_apply]
    congr 2
    exact (MulEquiv.symm_apply_apply (BinaryPermutation.naturalMulAction (Fin 8) r) _).symm

@[simp] theorem relabel_actor (r : Equiv.Perm (Fin 8)) (i : I) :
    (a.relabel r).actor i = r * a.actor i * r⁻¹ := by rfl

theorem relabel_kernel (r : Equiv.Perm (Fin 8)) : (a.relabel r).actor.ker = a.actor.ker := by
  ext i
  change r * a.actor i * r⁻¹ = 1 ↔ a.actor i = 1
  rw [mul_inv_eq_one, mul_eq_left]

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.NaturalEightAction
