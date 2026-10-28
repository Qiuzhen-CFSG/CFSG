module

public import Theory.Representation.BinaryPermutation
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Theory.ElementaryAbelian.Basic
public import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic

/-!
# Automorphisms of the binary even-weight plane

The permutation action on the three coordinates realizes all six automorphisms
of the four-group. Faithfulness is checked on the eight binary vectors; the
Klein-four automorphism count then gives the equivalence. The literal action
formula supplies compatible coordinates for the binary natural-module input
in Aschbacher–Smith G.2.3.
-/

@[expose] public section

namespace BinaryPlane
abbrev Plane := Multiplicative (BinaryPermutation.core (Fin 3))

def aut (p : Equiv.Perm (Fin 3)) : MulAut Plane where
  toFun v := Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 3) p v.toAdd)
  invFun v := Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 3) p⁻¹ v.toAdd)
  left_inv v := by
    change BinaryPermutation.coreRepresentation (Fin 3) p⁻¹
      (BinaryPermutation.coreRepresentation (Fin 3) p v.toAdd) = v.toAdd
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  right_inv v := by
    change BinaryPermutation.coreRepresentation (Fin 3) p
      (BinaryPermutation.coreRepresentation (Fin 3) p⁻¹ v.toAdd) = v.toAdd
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  map_mul' v w := by
    exact LinearMap.map_add (BinaryPermutation.coreRepresentation (Fin 3) p) _ _

def action : Equiv.Perm (Fin 3) →* MulAut Plane where
  toFun := aut
  map_one' := by
    apply MulEquiv.ext
    intro v
    exact congrArg (fun f => f v.toAdd) (map_one (BinaryPermutation.coreRepresentation (Fin 3)))
  map_mul' p q := by
    apply MulEquiv.ext
    intro v
    exact congrArg (fun f => f v.toAdd) (map_mul (BinaryPermutation.coreRepresentation (Fin 3)) p q)

private theorem faithful_raw : ∀ p : Equiv.Perm (Fin 3),
    (∀ v : Fin 3 → ZMod 2, (∑ i, v i) = 0 → ∀ i, v (p⁻¹ i) = v i) → p = 1 := by
  decide +kernel

theorem injective_action : Function.Injective action := by
  apply (MonoidHom.ker_eq_bot_iff action).mp
  apply le_bot_iff.mp
  intro p hp
  apply faithful_raw p
  intro v hv i
  have he := congrArg (fun f : MulAut Plane => f (Multiplicative.ofAdd ⟨v,hv⟩)) hp
  exact congrArg (fun w : Plane => w.toAdd.val i) he

instance : IsElementaryAbelian 2 Plane where
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    intro v
    change (2 : ℕ) • v.toAdd = 0
    simp only [← Nat.cast_smul_eq_nsmul (ZMod 2), CharP.cast_eq_zero, zero_smul])

theorem card_plane : Nat.card Plane = 4 := by
  change Nat.card (BinaryPermutation.core (Fin 3)) = 4
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), BinaryPermutation.finrank_core]
  norm_num [Nat.card_eq_fintype_card]

instance : IsKleinFour Plane where
  card_four := card_plane
  exponent_two := by
    let : Nontrivial Plane := (Finite.one_lt_card_iff_nontrivial).mp (by rw [card_plane]; decide)
    exact IsElementaryAbelian.exponent_eq_prime

noncomputable def equiv : Equiv.Perm (Fin 3) ≃* MulAut Plane :=
  MulEquiv.ofBijective action ⟨injective_action,
    (Nat.bijective_iff_injective_and_card action).mpr ⟨injective_action, by
      rw [IsKleinFour.card_mulAut]
      simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]⟩ |>.2⟩

end BinaryPlane
