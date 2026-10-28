module

public import Theory.Representation.BinaryOffender.FixedMovedComplement
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.Representation.SpecialLinearNatural
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.PGroup


/-!
# Complement of a natural binary plane

For an actual SL₂(2) action whose displacements lie in a natural plane,
the normal cubic subgroup has no nonzero fixed vector on that plane.
Odd-order averaging therefore supplies a fixed complement for the whole
SL₂(2) action. This retains the given action and its natural coordinates.

Source: the natural-factor splitting used in Aschbacher–Smith B.1.8 and
14.1.7, printed pp.70 and 977.
-/

public section

open Subgroup Representation.BinaryOffender
namespace Representation
private theorem binary_cubic_fixed :
    ∀ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
      g ≠ 1 → g ^ 3 = 1 → ∀ v : Fin 2 → ZMod 2,
        g.val.mulVec v = v → v = 0 := by
  decide +kernel

variable {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]

theorem natural_support_complement
    (ρ : Representation (ZMod 2) H V)
    (e : H ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
    (W : Submodule (ZMod 2) V) (f : W ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
    (hf : ∀ g (v : W), ρ g (v : V) = (f.symm (specialLinearNatural 2 (e g) (f v)) : V))
    (hm : ∀ g v, ρ g v - v ∈ W) : IsCompl W (fixedSpace ρ ⊤) := by
  classical
  obtain ⟨eS⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let a := e.trans eS
  let N := (alternatingGroup (Fin 3)).comap a.toMonoidHom
  let : N.Normal := inferInstance
  let : Finite H := Finite.of_equiv _ e.symm.toEquiv
  have hc : Nat.card N = 3 := by
    rw [← card_map_of_injective (f := a.toMonoidHom) a.injective,
      map_comap_eq_self_of_surjective a.surjective]
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have ho : Odd (Nat.card N) := by rw [hc]; decide
  apply isCompl_support_fixed_of_normal_odd ρ N ho W hm
  apply Submodule.disjoint_def.mpr
  intro v hv hn
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := N) 3 (by rw [hc])
  have heord : orderOf (e (z : H)) = 3 := by
    rw [e.orderOf_eq, Subgroup.orderOf_coe, hz]
  have hne : e (z : H) ≠ 1 := by
    intro he
    rw [he, orderOf_one] at heord
    omega
  have hp : e (z : H) ^ 3 = 1 := by
    rw [← heord]
    exact pow_orderOf_eq_one _
  have hfv : specialLinearNatural 2 (e (z : H)) (f ⟨v, hv⟩) = f ⟨v, hv⟩ := by
    apply f.symm.injective
    apply Subtype.val_injective
    rw [← hf, f.symm_apply_apply]
    exact hn z
  have hzv := binary_cubic_fixed (e (z : H)) hne hp (f ⟨v, hv⟩) hfv
  have hzero : (⟨v, hv⟩ : W) = 0 := f.injective (by simpa using hzv)
  exact congrArg Subtype.val hzero

end Representation
