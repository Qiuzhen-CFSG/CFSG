module

public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation
public import Theory.GroupTheory.PResidual.NormalizerCore

/-!
# The two-core of the two-residual of S₄

Every element of the Klein four core of S₄ is a product of two elements
whose cubes are one. Such elements belong to the two-residual. Thus the
core lies in that residual, and relative normality identifies their cores.
The finite calculation has only 24 permutations; no subgroup enumeration
or residual computation is used.

Application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), F.6.18(6), printed p.309, and the
terminal marked-amalgam exclusions on printed p.1155.
-/

public section
open Subgroup

namespace Theory.SpecificGroups.SymmetricFour

/-- The Klein four core is contained in the two-residual of S₄. -/
theorem twoCore_le_twoResidual :
    pCore 2 (Equiv.Perm (Fin 4)) ≤ pResidual 2 (Equiv.Perm (Fin 4)) := by
  rw [← SymmetricSix.DuadCalculation.core_eq]
  have hc : ∀ x ∈ SymmetricSix.DuadCalculation.core,
      ∃ a b : Equiv.Perm (Fin 4), a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a * b = x := by
    decide +kernel
  intro x hx
  obtain ⟨a, b, ha, hb, rfl⟩ := hc x hx
  apply (pResidual 2 (Equiv.Perm (Fin 4))).mul_mem
  · exact mem_pResidual_of_orderOf_coprime
      ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one ha))
  · exact mem_pResidual_of_orderOf_coprime
      ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hb))

/-- Core absorption transports through an actual local-group equivalence. -/
theorem twoCore_le_twoResidual_of_equiv {G : Type*} [Group G]
    (e : G ≃* Equiv.Perm (Fin 4)) : pCore 2 G ≤ pResidual 2 G := by
  apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
  rw [pCore_map_iso, map_pResidual]
  exact twoCore_le_twoResidual

/-- In any ambient group, a local S₄ and its embedded two-residual have
the same embedded two-core. This is a derived equality, not a marking premise. -/
theorem embedded_residual_twoCore {G : Type*} [Group G] (P : Subgroup G)
    (e : P ≃* Equiv.Perm (Fin 4)) :
    ((pResidual 2 P).map P.subtype).pCoreIn 2 = P.pCoreIn 2 :=
  pCoreIn_embedded_pResidual_eq_of_core_le 2 P
    (map_mono (twoCore_le_twoResidual_of_equiv e))

end Theory.SpecificGroups.SymmetricFour
