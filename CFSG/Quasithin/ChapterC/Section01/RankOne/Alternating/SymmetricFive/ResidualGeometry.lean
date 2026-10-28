module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Geometry
import Mathlib.Tactic


/-!
# The residual conjugator and codimension for the S₅ branch

The alternating fixed space is zero, as the three-cycle class sum is both
the identity on the core and zero on fixed vectors. Thus its fixed codimension
is four. An even five-cycle joins two transposition four-groups to S₅, and
conjugating the entire marking preserves this generation statement.

Source: Aschbacher–Smith, B.2.18 and the S₅ case of E.2.3, pp.81 and 216–217.
-/

public section

namespace CFSG.Quasithin.ChapterC.SymmetricFive
open BinaryPermutation Representation.BinaryOffender ChapterB.Offenders Subgroup Equiv
open BinaryPermutation.FiveCentralExtension

theorem fixedSpace_alternating_eq_bot :
    fixedSpace (coreRepresentation (Fin 5)) (alternatingGroup (Fin 5)) = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  change v = 0
  have h : ∑ g ∈ cubes, coreRepresentation (Fin 5) g v = ∑ _g ∈ cubes, v := by
    apply Finset.sum_congr rfl
    intro g hg
    exact hv ⟨g, cubes_even g hg⟩
  rw [core_sum, Finset.sum_const, cubes_card] at h
  have hz : 20 • v = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (R := ZMod 2)]
    change (20 : ZMod 2) • v = 0
    rw [show (20 : ZMod 2) = 0 from rfl, zero_smul]
  exact h.trans hz

theorem fixedCodim_alternating :
    fixedCodim (coreRepresentation (Fin 5)) (alternatingGroup (Fin 5)) = 4 := by
  have h := fixedCodim_add_finrank (coreRepresentation (Fin 5)) (alternatingGroup (Fin 5))
  rw [fixedSpace_alternating_eq_bot, finrank_bot, add_zero] at h
  exact h.trans (by simpa using BinaryPermutation.finrank_core (Fin 5))

theorem conjugate_fiveCycle_even (a : Sym) : a * fiveCycle * a⁻¹ ∈ alternatingGroup (Fin 5) := by
  have hs := Perm.mem_alternatingGroup.mp fiveCycle_even
  rw [Perm.mem_alternatingGroup, map_mul, map_mul, map_inv, hs, mul_one, mul_inv_cancel]

theorem two_conjugate_four_groups_generate (a : Sym) :
    (D 5).map (MulAut.conj a).toMonoidHom ⊔
      ((D 5).map (MulAut.conj a).toMonoidHom).map
        (MulAut.conj (a * fiveCycle * a⁻¹)).toMonoidHom = ⊤ := by
  have hc : ((D 5).map (MulAut.conj a).toMonoidHom).map
      (MulAut.conj (a * fiveCycle * a⁻¹)).toMonoidHom =
      ((D 5).map (MulAut.conj fiveCycle).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
    rw [map_map, map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [hc, ← Subgroup.map_sup, two_four_groups_generate,
    map_top_of_surjective _ (MulAut.conj a).surjective]
end CFSG.Quasithin.ChapterC.SymmetricFive
