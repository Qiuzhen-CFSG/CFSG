module
public import Theory.GroupTheory.NormalSymmetricThreeMarked

/-!
# Place the symmetric-three factors in the source normalizer

A Sylow-invariant two-perfect subgroup Y centralizes the cubic residual
of a normal S₃. The residual-containment-or-centralization dichotomy then
places the whole S₃ in N(Y): in the containment case its residual and
Sylow intersection both normalize Y, and these generate S₃.

This keeps the containment branch explicit. Two-perfectness and
normalization alone do not imply pointwise centralization of all of S₃.
The remaining classification argument must establish factor normalization,
using the at-most-two factor bound, before this deduction can be applied
inside the appropriate normalizer.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the S₃
elimination in 15.3.15(2)/26(2), printed pp.1125 and 1130.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.StarSelection
variable {A : Type*} [Group A] [Finite A]

/-- Both branches of the normal symmetric-three dichotomy place the
factor in the normalizer of a Sylow-invariant two-perfect subgroup. -/
theorem symmetricThree_le_normalizer (L : Subgroup A) [L.Normal]
    (e : L ≃* Equiv.Perm (Fin 3)) (S : Sylow 2 A)
    (Y : Subgroup A) (hY : IsPPerfect 2 Y)
    (hS : (S : Subgroup A) ≤ normalizer (Y : Set A)) :
    L ≤ normalizer (Y : Set A) := by
  rcases Theory.GroupTheory.NormalSymmetricThreeMarked.residual_le_or_centralizes
      L e S Y hY hS with hr | hc
  · obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_normal L
    have hgen := congrArg (fun U : Subgroup L => U.map L.subtype)
      (pResidual_sup_sylow_eq_top P)
    rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype,
      hP, subgroupOf_map_subtype] at hgen
    rw [← hgen]
    exact sup_le (hr.trans Y.le_normalizer) (inf_le_left.trans hS)
  · exact (le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _)

/-- An exact source normalizer equality therefore absorbs a normal S₃ factor. -/
theorem symmetricThree_le_of_normalizer_eq (L : Subgroup A) [L.Normal]
    (e : L ≃* Equiv.Perm (Fin 3)) (S : Sylow 2 A)
    (Y M : Subgroup A) (hY : IsPPerfect 2 Y)
    (hSM : (S : Subgroup A) ≤ M) (hN : normalizer (Y : Set A) = M) : L ≤ M := by
  rw [← hN]
  exact symmetricThree_le_normalizer L e S Y hY (hSM.trans_eq hN.symm)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.StarSelection
