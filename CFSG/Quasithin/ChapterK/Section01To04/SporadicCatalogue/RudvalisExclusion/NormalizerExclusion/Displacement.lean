module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.RudvalisExclusion.NormalizerExclusion.Inputs
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.RudvalisExclusion.NormalizerExclusion.Displacement.Certificates
public import Theory.SpecificGroups.Rudvalis.Model.ThreeConjugates.Fusion
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Moved-dimension bounds in the explicit Rudvalis action

Checked invertible minors give lower bounds fourteen for the marked `a`
and twelve for `b²`. The checked permutation-model involution fusion,
transported by the marked comparison, makes the bound twelve universal
and confines any involution of displacement at most twelve to the `b²`
class. No character table or matrix/permutation identification is assumed.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
Ru paragraph, manuscript p.17. In the ATLAS marking `a` is 2B and `b²` is 2A.
-/

public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisExclusion.NormalizerExclusion
open Subgroup Representation.BinaryOffender DisplacementCertificate

private theorem minor_rank_lower {r : ℕ} (M : Matrix (Fin 28) (Fin 28) (ZMod 2))
    (rows cols : Fin r → Fin 28) (R : Matrix (Fin r) (Fin r) (ZMod 2))
    (h : R * M.submatrix rows cols = 1) : r ≤ M.rank := by
  have hl := Matrix.rank_mul_le_right R (M.submatrix rows cols)
  rw [h, Matrix.rank_one, Fintype.card_fin] at hl
  exact hl.trans (Matrix.rank_submatrix_le M rows cols)

private theorem minor_displacement_lower {r : ℕ}
    (M : Matrix (Fin 28) (Fin 28) (ZMod 2)) (rows cols : Fin r → Fin 28)
    (R : Matrix (Fin r) (Fin r) (ZMod 2))
    (h : R * (M - 1).submatrix rows cols = 1) :
    r ≤ Module.finrank (ZMod 2) (LinearMap.range (Matrix.toLin' M - LinearMap.id)) := by
  have he : Matrix.toLin' (M - 1) = Matrix.toLin' M - LinearMap.id := by
    rw [map_sub, Matrix.toLin'_one]
  rw [← he, Matrix.toLin'_apply']
  exact minor_rank_lower (M - 1) rows cols R h

theorem standardA_displacement_lower :
    14 ≤ fixedCodim standardRepresentation (zpowers standardA) := by
  rw [fixedCodim_zpowers_eq_displacement_rank]
  change 14 ≤ Module.finrank (ZMod 2) (LinearMap.range (Matrix.toLin' matrixA - LinearMap.id))
  exact minor_displacement_lower matrixA rowsA colsA inverseA minorA_inverse

theorem standardBSq_displacement_lower :
    12 ≤ fixedCodim standardRepresentation (zpowers (standardB ^ 2)) := by
  rw [fixedCodim_zpowers_eq_displacement_rank]
  have he : standardRepresentation (standardB ^ 2) = Matrix.toLin' matrixBSq := by
    rw [map_pow, pow_two]
    change (Matrix.toLin' matrixB).comp (Matrix.toLin' matrixB) = _
    rw [← Matrix.toLin'_mul, matrixB_sq]
  rw [he]
  exact minor_displacement_lower matrixBSq rowsBSq colsBSq inverseBSq minorBSq_inverse

private theorem fixedCodim_eq_of_isConj {s t : standardGroup} (h : IsConj s t) :
    fixedCodim standardRepresentation (zpowers s) =
      fixedCodim standardRepresentation (zpowers t) := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact (fixedCodim_zpowers_conj standardRepresentation s g).symm

/-- Fusion uses the actual marked comparison, not just the name of the group. -/
theorem involution_fusion (hmodel : StandardComparison) (t : standardGroup)
    (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    IsConj t standardA ∨ IsConj t (standardB ^ 2) := by
  obtain ⟨e, ha, hb⟩ := hmodel
  have ha' : e Rudvalis.a = standardA := Subtype.ext ha
  have hb' : e Rudvalis.b = standardB := Subtype.ext hb
  have hs : (e.symm t) ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have hn : e.symm t ≠ 1 := fun h => ht (by simpa using congrArg e h)
  have hf := Rudvalis.involution_isConj_a_or_b_sq (e.symm t)
    (orderOf_eq_prime hs hn)
  rcases hf with h | h
  · left
    have hh := e.toMonoidHom.map_isConj h
    change IsConj (e (e.symm t)) (e Rudvalis.a) at hh
    rwa [e.apply_symm_apply, ha'] at hh
  · right
    have hh := e.toMonoidHom.map_isConj h
    change IsConj (e (e.symm t)) (e (Rudvalis.b ^ 2)) at hh
    rwa [e.apply_symm_apply, map_pow, hb'] at hh

/-- The exact two displacement consequences consumed by the centralizer argument. -/
theorem involution_displacement (hmodel : StandardComparison) (t : standardGroup)
    (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    12 ≤ fixedCodim standardRepresentation (zpowers t) ∧
      (fixedCodim standardRepresentation (zpowers t) ≤ 12 → IsConj t (standardB ^ 2)) := by
  rcases involution_fusion hmodel t ht ht2 with ha | hb
  · have hd := standardA_displacement_lower
    rw [← fixedCodim_eq_of_isConj ha] at hd
    exact ⟨by omega, fun h => by omega⟩
  · have hd := standardBSq_displacement_lower
    rw [← fixedCodim_eq_of_isConj hb] at hd
    exact ⟨hd, fun _ => hb⟩

end CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisExclusion.NormalizerExclusion
