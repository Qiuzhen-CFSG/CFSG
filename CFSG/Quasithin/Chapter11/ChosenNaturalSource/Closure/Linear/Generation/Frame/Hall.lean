module

public import Theory.GroupTheory.Hall.Conjugacy
public import Theory.GroupTheory.Hall.OddNormalProducts

/-!
# Correcting a lift by solvable Hall conjugacy

If an odd Hall subgroup and its conjugate lie in the same solvable subgroup,
Hall conjugacy supplies a correction whose product with the original element
normalizes the Hall subgroup. No constraint on the correction's quotient image
is asserted here; `Lift` cancels that image using the original Cartan.
Source: Aschbacher–Smith 11.5.7, printed p.781.
-/

open Subgroup
open Subgroup.OddHall
open scoped Pointwise
public section

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Frame

variable {L : Type*} [Group L] [Finite L]

omit [Finite L] in
private theorem map_conj_mul (Y : Subgroup L) (u v : L) :
    Y.map (MulAut.conj (u * v)).toMonoidHom =
      (Y.map (MulAut.conj v).toMonoidHom).map (MulAut.conj u).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    mul_inv_rev, mul_assoc]

/-- Hall conjugacy corrects the lift by an element of the common solvable
overgroup of the two odd Hall subgroups. -/
theorem exists_normalizer_correction
    {N X : Subgroup L} {a : L}
    (hsolv : Group.IsSolvable N)
    (hX : X ≤ N)
    (hXa : X.map (MulAut.conj a).toMonoidHom ≤ N)
    (hHall : IsHallSubgroup oddPrimes (X.subgroupOf N))
    (hHallXa : IsHallSubgroup oddPrimes
      ((X.map (MulAut.conj a).toMonoidHom).subgroupOf N)) :
    ∃ c : N, (c : L)⁻¹ * a ∈ normalizer (X : Set L) := by
  obtain ⟨c, hc⟩ := exists_conj_eq_of_isHallSubgroup_of_solvable
    hsolv hHall hHallXa
  have hc' : X.map (MulAut.conj a).toMonoidHom =
      X.map (MulAut.conj (c : L)).toMonoidHom := by
    have hh := congrArg (Subgroup.map N.subtype) hc
    simpa only [map_subgroupOf_eq_of_le hXa,
      map_subgroupOf_map_conj_eq hX] using hh
  refine ⟨c, ?_⟩
  apply mem_normalizer_iff_map_conj_eq.mpr
  change X.map (MulAut.conj ((c : L)⁻¹ * a)).toMonoidHom = X
  rw [map_conj_mul, hc', ← map_conj_mul, inv_mul_cancel, map_one]
  exact Subgroup.map_id X

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Frame

