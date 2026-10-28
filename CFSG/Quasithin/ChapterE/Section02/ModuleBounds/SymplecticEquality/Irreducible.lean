module
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.PrimeActors
public import CFSG.Quasithin.ChapterE.Section02.TwoConjugateCovers.SymplecticFour
public import Theory.Representation.SymplecticFour.CoreQuotientDegree
public import Theory.GroupAction.NormalPChiefSeries.FullDimension

/-!
# Irreducibility of the original symplectic core in the equality range

A noncentral chief factor of P/Z has degree at least 4m. If the original
actor has rank at most 2m, the entire P/Z has dimension at most 4m.
The factor therefore has the full dimension and its actual projection
is an equivariant isomorphism. This proves irreducibility of the original
conjugation action; it is not an assumed module-classification premise.

Source: Aschbacher–Smith E.2.15, printed p.228.
-/

public section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement Theory.SpecificGroups.SymplecticFour
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
variable {X F : Type*} [Group X] [Finite X] [Field F] [Finite F] [CharP F 2]
  {T : Sylow 2 X} {V M : Subgroup X} {g : X}

theorem symplectic_four_core_action_irreducible_of_rank_le
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : generalizedFitting X = pCore 2 X)
    (m : ℕ) (hm : 2 ≤ m) (hcard : Nat.card F = 2^m)
    (ξ : (X ⧸ J M) ≃* Sp F)
    (hrank : Nat.log 2 ((Z V g).relIndex (A V M g)) ≤ 2*m) :
    letI := h.Z_normal
    letI := h.core_geometry.1
    let q := QuotientGroup.mk' (Z V g)
    letI := h.quotient_direct_sum.1
    (normalRepresentation ((P V M g).map q)).IsIrreducible := by
  let := h.Z_normal
  let := h.core_geometry.1
  let q := QuotientGroup.mk' (Z V g)
  let U := (P V M g).map q
  let := h.quotient_direct_sum.1
  obtain ⟨s⟩ := SeriesOn.exists_series U
  obtain ⟨i,hi⟩ := h.quotient_core_noncentral_chief_exists hproper hfit s
  have hd := s.noncentral_factor_finrank_ge_symplectic_four
    (h.quotient_core_equiv_symplectic_four m hm hcard ξ) i hi m hm hcard
  have hu := h.quotient_core_finrank_eq_twice_actor
  have hle := (LinearMap.finrank_le_finrank_of_surjective
    (s.factorProjection_surjective i)).trans (Submodule.finrank_le _)
  apply s.normalRepresentation_irreducible_of_factor_full_dimension i
  dsimp only [U,q] at hle hd ⊢
  omega
end CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
