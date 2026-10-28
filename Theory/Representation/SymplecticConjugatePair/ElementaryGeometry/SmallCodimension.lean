module

public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.NaturalRatioBounds

/-!
# Elementary symplectic actors of small fixed codimension

An elementary two-subgroup on the natural Sp₄(2ⁿ) module with fixed
codimension below 2n lies, after conjugation, in a transvection root.
Its rank is therefore at most n. The point-radical alternative has
codimension at least 2n; in the plane radical, a larger fixed space
forces the subgroup into a root.

This is the natural-module estimate used in the top-extension case of
Aschbacher–Smith B.5.13, printed pp.110–112.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour

namespace SymplecticConjugatePair.NaturalBounds
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- Below twice the field degree, natural fixed codimension forces root rank. -/
theorem natural_small_codim_rank_le {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0 < n)
    {A : Subgroup (Sp F)} (hA : IsElementaryTwo A)
    (hc : fixedCodim binaryNatural A < 2*n) : rank A ≤ n := by
  let := hA.2
  obtain ⟨g, hg⟩ := elementary_conjugate_radical hF hn A
  let B := A.map (MulAut.conj g).toMonoidHom
  have hBc : fixedCodim (binaryNatural (F := F)) B < 2*n := by
    simpa only [B, fixedCodim_map_conj] using hc
  have hplane : B ≤ planeRadical := by
    rcases hg with hp | hp
    · by_contra hnp
      exact (not_lt_of_ge (point_outside_plane_fixedCodim hF hp hnp)) hBc
    · exact hp
  have hne : fixedSpace (binaryNatural (F := F)) B ≠ (plane F).restrictScalars (ZMod 2) := by
    intro he
    have hd := fixedCodim_add_finrank (binaryNatural (F := F)) B
    rw [he, finrank_binary_plane hF, finrank_vector hF] at hd
    omega
  obtain ⟨R, hR, hBR⟩ := exists_sylowTransvectionRoot_of_fixedSpace_ne hplane hne
  have hr := hR.rank_le hF hBR
  simpa only [B, rank_map_conj] using hr
end SymplecticConjugatePair.NaturalBounds
