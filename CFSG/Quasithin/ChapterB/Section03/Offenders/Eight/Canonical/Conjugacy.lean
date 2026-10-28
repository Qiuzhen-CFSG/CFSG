module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Defs
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Conjugacy
public import Theory.Representation.BinaryOffender.PermutationConjugacy

/-!
# Conjugacy transport for the canonical offender families

The representation of a conjugating permutation transports fixed spaces. Pulling
back every subgroup of the image proves preservation of the best-offender
condition, including its comparisons with all smaller subgroups.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition B.3.2, printed pp. 83–84.
-/

public section
namespace CFSG.Quasithin.ChapterB.Offenders
open Representation.BinaryOffender

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) (Equiv.Perm (Fin n)) V)
variable {A B : Subgroup (Equiv.Perm (Fin n))}

theorem IsConjugateTo.finrank_fixedSpace_eq (h : IsConjugateTo A B) :
    Module.finrank (ZMod 2) (fixedSpace ρ A) =
      Module.finrank (ZMod 2) (fixedSpace ρ B) := by
  obtain ⟨g, rfl⟩ := h
  exact (fixedSpaceConjEquiv ρ B g).finrank_eq.symm

theorem IsConjugateTo.fixedCodim_eq [FiniteDimensional (ZMod 2) V]
    (h : IsConjugateTo A B) : fixedCodim ρ A = fixedCodim ρ B := by
  obtain ⟨g, rfl⟩ := h
  exact fixedCodim_map_conj ρ B g

theorem IsConjugateTo.weight_eq (h : IsConjugateTo A B) : weight ρ A = weight ρ B := by
  unfold weight
  rw [h.rank_eq, h.finrank_fixedSpace_eq ρ]

theorem IsConjugateTo.isOffender [FiniteDimensional (ZMod 2) V]
    (h : IsConjugateTo A B) (hB : IsOffender ρ B) : IsOffender ρ A := by
  refine ⟨h.isElementaryTwo hB.1, ?_⟩
  rw [h.fixedCodim_eq ρ, h.rank_eq]
  exact hB.2

theorem IsConjugateTo.isStrongOffender [FiniteDimensional (ZMod 2) V]
    (h : IsConjugateTo A B) (hB : IsStrongOffender ρ B) : IsStrongOffender ρ A := by
  refine ⟨h.isElementaryTwo hB.1, ?_⟩
  rw [h.fixedCodim_eq ρ, h.rank_eq]
  exact hB.2

/-- Best-offender transport compares every subgroup, including the trivial one. -/
theorem IsConjugateTo.isBestOffender (h : IsConjugateTo A B)
    (hB : IsBestOffender ρ B) : IsBestOffender ρ A := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨hB.1.map_conj g, ?_⟩
  intro C hC
  let f := (MulAut.conj g).toMonoidHom
  have he : (C.comap f).map f = C :=
    Subgroup.map_comap_eq_self_of_surjective (MulAut.conj g).surjective C
  have hle : C.comap f ≤ B := by
    have hle : C.comap f ≤ (B.map f).comap f := Subgroup.comap_mono hC
    rwa [Subgroup.comap_map_eq_self_of_injective (MulAut.conj g).injective] at hle
  have hconj : IsConjugateTo C (C.comap f) := ⟨g, he.symm⟩
  rw [hconj.weight_eq ρ, (show IsConjugateTo (B.map f) B from ⟨g, rfl⟩).weight_eq ρ]
  exact hB.2 _ hle

end CFSG.Quasithin.ChapterB.Offenders
