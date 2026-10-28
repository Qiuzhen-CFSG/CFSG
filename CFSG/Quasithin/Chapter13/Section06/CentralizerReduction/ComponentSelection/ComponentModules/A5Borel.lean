module

public import Theory.Representation.BinaryAlternatingFiveBorel
public import Theory.Representation.BinaryOffender.IrreducibleMovedGeneration
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules

/-!
# The concrete Borel-module contradiction in 13.6.15

The five-point calculation is connected to the chapter's literal subspace
commutator and fixed-space conventions. The endpoint applies to [W_K,D]
and its submodule [V,D], with D = L_v in the source: a surjective Borel
projection and equivariant coordinates force [V,D] to have rank other than two.

The chapter owner must construct that projection, the coordinates and the
commutator inclusion. This module proves the module calculation and its
application; it does not assert the complete exclusion of the A₅ constituent.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
1 March 2004 manuscript, proof of Lemma 13.6.15, printed p.930.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.A5Borel

open Representation Representation.BinaryOffender
open BinaryPermutation BinaryPermutation.AlternatingFiveBorel

/-- [I,B] in the chapter's subspace commutator convention. -/
theorem source_commutator :
    subspaceCommutator (alternatingCoreRepresentation (Fin 5)) ⊤ B = moved := by
  rw [← commutator_eq_moved]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, v, _, rfl⟩
    exact Coinvariants.sub_mem_ker (ρ := action) ⟨g, hg⟩ v
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, v⟩, rfl⟩
    exact Submodule.subset_span ⟨g.val, g.property, v, Submodule.mem_top, rfl⟩

/-- C_I(B) in the chapter's fixed-space convention. -/
theorem source_fixed_line :
    fixedSpace (alternatingCoreRepresentation (Fin 5)) B =
      Submodule.span (ZMod 2) {fixedVector} := fixed_eq_line

variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]

/-- The literal D-action on [W_K,D], with invariance proved from commutators. -/
abbrev commutatorRepresentation (ρ : Representation (ZMod 2) H W)
    (WK : Submodule (ZMod 2) W) (D : Subgroup H) :
    Representation (ZMod 2) D (subspaceCommutator ρ WK D) :=
  (invariantSubspace ρ D _ (subspaceCommutator_invariant ρ WK D)).toRepresentation

/-- The final module contradiction used with D = L_v. The source's earlier
steps supply the genuine surjective Borel projection, coordinates on
[W_K,L_v], and [V,L_v] ≤ [W_K,L_v]. -/
theorem source_commutator_rank_ne_two (ρ : Representation (ZMod 2) H W)
    (WK V : Submodule (ZMod 2) W) (D : Subgroup H)
    (hinclude : subspaceCommutator ρ V D ≤ subspaceCommutator ρ WK D)
    (q : D →* B) (hq : Function.Surjective q)
    (e : subspaceCommutator ρ WK D ≃ₗ[ZMod 2] moved)
    (he : ∀ d w, e (commutatorRepresentation ρ WK D d w) =
      movedRepresentation (q d) (e w)) :
    Module.finrank (ZMod 2) (subspaceCommutator ρ V D) ≠ 2 := by
  let P := (subspaceCommutator ρ V D).comap (subspaceCommutator ρ WK D).subtype
  have hP : ∀ d w, w ∈ P → commutatorRepresentation ρ WK D d w ∈ P := by
    intro d w hw
    exact (subspaceCommutator_invariant ρ V D d.property w.val).2 hw
  have h := no_invariant_plane_of_surjective (commutatorRepresentation ρ WK D)
    q hq e he P hP
  have hd := (Submodule.comapSubtypeEquivOfLe hinclude).finrank_eq
  exact hd ▸ h

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.A5Borel
