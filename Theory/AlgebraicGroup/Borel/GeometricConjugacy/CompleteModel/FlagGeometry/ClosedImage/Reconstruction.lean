module

public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagGeometry.ClosedImage.Annihilator

/-!
# Reconstructing full flags from exterior lines

A finite increasing family of proper subspaces of the prescribed dimensions
extends to the exact natural-indexed `FullFlag`, by a constant top tail. This
works when the proper index set is empty as well.

We prove that a tuple lies in the actual Plücker image if and only if its
individual lines are Plücker lines and the simultaneous-annihilator rank
conditions hold. The reverse direction uses the annihilators themselves as
the recovered subspaces. The comparison is transported through the actual
ambient-product point equivalence for arbitrary coordinate bases.

This is the point-reconstruction step in the closed incidence construction
used in Borel, *Linear Algebraic Groups*, §11.1. Decomposability from rank
conditions and closedness of the determinantal locus remain separate results.
-/

@[expose] public noncomputable section

open scoped ExteriorAlgebra LinearAlgebra.Projectivization

namespace Theory.AlgebraicGroup.BorelGeometricConjugacy.FlagGeometry

universe u v
variable {k : Type u} [Field k] {V : Type v}
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Extend the proper terms of a flag by the constant top tail. This also
constructs the unique full flag on a zero-dimensional vector space. -/
def fullFlagOfFiniteChain
    (W : Fin (Module.finrank k V) → Submodule k V)
    (hmono : Monotone W) (hrank : ∀ i, Module.finrank k (W i) = (i : ℕ)) :
    FullFlag k V where
  subspace i := if hi : i < Module.finrank k V then W ⟨i, hi⟩ else ⊤
  monotone := by
    intro i j hij
    dsimp only
    split_ifs with hi hj hj
    · exact hmono (show (⟨i, hi⟩ : Fin (Module.finrank k V)) ≤ ⟨j, hj⟩ from hij)
    · exact le_top
    · omega
    · exact le_rfl
  finrank_eq i := by
    by_cases hi : i < Module.finrank k V
    · have hs : (if hi : i < Module.finrank k V then W ⟨i, hi⟩ else ⊤) = W ⟨i, hi⟩ :=
        dif_pos hi
      exact (congrArg (fun S : Submodule k V => Module.finrank k S) hs).trans
        ((hrank ⟨i, hi⟩).trans (min_eq_left (Nat.le_of_lt hi)).symm)
    · have hs : (if hi : i < Module.finrank k V then W ⟨i, hi⟩ else ⊤) = ⊤ := dif_neg hi
      exact (congrArg (fun S : Submodule k V => Module.finrank k S) hs).trans
        ((finrank_top k V).trans (min_eq_right (Nat.le_of_not_gt hi)).symm)

@[simp] theorem fullFlagOfFiniteChain_subspace
    (W : Fin (Module.finrank k V) → Submodule k V)
    (hmono : Monotone W) (hrank : ∀ i, Module.finrank k (W i) = (i : ℕ))
    (i : Fin (Module.finrank k V)) :
    (fullFlagOfFiniteChain W hmono hrank).subspace i = W i := by
  simp [fullFlagOfFiniteChain, i.isLt]

@[simp] theorem flagPlucker_fullFlagOfFiniteChain
    (W : Fin (Module.finrank k V) → Submodule k V)
    (hmono : Monotone W) (hrank : ∀ i, Module.finrank k (W i) = (i : ℕ))
    (i : Fin (Module.finrank k V)) :
    flagPlucker (fullFlagOfFiniteChain W hmono hrank) i =
      subspacePlucker i (W i) (hrank i) := by
  apply Projectivization.submodule_injective
  simp only [flagPlucker, subspacePlucker_submodule, fullFlagOfFiniteChain_subspace]

/-- Genuine full flags satisfy every simultaneous-annihilator rank condition. -/
theorem flagPlucker_rankConditions (F : FullFlag k V) : FlagRankConditions (flagPlucker F) := by
  intro i j hij
  apply (pluckerAnnihilator_incidence_iff i j (F.subspace i) (F.subspace j)
    ((F.finrank_eq i).trans (min_eq_left (Nat.le_of_lt i.isLt)))
    ((F.finrank_eq j).trans (min_eq_left (Nat.le_of_lt j.isLt)))).mpr
  exact F.monotone hij

/-- Exact point comparison: once the individual lines are decomposable, the
mixed rank conditions reconstruct the complete natural-indexed flag. -/
theorem mem_range_flagPlucker_iff
    (p : (i : Fin (Module.finrank k V)) → ℙ k (⋀[k]^(i : ℕ) V)) :
    p ∈ Set.range (flagPlucker (k := k) (V := V)) ↔
      (∀ i : Fin (Module.finrank k V), ∃ W : Submodule k V, ∃ hW : Module.finrank k W = (i : ℕ),
        subspacePlucker i W hW = p i) ∧ FlagRankConditions p := by
  classical
  constructor
  · rintro ⟨F, rfl⟩
    refine ⟨?_, flagPlucker_rankConditions F⟩
    intro i
    exact ⟨F.subspace i, (F.finrank_eq i).trans (min_eq_left (Nat.le_of_lt i.isLt)), rfl⟩
  · rintro ⟨hdecomp, hinc⟩
    let W (i : Fin (Module.finrank k V)) := pluckerAnnihilator (p i)
    have hrank (i : Fin (Module.finrank k V)) : Module.finrank k (W i) = (i : ℕ) := by
      obtain ⟨U, hU, hp⟩ := hdecomp i
      have heq : W i = U := by
        dsimp only [W]
        rw [← hp, pluckerAnnihilator_subspacePlucker]
      exact (congrArg (fun S : Submodule k V => Module.finrank k S) heq).trans hU
    have hmono : Monotone W := by
      intro i j hij
      have hinf : W i ⊓ W j = W i :=
        Submodule.eq_of_le_of_finrank_le inf_le_left (by
          rw [hrank]
          exact hinc i j hij)
      exact hinf.symm.le.trans inf_le_right
    refine ⟨fullFlagOfFiniteChain W hmono hrank, ?_⟩
    funext i
    rw [flagPlucker_fullFlagOfFiniteChain]
    obtain ⟨U, hU, hp⟩ := hdecomp i
    have hW : W i = U := by
      dsimp only [W]
      rw [← hp, pluckerAnnihilator_subspacePlucker]
    apply Projectivization.submodule_injective
    rw [subspacePlucker_submodule, hW, ← hp, subspacePlucker_submodule]

variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V] [IsAlgClosed k]

/-- The same point comparison under the actual ambient-product equivalence,
for every choice of exterior coordinate bases. -/
theorem mem_range_flagEmbedding_iff
    (b : CoordinateBases (k := k) V) (x : Variety.Geometric.Point (flagAmbient (k := k) V)) :
    x ∈ Set.range (flagEmbedding b) ↔
      (∀ i : Fin (Module.finrank k V), ∃ W : Submodule k V, ∃ hW : Module.finrank k W = (i : ℕ),
        subspacePlucker i W hW = ambientPointEquiv b x i) ∧
          FlagRankConditions (ambientPointEquiv b x) := by
  rw [← mem_range_flagPlucker_iff]
  constructor
  · rintro ⟨F, rfl⟩
    exact ⟨F, (ambientPointEquiv_flagEmbedding b F).symm⟩
  · rintro ⟨F, hF⟩
    refine ⟨F, (ambientPointEquiv b).injective ?_⟩
    rw [ambientPointEquiv_flagEmbedding]
    exact hF
end Theory.AlgebraicGroup.BorelGeometricConjugacy.FlagGeometry
