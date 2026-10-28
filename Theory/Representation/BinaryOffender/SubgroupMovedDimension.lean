module
public import Theory.Representation.BinaryOffender.ConjugateSubgroupSaturation
public import Theory.Representation.BinaryOffender.SmallMovedProducts
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.IrreducibleMovedGeneration
public import Theory.Representation.BinaryOffender.IrreducibleExistence
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Conjugate bounds and faithfulness on the original commutator space

Dual fixed-space codimension bounds the whole commutator of a subgroup
contained in a join of conjugate cyclic actors. Fixed layers are retained.
For a faithful action of a simple perfect subgroup, restriction to that
commutator remains faithful: a trivial restriction would make the original
action quadratic, hence trivial by perfectness.
Source application: Aschbacher--Smith, proof of 12.6.26, printed p.833.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Conjugate cyclic actors bound the literal subgroup commutator space. -/
theorem moved_finrank_le_mul_displacement_of_conjugates
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G)
    (v : G) {n : ℕ} (c : Fin n → G)
    (hg : K ≤ ⨆ i, (zpowers v).map (MulAut.conj (c i)).toMonoidHom) :
    Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ K) ≤
      n * Module.finrank (ZMod 2) (ρ v - LinearMap.id).range := by
  have h := fixedCodim_le_card_mul_of_subgroup_conjugates ρ.dual K (zpowers v) c hg
  rwa [fixedCodim_dual_eq_moved_finrank, Fintype.card_fin,
    fixedCodim_zpowers_dual, fixedCodim_zpowers_eq_displacement_rank] at h

omit [FiniteDimensional (ZMod 2) V] in
/-- The simple perfect actor remains faithful on its own commutator space. -/
theorem faithful_on_moved_of_simple_perfect
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G)
    [IsSimpleGroup K] [Group.IsPerfect K] (hf : Function.Injective (ρ.comp K.subtype)) :
    Function.Injective (invariantSubspace ρ K (subspaceCommutator ρ ⊤ K)
      (subspaceCommutator_invariant ρ ⊤ K)).toRepresentation := by
  let W := invariantSubspace ρ K (subspaceCommutator ρ ⊤ K)
    (subspaceCommutator_invariant ρ ⊤ K)
  rcases W.toRepresentation.normal_ker.eq_bot_or_eq_top with he | he
  · exact W.toRepresentation.ker_eq_bot_iff.mp he
  · have htriv : W.toRepresentation = 1 := MonoidHom.ker_eq_top_iff.mp he
    have hfixed : subspaceCommutator ρ ⊤ K ≤ fixedSpace ρ K := by
      intro w hw k
      exact congrArg Subtype.val (DFunLike.congr_fun
        (congrArg (fun σ => σ k) htriv) (⟨w,hw⟩ : W.toSubmodule))
    have hall := le_fixedSpace_of_commutator_le_fixedSpace ρ K ⊤
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) hfixed
    have hone (k : K) : k = 1 := by
      apply hf
      ext v
      exact (hall Submodule.mem_top k).trans (by simp)
    obtain ⟨k,hk⟩ := exists_ne (1 : K)
    exact (hk (hone k)).elim
end Representation.BinaryOffender
