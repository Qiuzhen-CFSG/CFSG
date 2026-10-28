module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.OppositeBorels.BorelCertification.SolvableFlags.Roots
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.OppositeBorels.BorelCertification.SolvableFlags.Torus

/-!
# The two flags invariant under a concrete signed Spin candidate

Torus projection makes every invariant subspace a coordinate subspace. The
simple-root actions make its coordinate set an order ideal in the eight-weight
diamond. There are two ideals only at dimension four; all other dimensions
have a unique ideal. Thus a full invariant flag has one of the two middle
choices, consistently through the whole flag.

Source: the natural-module maximality argument for GLS3, 1.11.2
(`refs/KGroup/GLS3/Chapter1.tex`) and Steinberg (6.2)(a)
(`refs/KGroup/GLS3/Chapter2St2.tex`). This classification concerns the actual
coroot torus and signed root points, with no Borel maximality hypothesis.
-/

@[expose] public section
open Theory Theory.AlgebraicGroup
open Theory.AlgebraicGroup.BorelGeometricConjugacy
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.SimplyConnected.Pinning.NaturalCoefficients
noncomputable section
namespace Triality.SimplyConnected.OppositeBorels.BorelCertification.SolvableFlags
universe u
variable (k : Type u) [Field k]

def basisIndices (negative : Bool) (W : Submodule k (QuadraticSpace k)) : Finset (Fin 8) := by
  classical
  exact Finset.univ.filter fun i => orderedBasis k (signedOrder negative) i ∈ W

lemma coordinateFlag_eq_span_initial (negative alternate : Bool) (r : ℕ) :
    (coordinateFlag k (flagOrder negative alternate)).subspace r =
      Submodule.span k
        (orderedBasis k (signedOrder negative) '' (Combinatorics.initial alternate r : Set (Fin 8))) := by
  classical
  apply congrArg (Submodule.span k)
  let p : Equiv.Perm (Fin 8) := if alternate then middleSwap else Equiv.refl _
  have hp (i : Fin 8) : p (p i) = i := by cases alternate <;> simp [p, middleSwap]
  have hm (i : Fin 8) : i ∈ Combinatorics.initial alternate r ↔ (p i).val < r := by
    cases alternate <;> simp [Combinatorics.initial, p, middleSwap]
  have hb (i : Fin 8) : orderedBasis k (flagOrder negative alternate) i =
      orderedBasis k (signedOrder negative) (p i) := by
    simp [orderedBasis_apply, flagOrder, p]
  apply Set.ext
  intro v
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨p (Fin.castLE (min_le_right r 8) j), (hm _).mpr ?_, (hb _).symm⟩
    rw [hp]
    exact j.isLt.trans_le (min_le_left _ _)
  · rintro ⟨i, hi, rfl⟩
    have hj : (p i).val < min r 8 := lt_min ((hm i).mp hi) (p i).isLt
    refine ⟨⟨(p i).val, hj⟩, ?_⟩
    dsimp only
    rw [hb]
    change orderedBasis k (signedOrder negative) (p (p i)) = _
    rw [hp]

lemma coordinateFlag_subspace_min (e : Fin 8 ≃ Index) (r : ℕ) :
    (coordinateFlag k e).subspace (min r 8) = (coordinateFlag k e).subspace r := by
  ext v
  simp only [mem_coordinateFlag]
  constructor
  · intro h i hi; exact h i (min_le_left _ _ |>.trans hi)
  · intro h i hi
    exact h i ((min_le_iff.mp hi).resolve_right (not_le.mpr i.isLt))

lemma coordinateFlag_subspace_eq_of_ne_four (negative a b : Bool) (r : ℕ) (hr : r ≠ 4) :
    (coordinateFlag k (flagOrder negative a)).subspace r =
      (coordinateFlag k (flagOrder negative b)).subspace r := by
  rw [coordinateFlag_eq_span_initial, coordinateFlag_eq_span_initial]
  suffices hh : Combinatorics.initial a r = Combinatorics.initial b r by rw [hh]
  have h34 : (3 < r ↔ 4 < r) := by omega
  ext i
  cases a <;> cases b <;> fin_cases i <;>
    norm_num [Combinatorics.initial, Equiv.swap_apply_def, Fin.ext_iff]
  all_goals
    first | exact h34 | exact h34.symm

variable [IsAlgClosed k] [CharP k 2]

lemma eq_span_basisIndices (negative : Bool) (W : Submodule k (QuadraticSpace k))
    (hW : ∀ g ∈ candidate k negative, ∀ v ∈ W, (naturalAction k g).1 v ∈ W) :
    W = Submodule.span k
      (orderedBasis k (signedOrder negative) '' (basisIndices k negative W : Set (Fin 8))) := by
  classical
  apply le_antisymm
  · intro v hv
    rw [← (orderedBasis k (signedOrder negative)).sum_repr v]
    apply Submodule.sum_mem
    intro i hi
    by_cases hz : (orderedBasis k (signedOrder negative)).repr v i = 0
    · simp only [hz, zero_smul]; exact Submodule.zero_mem _
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨i, ?_, rfl⟩
      simp only [basisIndices, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      apply (W.smul_mem_iff hz).mp
      simpa [orderedBasis, Module.Basis.repr_reindex_apply, Module.Basis.coord_apply] using
        coordinate_mem_of_candidate_invariant k negative W hW v hv (signedOrder negative i)
  · apply Submodule.span_le.mpr
    rintro v ⟨i, hi, rfl⟩
    simpa [basisIndices] using hi

lemma basisIndices_card (negative : Bool) (W : Submodule k (QuadraticSpace k))
    (hW : ∀ g ∈ candidate k negative, ∀ v ∈ W, (naturalAction k g).1 v ∈ W) :
    (basisIndices k negative W).card = Module.finrank k W := by
  classical
  let I := basisIndices k negative W
  have hspan : W = Submodule.span k
      (Set.range fun i : I => orderedBasis k (signedOrder negative) i) := by
    rw [eq_span_basisIndices k negative W hW]
    congr 1
    exact Set.image_eq_range _ _
  have hli : LinearIndependent k (fun i : I => orderedBasis k (signedOrder negative) i) :=
    (orderedBasis k (signedOrder negative)).linearIndependent.comp _ Subtype.val_injective
  conv_rhs => rw [hspan, finrank_span_eq_card hli, Fintype.card_coe]

private lemma subspace_classification_of_edges (negative : Bool) (W : Submodule k (QuadraticSpace k))
    (hW : ∀ g ∈ candidate k negative, ∀ v ∈ W, (naturalAction k g).1 v ∈ W)
    (hEdges : ∀ i j, Combinatorics.Edge i j →
      orderedBasis k (signedOrder negative) j ∈ W → orderedBasis k (signedOrder negative) i ∈ W) :
    ∃ alternate : Bool,
      W = (coordinateFlag k (flagOrder negative alternate)).subspace (Module.finrank k W) := by
  classical
  obtain ⟨alternate, ha⟩ := Combinatorics.initial_of_closed (basisIndices k negative W)
    (by
      intro i j hij hj
      simp only [basisIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact hEdges i j hij hj)
  refine ⟨alternate, ?_⟩
  calc
    W = Submodule.span k (orderedBasis k (signedOrder negative) ''
        (basisIndices k negative W : Set (Fin 8))) := eq_span_basisIndices k negative W hW
    _ = Submodule.span k (orderedBasis k (signedOrder negative) ''
        (Combinatorics.initial alternate (Module.finrank k W) : Set (Fin 8))) := by
      rw [ha, basisIndices_card k negative W hW]
    _ = _ := (coordinateFlag_eq_span_initial k negative alternate _).symm

lemma candidate_invariant_subspace (negative : Bool) (W : Submodule k (QuadraticSpace k))
    (hW : ∀ g ∈ candidate k negative, ∀ v ∈ W, (naturalAction k g).1 v ∈ W) :
    ∃ alternate : Bool,
      W = (coordinateFlag k (flagOrder negative alternate)).subspace (Module.finrank k W) :=
  subspace_classification_of_edges k negative W hW (basis_mem_of_edge k negative W hW)

lemma candidate_invariant_flag (negative : Bool) (F : FullFlag k (QuadraticSpace k))
    (hF : ∀ g ∈ candidate k negative, ∀ r v, v ∈ F.subspace r →
      (naturalAction k g).1 v ∈ F.subspace r) :
    ∃ alternate : Bool, F = coordinateFlag k (flagOrder negative alternate) := by
  have hW (r : ℕ) := candidate_invariant_subspace k negative (F.subspace r)
    (fun g hg => hF g hg r)
  obtain ⟨alternate, ha⟩ := hW 4
  rw [F.finrank_eq, finrank_quadraticSpace, min_eq_left (by decide : 4 ≤ 8)] at ha
  refine ⟨alternate, FullFlag.ext (fun r => ?_)⟩
  by_cases hr : r = 4
  · subst r; exact ha
  obtain ⟨a, he⟩ := hW r
  rw [F.finrank_eq, finrank_quadraticSpace, coordinateFlag_subspace_min] at he
  exact he.trans (coordinateFlag_subspace_eq_of_ne_four k negative a alternate r hr)

end Triality.SimplyConnected.OppositeBorels.BorelCertification.SolvableFlags
