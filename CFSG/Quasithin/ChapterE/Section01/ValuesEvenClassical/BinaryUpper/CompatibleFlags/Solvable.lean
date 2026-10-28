module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.BinaryUpper.CompatibleFlags.Alignment
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.Pairs
public import Theory.SpecificGroups.SymmetricFourSolvable

/-!
# Solvability of the binary outer flags and the four-dimensional middle flag

The literal flags have block sizes 2+2, 2+1+2, and 1+2+1. We reuse the
actual diagonal action of a five-dimensional flag with two nonadjacent
omitted nodes: its kernel is its intrinsic two-core, and its diagonal
factors are identified with S₃ × S₃ by the binary projective-line actions.

Extending a four-dimensional matrix by an identity coordinate embeds its
2+2 flag in the 2+2+1 flag, and its 1+2+1 flag in the 1+2+2 flag. The
entry formulas below prove these are embeddings of the specified flags.
Restricting the actual diagonal homomorphism along each embedding gives a
normal two-group kernel and solvable image. No extension shape or
solvability assumption is imposed on any of the three requested flags.

The proved coordinate comparison retains the original omitted root indices.
The ambient applications use Sylow alignment and the diagram-stability
normalization theorem, which includes graph extensions.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.14(1), printed p.214, citing Aschbacher (1982), Lemma 4.7.
This proves the solvable local cases used in that argument; the generating
family and the middle dimension-five local quotient have separate owners.
-/

public section

open Subgroup
open Representation.OneCohomology.SLHigherNatural
open BinaryLinear.SmallParabolicLevi BinaryLinear.SmallParabolicLevi.TwoNodes
open BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.BinaryUpper

private theorem symmetricThree_solvable : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  exact Group.isSolvable_of_isSolvable_injective
    (Equiv.Perm.viaEmbeddingHom_injective ⟨Fin.castSucc, Fin.castSucc_injective 3⟩)

/-- The actual diagonal action, followed by the two marked binary projective-line actions. -/
private noncomputable def pairFlagDiagonal (b : FiveBasis) (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    BinaryLinear.FiveFlagGeometry.flagStabilizer b ({i, j} : Set (Fin 4))ᶜ →*
      Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) :=
  (pairFactorsEquiv i j h).toMonoidHom.comp (flagDiagonalAction b ({i, j} : Set (Fin 4))ᶜ)

private theorem pairFlagDiagonal_ker (b : FiveBasis) (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    (pairFlagDiagonal b i j h).ker =
      pCore 2 (BinaryLinear.FiveFlagGeometry.flagStabilizer b ({i, j} : Set (Fin 4))ᶜ) := by
  ext g
  rw [← ker_flagDiagonalAction]
  change pairFactorsEquiv i j h (flagDiagonalAction b ({i, j} : Set (Fin 4))ᶜ g) = 1 ↔
    flagDiagonalAction b ({i, j} : Set (Fin 4))ᶜ g = 1
  constructor
  · intro hg
    exact (pairFactorsEquiv i j h).injective (hg.trans (map_one _).symm)
  · intro hg
    exact (congrArg (pairFactorsEquiv i j h) hg).trans (map_one _)

/-- Restrict the diagonal map itself: its kernel embeds in the proved two-core. -/
private theorem solvable_of_pairFlagEmbedding {A : Type*} [Group A] [Finite A]
    (b : FiveBasis) (i j : Fin 4) (h : i.val + 1 < j.val ∨ j.val + 1 < i.val)
    (f : A →* BinaryLinear.FiveFlagGeometry.flagStabilizer b ({i, j} : Set (Fin 4))ᶜ)
    (hf : Function.Injective f) : Group.IsSolvable A := by
  let q := pairFlagDiagonal b i j h
  let a := q.comp f
  let fk : a.ker →* q.ker :=
    { toFun x := ⟨f x.val, x.property⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' x y := Subtype.ext (map_mul f x.val y.val) }
  have hfk : Function.Injective fk := by
    intro x y hxy
    exact Subtype.ext (hf (congrArg Subtype.val hxy))
  have hq : IsPGroup 2 q.ker := by
    rw [pairFlagDiagonal_ker]
    exact pCore_isPGroup
  let : Group.IsNilpotent a.ker := (hq.of_injective fk hfk).isNilpotent
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := symmetricThree_solvable
  exact Group.isSolvable_of_ker_le_range a.ker.subtype a (by simp)

/-- Extend the given matrix by the identity on its fifth coordinate. -/
private def extendFour : SL 4 →* SL 5 where
  toFun A := ⟨Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks A.val 0 0 (1 : Matrix (Fin 1) (Fin 1) (ZMod 2))), by
      rw [Matrix.det_reindex_self]
      simp⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' A B := by
    apply Subtype.ext
    change Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (A.val * B.val) 0 0 (1 : Matrix (Fin 1) (Fin 1) (ZMod 2))) = _
    rw [show Matrix.fromBlocks (A.val * B.val) 0 0 (1 : Matrix (Fin 1) (Fin 1) (ZMod 2)) =
      Matrix.fromBlocks A.val 0 0 1 * Matrix.fromBlocks B.val 0 0 1 by
        simp [Matrix.fromBlocks_multiply]]
    exact map_mul (Matrix.reindexRingEquiv (ZMod 2) finSumFinEquiv) _ _

private theorem extendFour_entry (A : SL 4) (i j : Fin 4) :
    (extendFour A).val i.castSucc j.castSucc = A.val i j := by
  change Matrix.fromBlocks A.val 0 0 (1 : Matrix (Fin 1) (Fin 1) (ZMod 2))
    (finSumFinEquiv.symm i.castSucc) (finSumFinEquiv.symm j.castSucc) = A.val i j
  simp

private theorem extendFour_last_row (A : SL 4) (j : Fin 4) :
    (extendFour A).val (Fin.last 4) j.castSucc = 0 := by
  change Matrix.fromBlocks A.val 0 0 (1 : Matrix (Fin 1) (Fin 1) (ZMod 2))
    (finSumFinEquiv.symm (Fin.last 4)) (finSumFinEquiv.symm j.castSucc) = 0
  rw [finSumFinEquiv_symm_last, finSumFinEquiv_symm_apply_castSucc]
  rfl

private theorem extendFour_injective : Function.Injective extendFour := by
  intro A B h
  apply Subtype.ext
  ext i j
  have he := congrArg (fun C : SL 5 => C.val i.castSucc j.castSucc) h
  simpa only [extendFour_entry] using he

private theorem extendFour_preservesCut (A : SL 4) (k : ℕ) (hk : k ≤ 4)
    (hA : k < 4 → PreservesCut k A) : PreservesCut k (extendFour A) := by
  intro i j hik hjk
  obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last (show j ≠ Fin.last 4 by
    intro he; subst j; simp only [Fin.val_last] at hjk; omega)
  revert hik
  refine Fin.lastCases (fun _ => ?_) (fun i hi => ?_) i
  · exact extendFour_last_row A j
  · rw [extendFour_entry]
    change k ≤ i.val at hi
    exact hA (by have := i.isLt; omega) i j hi hjk

/-- The original cuts are preserved, and the new fourth cut is automatic. -/
private def extendFourParabolic (J K : Set ℕ) (hJK : J ⊆ K) :
    parabolic 4 J →* parabolic 5 K where
  toFun A := ⟨extendFour A.val, by
    intro k hk
    change 0 < k ∧ k < 5 ∧ k - 1 ∉ K at hk
    constructor
    · apply extendFour_preservesCut A.val k (by omega)
      intro hk4
      exact (A.property k ⟨hk.1, hk4, fun h => hk.2.2 (hJK h)⟩).1
    · rw [← map_inv]
      apply extendFour_preservesCut A.val⁻¹ k (by omega)
      intro hk4
      exact (A.property k ⟨hk.1, hk4, fun h => hk.2.2 (hJK h)⟩).2⟩
  map_one' := Subtype.ext (map_one extendFour)
  map_mul' A B := Subtype.ext (map_mul extendFour A.val B.val)

private theorem extendFourParabolic_injective (J K : Set ℕ) (hJK : J ⊆ K) :
    Function.Injective (extendFourParabolic J K hJK) := by
  intro A B h
  exact Subtype.ext (extendFour_injective (congrArg Subtype.val h))


/-- The same coordinate flag under the proved SL-to-PSL-to-linear comparisons. -/
private noncomputable def fiveParabolicEquivPair (i j : Fin 4) :
    parabolic 5 {i.val, j.val} ≃*
      BinaryLinear.FiveFlagGeometry.flagStabilizer (coordinateBasis 4) ({i, j} : Set (Fin 4))ᶜ :=
  ((binaryProjectiveEquiv 5).subgroupMap _).trans
    (((linearComparison 5).subgroupMap _).trans (MulEquiv.subgroupCongr (by
      change (projectiveParabolic 5 {i.val, j.val}).map (linearComparison 5).toMonoidHom = _
      rw [map_projectiveParabolic_linear]
      have hc : {k : Fin 4 | k.val ∉ ({i.val, j.val} : Set ℕ)} = ({i, j} : Set (Fin 4))ᶜ := by
        ext k
        simp [Fin.ext_iff]
      rw [hc]
      rfl)))

private theorem fiveParabolic_pair_solvable (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    Group.IsSolvable (parabolic 5 {i.val, j.val}) :=
  solvable_of_pairFlagEmbedding (coordinateBasis 4) i j h
    (fiveParabolicEquivPair i j).toMonoidHom (fiveParabolicEquivPair i j).injective

private theorem fourParabolic_solvable (J : Set ℕ) (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) (hJ : J ⊆ {i.val, j.val}) :
    Group.IsSolvable (parabolic 4 J) :=
  solvable_of_pairFlagEmbedding (coordinateBasis 4) i j h
    ((fiveParabolicEquivPair i j).toMonoidHom.comp (extendFourParabolic J {i.val, j.val} hJ))
    ((fiveParabolicEquivPair i j).injective.comp (extendFourParabolic_injective _ _ _))

private theorem projective_solvable_of_linear {d : ℕ} (J : Set ℕ)
    (hs : Group.IsSolvable (parabolic d J)) : Group.IsSolvable (projectiveParabolic d J) := by
  let := hs
  exact Group.isSolvable_of_surjective
    (f := ((binaryProjectiveEquiv d).subgroupMap (parabolic d J)).toMonoidHom)
    ((binaryProjectiveEquiv d).subgroupMap (parabolic d J)).surjective

/-- The binary outer flag is solvable in dimensions four and five. -/
theorem projectiveParabolic_outer_isSolvable {d : ℕ} (hd : d = 4 ∨ d = 5) :
    Group.IsSolvable (projectiveParabolic d (outerRoots d)) := by
  rcases hd with rfl | rfl
  · exact projective_solvable_of_linear _
      (fourParabolic_solvable _ 0 2 (Or.inl (by decide)) (by simp [outerRoots]))
  · exact projective_solvable_of_linear _
      (fiveParabolic_pair_solvable 0 3 (Or.inl (by decide)))

/-- The actual four-dimensional middle flag, of block sizes 1+2+1, is solvable. -/
theorem projectiveParabolic_middle_four_isSolvable :
    Group.IsSolvable (projectiveParabolic 4 (middleRoots 4)) := by
  apply projective_solvable_of_linear
  apply fourParabolic_solvable _ 1 3 (Or.inl (by decide))
  intro r hr
  change 0 < r ∧ r + 2 < 4 at hr
  have : r = 1 := by omega
  simp [this]

/-- Adjoining the aligned ambient Sylow subgroup preserves solvability of the outer flag. -/
theorem ambientFlag_outer_isSolvable {G : Type*} [Group G] [Finite G] {d : ℕ}
    (hd : d = 4 ∨ d = 5) (L : Subgroup G) [L.Normal] (T : Sylow 2 G)
    (e : L ≃* PSL d) (he : SylowAligned L (T : Subgroup G) e) :
    Group.IsSolvable (ambientFlag L (T : Subgroup G) e (outerRoots d)) :=
  ambientFlag_isSolvable_of_model hd L T e he _ (outerRoots_diagramStable d)
    (projectiveParabolic_outer_isSolvable hd)

/-- The middle flag in dimension four remains solvable in its ambient Sylow extension. -/
theorem ambientFlag_middle_four_isSolvable {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) [L.Normal] (T : Sylow 2 G)
    (e : L ≃* PSL 4) (he : SylowAligned L (T : Subgroup G) e) :
    Group.IsSolvable (ambientFlag L (T : Subgroup G) e (middleRoots 4)) :=
  ambientFlag_isSolvable_of_model (Or.inl rfl) L T e he _ (middleRoots_diagramStable 4)
    projectiveParabolic_middle_four_isSolvable

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.BinaryUpper
