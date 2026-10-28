module

public import Theory.Representation.SymplecticFourOrthogonalCover.SylowFlag.Conjugation
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Actual Sp₄′ flag-stabilizer orbits

The product of roots 4 and 6 lies in the derived group, including over F₂.
Conjugating by the symplectic permutation swapping the hyperbolic pairs gives
an opposite shear. On the standard plane these are the two elementary shears,
which move every nonzero vector to e₀. An element mapping one nonzero vector
of the standard line to another stabilizes the whole line by F-linearity.
Thus both literal stabilizers are transitive on their nonzero vectors.

Source: Aschbacher–Smith, I.2.3(2), printed p.413 / PDF p.424.
-/

public section
noncomputable section
open Matrix Subgroup
open Representation.OneCohomology
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
namespace Representation.SymplecticFourOrthogonalCover.SylowFlag
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

private def swapPairs : Sp K :=
  ⟨fromBlocks !![0,1;1,0] 0 0 !![0,1;1,0], by
    rw [SymplecticGroup.mem_iff]
    ext a b
    rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
      simp [Matrix.J, Matrix.mul_apply, Matrix.fromBlocks, Matrix.one_apply,
        Fintype.sum_sum_type, Fin.sum_univ_two, CharTwo.neg_eq]⟩

omit [Finite K] in
private lemma swap_pairs_roots (t : K) :
    swapPairs * (rootElement 4 t * rootElement 6 t) =
      (rootElement 4 t * rootElement 7 t) * swapPairs (K := K) := by
  apply Subtype.ext
  change swapPairs.val * (rootMatrix 4 t * rootMatrix 6 t) =
    (rootMatrix 4 t * rootMatrix 7 t) * swapPairs.val
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [swapPairs, rootMatrix, Matrix.mul_apply, Matrix.fromBlocks,
      Matrix.single, Matrix.one_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      CharTwo.neg_eq, CharTwo.add_self_eq_zero]

private lemma lower_derived (t : K) :
    rootElement 4 t * rootElement 7 t ∈ commutator (Sp K) := by
  have h := (inferInstance : (commutator (Sp K)).Normal).conj_mem
    _ (paired_roots_derived (K := K) 1 t) (swapPairs (K := K))
  simpa only [show (![0,4] : Fin 2 → Fin 8) 1 = 4 from rfl,
    show (![2,6] : Fin 2 → Fin 8) 1 = 6 from rfl,
    swap_pairs_roots, mul_inv_cancel_right] using h

private def upper (t : K) : L (K := K) :=
  ⟨rootElement 4 t * rootElement 6 t, paired_roots_derived 1 t⟩
private def lower (t : K) : L (K := K) :=
  ⟨rootElement 4 t * rootElement 7 t, lower_derived t⟩

private def vec (a b : K) : Natural (K := K) := Sum.elim ![a,b] 0

private lemma vec_mem (a b : K) : vec a b ∈ secondPlane (K := K) := by
  rw [secondPlane_eq_plane]
  intro i
  rfl

private lemma eq_vec {x : Natural (K := K)} (hx : x ∈ secondPlane) :
    x = vec (x (.inl 0)) (x (.inl 1)) := by
  rw [secondPlane_eq_plane] at hx
  funext i
  rcases i with i | i
  · fin_cases i <;> rfl
  · exact hx i

private lemma upper_vec (t a b : K) :
    symplecticDerivedNatural 2 (upper t) (vec a b) = vec (a + t * b) b := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [upper, symplecticDerivedNatural_apply, rootElement, rootMatrix,
      Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks, Matrix.single,
      Matrix.one_apply, vec, add_comm]

private lemma lower_vec (t a b : K) :
    symplecticDerivedNatural 2 (lower t) (vec a b) = vec a (b + t * a) := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [lower, symplecticDerivedNatural_apply, rootElement, rootMatrix,
      Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks, Matrix.single,
      Matrix.one_apply, vec, add_comm]

omit [Finite K] [CharP K 2] in
private lemma stabilizer_of_invariant [Algebra (ZMod 2) K]
    (W : Submodule K (Natural (K := K))) (g : L (K := K))
    (h : ∀ x ∈ W, symplecticDerivedNatural 2 g x ∈ W) :
    g ∈ BinaryOffender.subspaceStabilizer binaryNatural (W.restrictScalars (ZMod 2)) := by
  have he : W.map (symplecticDerivedNatural 2 g) = W :=
    Submodule.eq_of_le_of_finrank_eq
      (by rintro _ ⟨x,hx,rfl⟩; exact h x hx)
      (Transport.finrank_map _ _ _)
  intro x
  change symplecticDerivedNatural 2 g x ∈ W ↔ x ∈ W
  constructor
  · intro hx
    rw [← he] at hx
    obtain ⟨y,hy,hyx⟩ := hx
    have : y = x := ((symplecticDerivedNatural 2).apply_bijective g).injective hyx
    exact this ▸ hy
  · exact h x

variable [Algebra (ZMod 2) K]
private abbrev planeStab := BinaryOffender.subspaceStabilizer
  (binaryNatural (K := K)) (secondPlane.restrictScalars (ZMod 2))

private def upperP (t : K) : planeStab (K := K) :=
  ⟨upper t, stabilizer_of_invariant secondPlane (upper t) (by
    intro x hx
    rw [eq_vec hx, upper_vec]
    exact vec_mem _ _)⟩
private def lowerP (t : K) : planeStab (K := K) :=
  ⟨lower t, stabilizer_of_invariant secondPlane (lower t) (by
    intro x hx
    rw [eq_vec hx, lower_vec]
    exact vec_mem _ _)⟩

private lemma to_seed_right (a b : K) (hb : b ≠ 0) :
    ∃ g : planeStab (K := K),
      symplecticDerivedNatural 2 g.val (vec a b) = vec 1 0 := by
  refine ⟨lowerP (-b) * upperP ((1-a)/b), ?_⟩
  change symplecticDerivedNatural 2 (lower (-b) * upper ((1-a)/b)) (vec a b) = _
  have hc : a + ((1-a)/b)*b = 1 := by rw [div_mul_cancel₀ _ hb]; ring
  rw [map_mul, Module.End.mul_apply, upper_vec, hc, lower_vec]
  simp

private lemma to_seed (x : Natural (K := K)) (hx : x ∈ secondPlane) (hn : x ≠ 0) :
    ∃ g : planeStab (K := K), symplecticDerivedNatural 2 g.val x = vec 1 0 := by
  by_cases hb : x (.inl 1) = 0
  · have ha : x (.inl 0) ≠ 0 := by
      intro ha
      apply hn
      rw [eq_vec hx,ha,hb]
      ext i
      rcases i with i | i <;> fin_cases i <;> rfl
    obtain ⟨g,hg⟩ := to_seed_right (x (.inl 0)) (1 : K) one_ne_zero
    refine ⟨g * lowerP ((x (.inl 0))⁻¹), ?_⟩
    change symplecticDerivedNatural 2 (g.val * lower ((x (.inl 0))⁻¹)) x = _
    rw [map_mul, Module.End.mul_apply]
    conv_lhs => arg 2; arg 2; rw [eq_vec hx, hb]
    rw [lower_vec, inv_mul_cancel₀ ha, zero_add]
    exact hg
  · rw [eq_vec hx]
    exact to_seed_right _ _ hb

/-- The literal plane stabilizer in Sp₄(K)′ is transitive on its nonzero vectors. -/
theorem secondPlane_transitive (x y : Natural (K := K))
    (hx : x ∈ secondPlane) (hy : y ∈ secondPlane) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    ∃ g : BinaryOffender.subspaceStabilizer binaryNatural
      (secondPlane.restrictScalars (ZMod 2)), binaryNatural g.val x = y := by
  obtain ⟨a,ha⟩ := to_seed x hx hx0
  obtain ⟨b,hb⟩ := to_seed y hy hy0
  refine ⟨b⁻¹ * a, ?_⟩
  change symplecticDerivedNatural 2 (b.val⁻¹ * a.val) x = y
  rw [map_mul, Module.End.mul_apply, ha, ← hb]
  exact (symplecticDerivedNatural 2).inv_self_apply b.val y

private lemma line_stabilizer_of_maps_point (g : L (K := K))
    (x : Natural (K := K)) (hx : x ∈ firstLine) (hx0 : x ≠ 0)
    (hy : symplecticDerivedNatural 2 g x ∈ firstLine) :
    g ∈ BinaryOffender.subspaceStabilizer binaryNatural
      (firstLine.restrictScalars (ZMod 2)) := by
  apply stabilizer_of_invariant
  have he : firstLine (K := K) = K ∙ x :=
    eq_span_singleton_of_mem_of_finrank_eq_one (firstLine_finrank (K := K)) hx hx0
  intro v hv
  rw [he] at hv
  obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [map_smul]
  exact Submodule.smul_mem _ c hy

/-- The literal line stabilizer is transitive, including over the binary field. -/
theorem firstLine_transitive (x y : Natural (K := K))
    (hx : x ∈ firstLine) (hy : y ∈ firstLine) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    ∃ g : BinaryOffender.subspaceStabilizer binaryNatural
      (firstLine.restrictScalars (ZMod 2)), binaryNatural g.val x = y := by
  have hle : firstLine (K := K) ≤ secondPlane := by
    rw [firstLine_eq_point, secondPlane_eq_plane]
    exact point_le_plane
  obtain ⟨g,hg⟩ := secondPlane_transitive x y (hle hx) (hle hy) hx0 hy0
  have hm : symplecticDerivedNatural 2 g.val x ∈ firstLine := by
    change binaryNatural g.val x ∈ firstLine
    rw [hg]
    exact hy
  exact ⟨⟨g.val, line_stabilizer_of_maps_point g.val x hx hx0 hm⟩, hg⟩


end Representation.SymplecticFourOrthogonalCover.SylowFlag
