module

public import Theory.Representation.SymplecticFourOrthogonalCover.Universal
public import Theory.SpecificGroups.SymplecticFour.RootSubgroup

/-!
# Transvection roots in the orthogonal cover of Sp₄(K)′

For |K| > 2, perfectness places the literal matrix root in the derived group.
Its displacement on the five-space is v₂(t e₀, √t). These images are
nonsingular lines, pairwise disjoint for distinct nonzero parameters, and
span the first natural line's preimage. That preimage is root-fixed.
Two explicit displacements suffice to span it. Scalar restriction and the
universal cover quotient then give the same commutator and centrality
identities for every binary cover over its original projection.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), I.2.3(1b),(3),
printed p.413/PDF p.424. The binary obstruction and conjugation transport
are supplied in the `Binary` and `Conjugates` extensions.
-/

@[expose] public section

noncomputable section
namespace Representation.SymplecticFourOrthogonalCover.Roots
open Matrix ClassicalOrthogonal Representation.OneCohomology
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour hiding e
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

abbrev sqrt : K ≃+* K := (frobeniusEquiv K 2).symm

theorem root_mem_derived (hcard : 2 < Nat.card K) (t : K) :
    rootElement 0 t ∈ commutator (Sp K) := by
  rw [LargeField.commutator_eq_top hcard]
  trivial

def element (hcard : 2 < Nat.card K) (t : K) : L (K := K) :=
  ⟨rootElement 0 t, root_mem_derived hcard t⟩

def group : Subgroup (L (K := K)) :=
  (RootSubgroup.group 0).subgroupOf (commutator (Sp K))

lemma element_mem_group (hcard : 2 < Nat.card K) (t : K) : element hcard t ∈ group :=
  (RootSubgroup.mem_group_iff 0 _).mpr ⟨t, rfl⟩

lemma mem_group (hcard : 2 < Nat.card K) (g : L (K := K)) :
    g ∈ group ↔ ∃ t, element hcard t = g := by
  change g.val ∈ RootSubgroup.group 0 ↔ _
  rw [RootSubgroup.mem_group_iff]
  exact ⟨fun ⟨t, ht⟩ => ⟨t, Subtype.ext ht⟩,
    fun ⟨t, ht⟩ => ⟨t, congrArg Subtype.val ht⟩⟩

lemma correction_root (t : K) (v : Natural (K := K)) :
    correction (rootElement 0 t) v = sqrt t * v (.inr 0) := by
  simp [correction, quadraticCocycle, transposeSp, rootElement, rootMatrix,
    rowQuadratic, Matrix.transpose_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
    Matrix.single, Matrix.fromBlocks, sqrt]

omit [Finite K] [CharP K 2] in
lemma natural_root (t : K) (v : Natural (K := K)) :
    (rootElement 0 t).val *ᵥ v = v + (t * v (.inr 0)) • e 0 := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [rootElement, rootMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Fin.sum_univ_two, Matrix.single, Matrix.fromBlocks, e, add_comm]

def vector (t : K) : Space (K := K) := (t • e 0, sqrt t)

lemma displacement (hcard : 2 < Nat.card K) (t : K) (v : Space (K := K)) :
    action (element hcard t) v - v = v.1 (.inr 0) • vector t := by
  rw [action_apply]
  change ((rootElement 0 t).val *ᵥ v.1, v.2 + correction (rootElement 0 t) v.1) - v = _
  rw [natural_root, correction_root]
  apply Prod.ext
  · change v.1 + (t * v.1 (.inr 0)) • e 0 - v.1 = _
    simp [vector, smul_smul, mul_comm]
  · change v.2 + sqrt t * v.1 (.inr 0) - v.2 = _
    simp [vector, mul_comm]

def rootDisplacement (hcard : 2 < Nat.card K) (t : K) : Submodule K (Space (K := K)) :=
  LinearMap.range (action (element hcard t) - LinearMap.id)

lemma rootDisplacement_eq_span (hcard : 2 < Nat.card K) (t : K) :
    rootDisplacement hcard t = Submodule.span K {vector t} := by
  ext v
  rw [rootDisplacement, LinearMap.mem_range, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w.1 (.inr 0), (displacement hcard t w).symm⟩
  · rintro ⟨c, rfl⟩
    refine ⟨(c • ClassicalOrthogonal.f 0, 0), ?_⟩
    change action (element hcard t) (c • ClassicalOrthogonal.f 0, 0) - (c • ClassicalOrthogonal.f 0, 0) = _
    rw [displacement]
    simp [ClassicalOrthogonal.f]

lemma vector_ne_zero (t : K) (ht : t ≠ 0) : vector t ≠ 0 := by
  intro h
  have hs := congrArg Prod.snd h
  exact ht (sqrt.injective (hs.trans (map_zero sqrt).symm))

lemma rootDisplacement_dimension (hcard : 2 < Nat.card K) (t : K) (ht : t ≠ 0) :
    Module.finrank K (rootDisplacement hcard t) = 1 := by
  rw [rootDisplacement_eq_span]
  exact finrank_span_singleton (vector_ne_zero t ht)

def firstPreimage : Submodule K (Space (K := K)) := firstLine.comap projection.toLinearMap

lemma mem_firstPreimage (v : Space (K := K)) :
    v ∈ firstPreimage ↔ ∃ a : K, a • e 0 = v.1 := by
  exact Submodule.mem_span_singleton

lemma rootDisplacement_le_firstPreimage (hcard : 2 < Nat.card K) (t : K) :
    rootDisplacement hcard t ≤ firstPreimage := by
  rw [rootDisplacement_eq_span]
  apply Submodule.span_le.mpr
  intro v hv
  rcases Set.mem_singleton_iff.mp hv with rfl
  exact (mem_firstPreimage _).mpr ⟨t, rfl⟩

lemma form_vector (t : K) : formB 2 K (vector t) = t := by
  simp [vector, formB_apply, formD_apply, e, frobeniusEquiv_symm_pow_p, sqrt]

lemma rootDisplacement_nonsingular (hcard : 2 < Nat.card K) (t : K) (ht : t ≠ 0)
    (v : Space (K := K)) (hv : v ∈ rootDisplacement hcard t) (hne : v ≠ 0) :
    formB 2 K v ≠ 0 := by
  rw [rootDisplacement_eq_span, Submodule.mem_span_singleton] at hv
  obtain ⟨a, rfl⟩ := hv
  have ha : a ≠ 0 := by intro h; simp [h] at hne
  rw [QuadraticMap.map_smul, form_vector]
  exact mul_ne_zero (mul_ne_zero ha ha) ht

lemma rootDisplacement_ne_radical (hcard : 2 < Nat.card K) (t : K) (ht : t ≠ 0) :
    rootDisplacement hcard t ≠ radical := by
  intro he
  have hm : vector t ∈ rootDisplacement hcard t := by
    rw [rootDisplacement_eq_span]
    exact Submodule.subset_span (Set.mem_singleton _)
  rw [he, mem_radical] at hm
  have hh := congrFun hm (.inl 0)
  exact ht (by simpa [vector, e] using hh)

lemma rootDisplacement_disjoint (hcard : 2 < Nat.card K)
    (s t : K) (hs : s ≠ 0) (hst : s ≠ t) :
    Disjoint (rootDisplacement hcard s) (rootDisplacement hcard t) := by
  rw [Submodule.disjoint_def]
  intro v hvs hvt
  rw [rootDisplacement_eq_span, Submodule.mem_span_singleton] at hvs hvt
  obtain ⟨a, rfl⟩ := hvs
  obtain ⟨b, hb⟩ := hvt
  by_cases ha : a = 0
  · simp [ha]
  have hz : (a • vector s).2 ≠ 0 := mul_ne_zero ha ((map_ne_zero sqrt).mpr hs)
  have hrel (u c : K) : u * (c • vector u).2 ^ 2 = ((c • vector u).1 (.inl 0)) ^ 2 := by
    simp [vector, e, mul_pow, frobeniusEquiv_symm_pow_p, sqrt]
    ring
  have hh := (hrel s a).trans ((congrArg (fun v : Space (K := K) => v.1 (.inl 0) ^ 2) hb).symm)
  rw [← hrel t b, congrArg Prod.snd hb] at hh
  exact (hst (mul_right_cancel₀ (pow_ne_zero 2 hz) hh)).elim

lemma firstPreimage_fixed (hcard : 2 < Nat.card K) :
    firstPreimage (K := K) ≤ fixed (action.comp group.subtype) := by
  intro v hv g
  obtain ⟨a, ha⟩ := (mem_firstPreimage v).mp hv
  obtain ⟨t, ht⟩ := (mem_group hcard g.val).mp g.property
  change action g.val v = v
  rw [← ht, ← sub_eq_zero, displacement]
  rw [← ha]
  simp [e]

omit [CharP K 2] in
private lemma exists_parameter (hcard : 2 < Nat.card K) : ∃ a : K, a ≠ 0 ∧ a ≠ 1 := by
  classical
  let := Fintype.ofFinite K
  have h : ({0, 1} : Finset K).card < (Finset.univ : Finset K).card := by
    simpa [Nat.card_eq_fintype_card] using hcard
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card h
  exact ⟨a, by simpa using ha⟩

lemma firstPreimage_displacements (hcard : 2 < Nat.card K)
    (v : Space (K := K)) (hv : v ∈ firstPreimage) :
    ∃ (t : K) (u w : Space (K := K)),
      v = (action (element hcard 1) u - u) + (action (element hcard t) w - w) := by
  obtain ⟨a, ha, ha1⟩ := exists_parameter hcard
  obtain ⟨b, hb⟩ := (mem_firstPreimage v).mp hv
  have hd : a ^ 2 - a ≠ 0 := by
    rw [show a ^ 2 - a = a * (a - 1) by ring]
    exact mul_ne_zero ha (sub_ne_zero.mpr ha1)
  let z := (b - v.2) / (a ^ 2 - a)
  let y := v.2 - a * z
  refine ⟨a ^ 2, (y • ClassicalOrthogonal.f 0, 0),
    (z • ClassicalOrthogonal.f 0, 0), ?_⟩
  rw [displacement, displacement]
  have hb' : b = y + a ^ 2 * z := by
    dsimp [y, z]
    field_simp [hd]
    ring
  apply Prod.ext
  · rw [← hb]
    simp only [vector, Prod.fst_add, Prod.smul_fst, Pi.smul_apply, ClassicalOrthogonal.f,
      Pi.single_eq_same, smul_eq_mul, mul_one, one_smul, ← add_smul, smul_smul]
    rw [hb', mul_comm z]
  · simp [vector, ClassicalOrthogonal.f, sqrt, frobeniusEquiv_symm_pow, y, mul_comm]

lemma root_commutator (hcard : 2 < Nat.card K) :
    Coinvariants.ker (action.comp (group (K := K)).subtype) = firstPreimage := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, v⟩, rfl⟩
    obtain ⟨t, ht⟩ := (mem_group hcard g.val).mp g.property
    change action g.val v - v ∈ firstPreimage
    rw [← ht]
    exact rootDisplacement_le_firstPreimage hcard t ⟨v, rfl⟩
  · intro v hv
    obtain ⟨t, u, w, hv⟩ := firstPreimage_displacements hcard v hv
    rw [hv]
    exact Submodule.add_mem _
      (Coinvariants.sub_mem_ker (ρ := action.comp (group (K := K)).subtype)
        ⟨element hcard 1, element_mem_group hcard 1⟩ u)
      (Coinvariants.sub_mem_ker (ρ := action.comp (group (K := K)).subtype)
        ⟨element hcard t, element_mem_group hcard t⟩ w)

section Binary
variable [Algebra (ZMod 2) K]

lemma cover_root_geometry (hcard : 2 < Nat.card K)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (L (K := K)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := K))) (hp : IsCover p) :
    fixed σ ≤ (firstLine.restrictScalars (ZMod 2)).comap p.toLinearMap ∧
      (firstLine.restrictScalars (ZMod 2)).comap p.toLinearMap =
        Coinvariants.ker (σ.comp group.subtype) ∧
      (firstLine.restrictScalars (ZMod 2)).comap p.toLinearMap ≤
        fixed (σ.comp group.subtype) := by
  obtain ⟨f, hf, hover⟩ := exists_cover_quotient p hp
  refine ⟨fixed_le_preimage p _ (by rw [binary_natural_fixed]; exact bot_le), ?_⟩
  apply preimage_root_geometry_of_surjective binaryProjection p f hf hover group
  · change (firstPreimage (K := K)).restrictScalars (ZMod 2) =
      Coinvariants.ker (restrictScalars (k := ZMod 2)
        ((action (K := K)).comp (group (K := K)).subtype))
    rw [coinvariants_restrictScalars, root_commutator hcard]
  · exact firstPreimage_fixed hcard

end Binary

end Representation.SymplecticFourOrthogonalCover.Roots
