module

public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.QuotientConstruction.AffineQuotient
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.QuotientConstruction.AffineCoverage.Geometry
public import Mathlib.LinearAlgebra.Determinant

/-!
# Affine coverage of the native M₂₄ trio stabilizer

Every element stabilizing the literal standard trio permutes its three octads
and acts on their checked binary coordinates with a common linear part.
The native octads supported on two trio parts detect equality of vector
differences. Preserving these octads forces the three local actions, after
subtracting their values at zero, to agree and to be additive. Their common
map is bijective and hence has determinant one over F₂.

This proves the `AffineCoverage` input of the quotient construction. Source
context: Aschbacher, *Sporadic Groups*, Chapter 7, Lemma 20.2, printed p.97;
GLS3, Table 5.3e. The full stabilizer structure is assembled separately.
-/

open scoped Pointwise
namespace Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction

private theorem octad_injective : Function.Injective standardTrioOctad := by
  intro i j h
  apply (point_mem_octad_iff i j 0).mp
  rw [← h]
  exact point_mem_octad _ _

private theorem smul_block_mem (g : M24) {B : Finset (Fin 24)} (hB : B ∈ m24Blocks) :
    g • B ∈ m24Blocks := by
  have h := (mem_M24_iff g.val).mp g.property
  change g.val • B ∈ (m24Blocks : Set (Finset (Fin 24)))
  rw [← h]
  exact Set.smul_mem_smul_set hB

private theorem coordinate_action (g : trioStabilizer standardTrio) :
    ∃ (s : Equiv.Perm (Fin 3)) (f : Fin 3 → Vector → Vector),
      (∀ i, g.val • standardTrioOctad i = standardTrioOctad (s i)) ∧
      (∀ i v, g.val.val (point (i,v)) = point (s i, f i v)) := by
  classical
  have hp (i : Fin 3) : ∃ j, g.val • standardTrioOctad i = standardTrioOctad j := by
    have h := (mem_trioStabilizer_iff standardTrio g.val).mp g.property
      (standardTrioOctad i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
    exact ⟨j, hj.symm⟩
  choose s hs using hp
  have hinj : Function.Injective s := by
    intro i j hij
    apply octad_injective
    have h : g.val • standardTrioOctad i = g.val • standardTrioOctad j := by
      rw [hs i, hs j, hij]
    exact (MulAction.injective g.val) h
  let σ : Equiv.Perm (Fin 3) := Equiv.ofBijective s
    ⟨hinj, Finite.surjective_of_injective hinj⟩
  let f : Fin 3 → Vector → Vector := fun i v => (point.symm (g.val.val (point (i,v)))).2
  refine ⟨σ, f, hs, ?_⟩
  intro i v
  let p := point.symm (g.val.val (point (i,v)))
  have he : point p = g.val.val (point (i,v)) := point.apply_symm_apply _
  have hm : point p ∈ standardTrioOctad (s i) := by
    rw [he, ← hs i]
    exact Finset.smul_mem_smul_finset (point_mem_octad i v)
  have hfst : p.1 = s i := (point_mem_octad_iff _ _ _).mp hm
  exact he.symm.trans (congrArg point (Prod.ext hfst rfl))

private theorem differences_preserved (g : trioStabilizer standardTrio)
    (s : Equiv.Perm (Fin 3)) (f : Fin 3 → Vector → Vector)
    (hs : ∀ i, g.val • standardTrioOctad i = standardTrioOctad (s i))
    (hf : ∀ i v, g.val.val (point (i,v)) = point (s i, f i v))
    (i j : Fin 3) (hij : i ≠ j) (u v w z : Vector) (he : u + v = w + z) :
    f i u + f i v = f j w + f j z := by
  apply (CoverageGeometry.same_difference_iff (s i) (s j)
    (fun h => hij (s.injective h)) _ _ _ _).mpr
  intro B hB hsub
  let C := g.val⁻¹ • B
  have hC : C ∈ m24Blocks := smul_block_mem g.val⁻¹ hB
  have hCsub : C ⊆ standardTrioOctad i ∪ standardTrioOctad j := by
    apply Finset.subset_smul_finset_iff.mp
    simpa only [Finset.smul_finset_union, hs] using hsub
  have h := (CoverageGeometry.same_difference_iff i j hij u v w z).mp he C hC hCsub
  have hm (a : Fin 3) (x : Vector) :
      point (s a, f a x) ∈ B ↔ point (a,x) ∈ C := by
    rw [← hf a x]
    exact (Finset.mem_inv_smul_finset_iff (a := g.val)).symm
  simpa only [hm] using h

private theorem binary_add_self (v : Vector) : v + v = 0 := by
  ext k
  exact (show ∀ a : ZMod 2, a + a = 0 by decide) (v k)

/-- Every permutation in the native standard-trio stabilizer has the shared
coordinate formula with one octad permutation and one special linear part. -/
public theorem affineCoverage : AffineCoverage := by
  intro g
  obtain ⟨s, f, hs, hf⟩ := coordinate_action g
  have hd := differences_preserved g s f hs hf
  let l : Vector → Vector := fun v => f 0 v + f 0 0
  have hc (i : Fin 3) (v : Vector) : f i v + f i 0 = l v := by
    by_cases hi : i = 0
    · subst i; rfl
    · exact hd i 0 hi v 0 v 0 rfl
  have hz : l 0 = 0 := binary_add_self _
  have ha (u v : Vector) : l (u + v) = l u + l v := by
    calc
      l (u + v) = f 1 u + f 1 v := hd 0 1 (by decide) (u + v) 0 u v (by simp)
      _ = (f 1 u + f 1 0) + (f 1 v + f 1 0) := by
        rw [add_add_add_comm, binary_add_self, add_zero]
      _ = l u + l v := by rw [hc, hc]
  let L : Vector →ₗ[ZMod 2] Vector :=
    { toFun := l
      map_add' := ha
      map_smul' := by
        intro a v
        have h : a = 0 ∨ a = 1 := (show ∀ a : ZMod 2, a = 0 ∨ a = 1 by decide) a
        rcases h with rfl | rfl
        · simpa using hz
        · simp }
  have hfi (i : Fin 3) : Function.Injective (f i) := by
    intro u v huv
    have h : g.val.val (point (i,u)) = g.val.val (point (i,v)) := by rw [hf, hf, huv]
    exact congrArg Prod.snd (point.injective (g.val.val.injective h))
  have hL : Function.Injective L := by
    intro u v huv
    exact hfi 0 (add_right_cancel huv)
  let e : Vector ≃ₗ[ZMod 2] Vector :=
    LinearEquiv.ofBijective L ⟨hL, Finite.surjective_of_injective hL⟩
  let A := LinearMap.toMatrix' L
  have hdet : A.det = 1 := by
    have hu : IsUnit A.det := by
      rw [LinearMap.det_toMatrix']
      exact e.isUnit_det'
    have hne : A.det ≠ 0 := hu.ne_zero
    exact (show ∀ x : ZMod 2, x ≠ 0 → x = 1 by decide) _ hne
  let q : QuotientModel := (s, ⟨A, hdet⟩)
  refine ⟨q, fun i => f i 0, ?_⟩
  intro i v
  rw [hf]
  apply congrArg point
  refine Prod.ext rfl ?_
  change f i v = Matrix.toLin' (LinearMap.toMatrix' L) v + f i 0
  rw [Matrix.toLin'_toMatrix']
  change f i v = l v + f i 0
  rw [← hc i v, add_assoc, binary_add_self, add_zero]

end Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
