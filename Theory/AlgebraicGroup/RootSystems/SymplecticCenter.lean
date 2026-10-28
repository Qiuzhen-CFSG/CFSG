module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.ClassicalPointGroups
public import Mathlib.LinearAlgebra.Center
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
This module computes the center of the standard symplectic point group.  For
the canonical form represented by `Matrix.J`, every central isometry is scalar
and its scalar squares to one; consequently the center is finite (in fact it
has at most the two elements `1` and `-1`).  The result is stated for the
`bilinearIsometrySubgroup` used by the concrete algebraic-group model, so a
point-group equivalence can transport it directly to the carrier variety.

The proof is characteristic-free.  For an alternating form `B`, the rank-one
map `x ↦ x + B(v, x) • v` is a symplectic transvection.  A central isometry
commutes with every such map.  Nondegeneracy then forces its value on each
vector to lie in that vector's span, and the linear-center lemma identifies it
with a scalar map.  Evaluating preservation of the standard form on one
hyperbolic pair shows that the scalar has square one.  This is the standard
linear-algebra calculation of the center of a symplectic group; no structural
semisimplicity or center-finiteness theorem is used.
-/

namespace Theory.AlgebraicGroup

open scoped BigOperators

universe u v


variable {k : Type u} [Field k]

/-- The canonical symplectic bilinear form on two copies of `Fin m → k`. -/
public abbrev standardSymplecticBilinForm (m : ℕ) :
    LinearMap.BilinForm k ((Fin m ⊕ Fin m) → k) :=
  Matrix.toBilin' (Matrix.J (Fin m) k)

private lemma standardSymplecticBilinForm_apply (m : ℕ)
    (x y : (Fin m ⊕ Fin m) → k) :
    standardSymplecticBilinForm (k := k) m x y =
      ∑ i : Fin m, (x (.inr i) * y (.inl i) - x (.inl i) * y (.inr i)) := by
  simp [standardSymplecticBilinForm, Matrix.toBilin'_apply, Matrix.J,
    Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.one_apply,
    mul_ite]
  ring

private lemma standardSymplecticBilinForm_isAlt (m : ℕ) :
    (standardSymplecticBilinForm (k := k) m).IsAlt := by
  intro x
  rw [standardSymplecticBilinForm_apply]
  simp [mul_comm]

private lemma standardSymplecticBilinForm_nondegenerate (m : ℕ) :
    (standardSymplecticBilinForm (k := k) m).Nondegenerate := by
  apply Matrix.Nondegenerate.toBilin'
  rw [Matrix.nondegenerate_iff_det_ne_zero]
  exact (Matrix.isUnit_det_J (Fin m) k).ne_zero

private def symplecticTransvection
    {V : Type u} [AddCommGroup V] [Module k V]
    (B : LinearMap.BilinForm k V) (hB : B.IsAlt) (v : V) :
    bilinearIsometrySubgroup B := by
  let t := LinearEquiv.transvection (hB.self_eq_zero v)
  refine ⟨t, (mem_bilinearIsometrySubgroup B t).2 ?_⟩
  intro x y
  simp only [t, LinearEquiv.transvection.apply]
  change B (x + B v x • v) (y + B v y • v) = B x y
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply]
  rw [hB.self_eq_zero, smul_zero, add_zero]
  rw [← hB.neg_eq v x]
  simp only [smul_eq_mul]
  ring

private lemma center_bilinearIsometry_eq_smul
    {V : Type u} [AddCommGroup V] [Module k V]
    (B : LinearMap.BilinForm k V) (hB : B.IsAlt) (hBnd : B.Nondegenerate)
    (g : Subgroup.center (bilinearIsometrySubgroup B)) :
    ∃ a : k, (g.1.1 : V →ₗ[k] V) = a • LinearMap.id := by
  have hspan (v : V) : g.1.1 v ∈ k ∙ v := by
    by_cases hv : v = 0
    · subst v
      simp
    · have hex : ∃ x : V, B v x ≠ 0 := by
        by_contra h
        apply hv
        apply hBnd.1 v
        intro x
        by_contra hx
        exact h ⟨x, hx⟩
      obtain ⟨x, hx⟩ := hex
      let t := symplecticTransvection B hB v
      have hcomm := congrArg (fun e : bilinearIsometrySubgroup B => e.1 x)
        ((Subgroup.mem_center_iff.mp g.2) t)
      simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, map_add, map_smul,
        t, symplecticTransvection, LinearEquiv.transvection.apply] at hcomm
      have hrelation : B v (g.1.1 x) • v = B v x • g.1.1 v :=
        add_left_cancel hcomm
      refine Submodule.mem_span_singleton.mpr ⟨(B v x)⁻¹ * B v (g.1.1 x), ?_⟩
      calc
        ((B v x)⁻¹ * B v (g.1.1 x)) • v =
            (B v x)⁻¹ • (B v (g.1.1 x) • v) := by rw [smul_smul]
        _ = (B v x)⁻¹ • (B v x • g.1.1 v) := by rw [hrelation]
        _ = ((B v x)⁻¹ * B v x) • g.1.1 v := by rw [smul_smul]
        _ = g.1.1 v := by simp [hx]
  apply LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
  intro v hli
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hspan v)
  have hzero : (-a) • v + (1 : k) • g.1.1 v = 0 := by
    rw [← ha]
    simp
  exact one_ne_zero ((LinearIndependent.pair_iff.mp hli) (-a) 1 hzero).2

private lemma standardSymplecticBilinForm_hyperbolicPair (m : ℕ) (i : Fin m) :
    standardSymplecticBilinForm (k := k) m
        (Pi.single (.inr i) 1) (Pi.single (.inl i) 1) = 1 := by
  rw [standardSymplecticBilinForm_apply]
  classical
  simp [Pi.single_apply, Sum.inr.injEq, Sum.inl.injEq]

private lemma center_standardSymplectic_exists_scalar
    (m : ℕ) (hm : 0 < m)
    (g : Subgroup.center
      (bilinearIsometrySubgroup (standardSymplecticBilinForm (k := k) m))) :
    ∃ a : k, a ^ 2 = 1 ∧
      ∀ v, g.1.1 v = a • v := by
  obtain ⟨a, ha⟩ := center_bilinearIsometry_eq_smul
    (standardSymplecticBilinForm (k := k) m)
    (standardSymplecticBilinForm_isAlt m)
    (standardSymplecticBilinForm_nondegenerate m) g
  refine ⟨a, ?_, fun v => ?_⟩
  · let i : Fin m := ⟨0, hm⟩
    let e₁ : (Fin m ⊕ Fin m) → k := Pi.single (.inr i) 1
    let e₂ : (Fin m ⊕ Fin m) → k := Pi.single (.inl i) 1
    have ha_apply (v : (Fin m ⊕ Fin m) → k) : g.1.1 v = a • v := by
      exact DFunLike.congr_fun ha v
    have hisom := (mem_bilinearIsometrySubgroup
      (standardSymplecticBilinForm (k := k) m) g.1).1 g.1.2 e₁ e₂
    rw [ha_apply, ha_apply] at hisom
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at hisom
    rw [show standardSymplecticBilinForm (k := k) m e₁ e₂ = 1 by
      exact standardSymplecticBilinForm_hyperbolicPair m i] at hisom
    simpa [pow_two] using hisom
  · exact DFunLike.congr_fun ha v

/-- A standard symplectic isometry is central exactly when it is scalar by a
square root of one. -/
public theorem mem_center_standardSymplectic_iff
    (m : ℕ) (hm : 0 < m)
    (g : bilinearIsometrySubgroup
      (standardSymplecticBilinForm (k := k) m)) :
    g ∈ Subgroup.center
        (bilinearIsometrySubgroup (standardSymplecticBilinForm (k := k) m)) ↔
      ∃ a : k, a ^ 2 = 1 ∧ ∀ v, g.1 v = a • v := by
  constructor
  · intro hg
    exact center_standardSymplectic_exists_scalar m hm ⟨g, hg⟩
  · rintro ⟨a, -, ha⟩
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change h.1 (g.1 v) = g.1 (h.1 v)
    rw [ha, map_smul, ha]

/-- For positive rank, the center of the standard symplectic point group is
finite by the scalar-square calculation below. -/
private theorem standardSymplectic_center_finite_pos
    (m : ℕ) (hm : 0 < m) :
    Finite (Subgroup.center
      (bilinearIsometrySubgroup (standardSymplecticBilinForm (k := k) m))) := by
  let scalar (g : Subgroup.center
      (bilinearIsometrySubgroup (standardSymplecticBilinForm (k := k) m))) : k :=
    Classical.choose (center_standardSymplectic_exists_scalar m hm g)
  have scalar_sq (g : Subgroup.center
      (bilinearIsometrySubgroup (standardSymplecticBilinForm (k := k) m))) :
      scalar g ^ 2 = 1 :=
    (Classical.choose_spec
      (center_standardSymplectic_exists_scalar m hm g)).1
  have scalar_apply (g : Subgroup.center
      (bilinearIsometrySubgroup (standardSymplecticBilinForm (k := k) m))) (v) :
      g.1.1 v = scalar g • v :=
    (Classical.choose_spec
      (center_standardSymplectic_exists_scalar m hm g)).2 v
  let signScalars := {a : k // a ∈ ({1, -1} : Set k)}
  let _ : Finite signScalars := by
    dsimp only [signScalars]
    infer_instance
  let toScalar : Subgroup.center
      (bilinearIsometrySubgroup (standardSymplecticBilinForm (k := k) m)) →
      signScalars := fun g => ⟨scalar g, by simpa [sq_eq_one_iff] using scalar_sq g⟩
  apply Finite.of_injective toScalar
  intro g h hgh
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  rw [scalar_apply, scalar_apply]
  have hs : scalar g = scalar h := congrArg (fun a : signScalars => (a : k)) hgh
  rw [hs]

/- The rank-zero carrier is trivial; positive ranks use the scalar-square
description above. -/
public theorem standardSymplectic_center_finite_all
    (m : ℕ) :
    Finite (Subgroup.center
      (bilinearIsometrySubgroup (standardSymplecticBilinForm (k := k) m))) := by
  by_cases hm : m = 0
  · subst m
    exact Finite.of_subsingleton
  · exact standardSymplectic_center_finite_pos m (Nat.pos_of_ne_zero hm)

/- Compatibility wrapper retaining the former rank-at-least-three statement. -/
public theorem standardSymplectic_center_finite
    (m : ℕ) (_hm : 3 ≤ m) :
    Finite (Subgroup.center
      (bilinearIsometrySubgroup (standardSymplecticBilinForm (k := k) m))) := by
  exact standardSymplectic_center_finite_all m

/-- Center finiteness transfers from the standard symplectic point group across
any multiplicative equivalence, in particular across the point equivalence of
a concrete symplectic carrier variety. -/
public theorem finite_center_of_mulEquiv_standardSymplectic
    {G : Type v} [Group G] (m : ℕ) (_hm : 3 ≤ m)
    (e : G ≃* bilinearIsometrySubgroup
      (standardSymplecticBilinForm (k := k) m)) :
    Finite (Subgroup.center G) := by
  let _ : Finite (Subgroup.center
      (bilinearIsometrySubgroup (standardSymplecticBilinForm (k := k) m))) :=
    standardSymplectic_center_finite_all m
  exact Finite.of_injective (Subgroup.centerCongr e) (Subgroup.centerCongr e).injective

/- Center finiteness transfers across any multiplicative equivalence in every
rank. -/
public theorem finite_center_of_mulEquiv_standardSymplectic_all
    {G : Type v} [Group G] (m : ℕ)
    (e : G ≃* bilinearIsometrySubgroup
      (standardSymplecticBilinForm (k := k) m)) :
    Finite (Subgroup.center G) := by
  let _ : Finite (Subgroup.center
      (bilinearIsometrySubgroup (standardSymplecticBilinForm (k := k) m))) :=
    standardSymplectic_center_finite_all m
  exact Finite.of_injective (Subgroup.centerCongr e) (Subgroup.centerCongr e).injective

end Theory.AlgebraicGroup
