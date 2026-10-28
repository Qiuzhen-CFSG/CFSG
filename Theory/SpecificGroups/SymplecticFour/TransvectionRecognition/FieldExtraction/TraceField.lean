module
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.FieldExtraction.RankOneSchur
public import Theory.Representation.CoefficientDescent
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.BaseChange
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# Trace-field coordinates for rank-one symplectic actions

For an irreducible action containing a rank-one displacement, write that
operator as `u ⊗ l`. The values `l (g u)` are differences of group traces.
Symplectic invariance makes `l` a nonzero scalar multiple of pairing with `u`.
An orbit basis therefore has its normalized Gram matrix over the trace field.
Inverting this Gram matrix puts every action matrix over the same field.

This gives a direct field-of-definition step for Aschbacher--Smith G.4.8,
printed pp.340--341, retaining the actual coefficient field and avoiding any
assumption of irreducibility over its prime subfield.
-/

@[expose] public noncomputable section
open Module Matrix
namespace Representation.TraceFieldDescent
variable {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

omit [FiniteDimensional F V] in
theorem exists_smulRight_of_rank_one (N : Module.End F V)
    (hr : finrank F (LinearMap.range N) = 1) :
    ∃ (u : V) (l : Module.Dual F V), u ≠ 0 ∧ l ≠ 0 ∧ N = l.smulRight u := by
  have hn : LinearMap.range N ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hr
    exact Nat.zero_ne_one hr
  obtain ⟨u,hu,hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  have he := eq_span_singleton_of_mem_of_finrank_eq_one hr hu hu0
  let L : V →ₗ[F] (F ∙ u) := N.codRestrict (F ∙ u) (fun v => he ▸ N.mem_range_self v)
  let l : Module.Dual F V := (LinearEquiv.coord F V u hu0).toLinearMap.comp L
  have hN : N = l.smulRight u := by
    ext v
    exact (LinearEquiv.coord_apply_smul F V u hu0 (L v)).symm
  refine ⟨u,l,hu0,?_,hN⟩
  intro h
  apply hn
  rw [hN,h]
  simp

omit [FiniteDimensional F V] in
theorem span_orbit_eq_top (ρ : Representation F G V) [ρ.IsIrreducible]
    (u : V) (hu : u ≠ 0) : Submodule.span F (Set.range (fun g => ρ g u)) = ⊤ := by
  let W : Subrepresentation ρ := {
    toSubmodule := Submodule.span F (Set.range (fun g => ρ g u))
    apply_mem_toSubmodule g x hx := by
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨h,rfl⟩ := hy
        exact Submodule.subset_span ⟨g*h, by simp⟩
      | zero => simp
      | add x y hx hy hix hiy => simpa only [map_add] using Submodule.add_mem _ hix hiy
      | smul c x hx hix => simpa only [map_smul] using Submodule.smul_mem _ c hix }
  rcases (inferInstance : ρ.IsIrreducible).eq_bot_or_eq_top W with hw | hw
  · have huW : u ∈ W := by
      change u ∈ Submodule.span F (Set.range (fun g => ρ g u))
      exact Submodule.subset_span ⟨1,by simp⟩
    rw [hw] at huW
    exact (hu huW).elim
  · exact congrArg Subrepresentation.toSubmodule hw

theorem rank_one_trace (ρ : Representation F G V) (t : G)
    (u : V) (l : Module.Dual F V) (hN : ρ t - 1 = l.smulRight u) (g : G) :
    l (ρ g u) = LinearMap.trace F V (ρ (t*g)) - LinearMap.trace F V (ρ g) := by
  have he : (ρ t-1)*ρ g = (l.comp (ρ g)).smulRight u := by
    rw [hN]
    ext v
    rfl
  calc
    l (ρ g u) = LinearMap.trace F V ((l.comp (ρ g)).smulRight u) :=
      (LinearMap.trace_smulRight (l.comp (ρ g)) u).symm
    _ = LinearMap.trace F V ((ρ t-1)*ρ g) := congrArg (LinearMap.trace F V) he.symm
    _ = LinearMap.trace F V (ρ (t*g)) - LinearMap.trace F V (ρ g) := by
      rw [sub_mul,one_mul,←map_mul,map_sub]

omit [FiniteDimensional F V] in
theorem functional_eq_form (ρ : Representation F G V) (t : G)
    (u : V) (hu : u ≠ 0) (l : Module.Dual F V) (hl : l ≠ 0)
    (hN : ρ t - 1 = l.smulRight u)
    (B : LinearMap.BilinForm F V) (halt : B.IsAlt) (hB : B.Nondegenerate)
    (hp : ∀ x y, B (ρ t x) (ρ t y) = B x y) :
    ∃ c : F, c ≠ 0 ∧ ∀ y, l y = c * B u y := by
  have ht (v : V) : ρ t v = v + l v • u := by
    have h := LinearMap.congr_fun hN v
    change ρ t v - v = l v • u at h
    exact sub_eq_iff_eq_add.mp h |>.trans (add_comm _ _)
  have he (x y : V) : l x * B u y = l y * B u x := by
    have h := hp x y
    rw [ht,ht] at h
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, halt.self_eq_zero, mul_zero, add_zero] at h
    rw [←halt.neg_eq u x] at h
    linear_combination h
  obtain ⟨x,hx⟩ : ∃ x, B u x ≠ 0 := by
    by_contra! h
    exact hu (hB.1 u h)
  have hlx : l x ≠ 0 := by
    intro hz
    apply hl
    ext y
    have hh := he x y
    rw [hz,zero_mul] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_right hx
  refine ⟨l x / B u x, div_ne_zero hlx hx, fun y => ?_⟩
  apply (mul_right_cancel₀ hx)
  calc
    l y * B u x = l x * B u y := (he x y).symm
    _ = (l x / B u x * B u y) * B u x := by field_simp

theorem exists_orbit_basis (ρ : Representation F G V) [ρ.IsIrreducible]
    (u : V) (hu : u ≠ 0) :
    ∃ b : Basis (Fin (finrank F V)) F V, ∀ i, ∃ g : G, b i = ρ g u := by
  classical
  have hs := (span_orbit_eq_top ρ u hu).ge
  let b := Basis.ofSpan hs
  let b' := b.reindex (b.indexEquiv (Module.finBasis F V))
  refine ⟨b',fun i => ?_⟩
  have h := Basis.ofSpan_subset hs (Set.mem_range_self ((b.indexEquiv (Module.finBasis F V)).symm i))
  obtain ⟨g,hg⟩ := h
  exact ⟨g,by simpa only [b', Basis.reindex_apply, b] using hg.symm⟩

omit [FiniteDimensional F V] in
theorem repr_mem_of_pairings {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Subfield F) (b : Basis ι F V) (B : LinearMap.BilinForm F V)
    (hB : B.Nondegenerate) (hK : ∀ i j, B (b i) (b j) ∈ K)
    (v : V) (hv : ∀ i, B (b i) v ∈ K) : ∀ i, b.repr v i ∈ K := by
  let A := LinearMap.BilinForm.toMatrix b B
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr
    ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hB)
  have hA : ∀ i j, A i j ∈ K := by
    simpa only [A, LinearMap.BilinForm.toMatrix_apply] using hK
  have hinv : ∀ i j, A⁻¹ i j ∈ K :=
    Matrix.mem_subfield_of_mul_eq_one_of_mem_subfield_right (_root_.Equiv.refl ι) K
      (Matrix.mul_nonsing_inv A hu) hA
  have hm : A *ᵥ (fun i => b.repr v i) = (fun i => B (b i) v) := by
    ext i
    simp only [Matrix.mulVec, dotProduct, A, LinearMap.BilinForm.toMatrix_apply]
    conv_rhs => rw [←b.sum_repr v]
    simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
  have he := congrArg (fun y => A⁻¹ *ᵥ y) hm
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hu, Matrix.one_mulVec] at he
  intro i
  rw [congrFun he i]
  exact K.sum_mem (fun j _ => K.mul_mem (hinv i j) (hv j))

/-- Traces determine a basis of definition and the compatible alternating
form for an irreducible symplectic action containing a rank-one actor. -/
theorem exists_basis_over_trace_subfield
    (ρ : Representation F G V) [ρ.IsIrreducible] (t : G)
    (hr : finrank F (LinearMap.range (ρ t-1)) = 1)
    (B : LinearMap.BilinForm F V) (halt : B.IsAlt) (hB : B.Nondegenerate)
    (hp : ∀ g x y, B (ρ g x) (ρ g y) = B x y)
    (K : Subfield F) (hK : ∀ g, LinearMap.trace F V (ρ g) ∈ K) :
    ∃ (b : Basis (Fin (finrank F V)) F V) (c : F), c ≠ 0 ∧
      (∀ i j, (c • B) (b i) (b j) ∈ K) ∧
      (∀ g i j, LinearMap.toMatrix b b (ρ g) i j ∈ K) := by
  classical
  obtain ⟨u,l,hu,hl,hN⟩ := exists_smulRight_of_rank_one (ρ t-1) hr
  obtain ⟨c,hc,hcl⟩ := functional_eq_form ρ t u hu l hl hN B halt hB (hp t)
  obtain ⟨b,hb⟩ := exists_orbit_basis ρ u hu
  have hpair (g h : G) : (c • B) (ρ g u) (ρ h u) ∈ K := by
    have he : B (ρ g u) (ρ h u) = B u (ρ (g⁻¹*h) u) := by
      have hh := hp g⁻¹ (ρ g u) (ρ h u)
      simpa only [ρ.inv_self_apply, ←Module.End.mul_apply, ←map_mul] using hh.symm
    change c * B (ρ g u) (ρ h u) ∈ K
    rw [he,←hcl,rank_one_trace ρ t u l hN]
    exact K.sub_mem (hK _) (hK _)
  have hform : ∀ i j, (c • B) (b i) (b j) ∈ K := by
    intro i j
    obtain ⟨g,hg⟩ := hb i
    obtain ⟨h,hh⟩ := hb j
    rw [hg,hh]
    exact hpair g h
  have hnondeg : (c • B).Nondegenerate := by
    constructor
    · intro x hx
      exact hB.1 x (fun y => (mul_eq_zero.mp (hx y)).resolve_left hc)
    · intro y hy
      exact hB.2 y (fun x => (mul_eq_zero.mp (hy x)).resolve_left hc)
  refine ⟨b,c,hc,hform,fun g i j => ?_⟩
  rw [LinearMap.toMatrix_apply]
  exact repr_mem_of_pairings K b (c • B) hnondeg hform (ρ g (b j)) (fun k => by
    obtain ⟨a,ha⟩ := hb k
    obtain ⟨d,hd⟩ := hb j
    rw [ha,hd,←Module.End.mul_apply,←map_mul]
    exact hpair a (g*d)) i

end Representation.TraceFieldDescent
