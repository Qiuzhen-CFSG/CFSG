module

public import Theory.AlgebraicGroup.RootSystems.TypeE8RootPairing
public import Mathlib.Data.ZMod.QuotientGroup

/-!
# The standard root pairing of type E7

The E7 roots are the E8 roots orthogonal to `e₀ + e₁`.  We use the resulting
seven-dimensional hyperplane as both root and coroot space, with the Euclidean
pairing.  Reflection stability is inherited from the explicit E8 reflection
calculation and the hyperplane equation; all roots have squared length two.
The displayed seven simple roots are linearly independent, span this
hyperplane, and have the exact Cartan matrix declared in `Exceptional.lean`.

The final section records the integral Cartan-coordinate lattice: the root
lattice is the kernel of the mod-two character `x₃ + x₄ + x₆`, hence the
weight/root quotient is canonically `ZMod 2`.  These statements are purely
coordinate calculations and do not use algebraic-group classification or
Chevalley existence results.
-/

namespace Theory.AlgebraicGroup.StandardRootSystem

open Set Submodule
open scoped BigOperators

private lemma dot_add_left_E7 (x y z : Vec 8) :
    dot (x + y) z = dot x z + dot y z := by
  simp [dot, add_mul, Finset.sum_add_distrib]

private lemma dot_sub_left_E7 (x y z : Vec 8) :
    dot (x - y) z = dot x z - dot y z := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]

private lemma dot_smul_left_E7 (c : ℝ) (x y : Vec 8) :
    dot (c • x) y = c * dot x y := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma dot_smul_right_E7 (c : ℝ) (x y : Vec 8) :
    dot x (c • y) = c * dot x y := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma dot_add_right_E7 (x y z : Vec 8) :
    dot x (y + z) = dot x y + dot x z := by
  rw [dot_comm, dot_add_left_E7, dot_comm y x, dot_comm z x]

private lemma dot_sub_right_E7 (x y z : Vec 8) :
    dot x (y - z) = dot x y - dot x z := by
  rw [dot_comm, dot_sub_left_E7, dot_comm y x, dot_comm z x]

private lemma dot_self_eq_zero_E7 {x : Vec 8} (h : dot x x = 0) : x = 0 := by
  funext i
  have hs : ∑ j, x j * x j = 0 := by simpa [dot] using h
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (x j))).mp hs i
    (Finset.mem_univ i)
  exact (mul_self_eq_zero.mp hi)

private lemma dot_neg_left_E7 (x y : Vec 8) : dot (-x) y = -dot x y := by
  simp [dot, Finset.sum_neg_distrib]

private lemma dot_basisVector_left_E7 (i : Fin 8) (x : Vec 8) :
    dot (basisVector i) x = x i := by
  classical
  simp [dot, basisVector, Pi.single_apply]

private lemma dot_basisVector_right_E7 (x : Vec 8) (i : Fin 8) :
    dot x (basisVector i) = x i := by
  rw [dot_comm, dot_basisVector_left_E7]

private lemma dot_smul_self_E7 (c : ℝ) (x : Vec 8) :
    dot (c • x) (c • x) = c ^ 2 * dot x x := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

public theorem typeE7Roots_finite : typeE7Roots.Finite := by
  exact typeE8Roots_finite.subset (by
    intro x hx
    exact hx.1)

public instance typeE7Roots_finiteType : Finite typeE7Roots :=
  Set.finite_coe_iff.mpr typeE7Roots_finite

/- The hyperplane carrying the E7 root system. -/
@[expose] public noncomputable def typeE7Space : Submodule ℝ (Vec 8) :=
  LinearMap.ker ((dotProductEquiv ℝ (Fin 8)).toLinearMap.flip
    (basisVector 0 + basisVector 1))

@[expose] public noncomputable def typeE7RootEmbedding : typeE7Roots ↪ typeE7Space :=
  ⟨fun r => ⟨r.1, by
    change dot r.1 (basisVector 0 + basisVector 1) = 0
    exact r.2.2⟩, by
      intro r s h
      apply Subtype.ext
      exact congrArg (fun z : typeE7Space => z.1) h⟩

@[simp] public lemma typeE7RootEmbedding_apply (r : typeE7Roots) :
    (typeE7RootEmbedding r : typeE7Space) = ⟨r.1, r.2.2⟩ := rfl

private lemma typeE7Space_coe_nsmul (n : ℕ) (x : typeE7Space) :
    ((n • x : typeE7Space) : Vec 8) = n • (x : Vec 8) := by
  rfl

private lemma typeE7Space_coe_neg (x : typeE7Space) :
    ((-x : typeE7Space) : Vec 8) = -(x : Vec 8) := by
  rfl

private lemma typeE7Space_coe_sum (f : Fin 7 → typeE7Space) :
    ((∑ i, f i : typeE7Space) : Vec 8) = ∑ i, (f i : Vec 8) := by
  rfl

@[expose] public noncomputable def typeE7CoordinatePairing :
    typeE7Space →ₗ[ℝ] typeE7Space →ₗ[ℝ] ℝ :=
  { toFun := fun x =>
      { toFun := fun y => dot x.1 y.1
        map_add' := by
          intro y z
          change dot x.1 (y.1 + z.1) = dot x.1 y.1 + dot x.1 z.1
          exact dot_add_right_E7 _ _ _
        map_smul' := by
          intro c y
          change dot x.1 (c • y.1) = c * dot x.1 y.1
          exact dot_smul_right_E7 _ _ _ }
    map_add' := by
      intro x y
      ext z
      change dot (x.1 + y.1) z.1 = dot x.1 z.1 + dot y.1 z.1
      exact dot_add_left_E7 _ _ _
    map_smul' := by
      intro c x
      ext y
      change dot (c • x.1) y.1 = c * dot x.1 y.1
      exact dot_smul_left_E7 _ _ _ }

public instance typeE7CoordinatePairing_isPerfPair :
    typeE7CoordinatePairing.IsPerfPair := by
  apply LinearMap.IsPerfPair.of_injective
  · intro x y h
    have hsub : typeE7CoordinatePairing (x - y) = 0 := by
      rw [map_sub, h, sub_self]
    have hh := LinearMap.congr_fun hsub (x - y)
    have hz : dot (x.1 - y.1) (x.1 - y.1) = 0 := by
      simpa [typeE7CoordinatePairing, dot_sub_left_E7, dot_sub_right_E7,
        dot_smul_left_E7, dot_smul_right_E7, dot_comm] using hh
    apply Subtype.ext
    have hxy : x.1 - y.1 = 0 := dot_self_eq_zero_E7 hz
    exact sub_eq_zero.mp hxy
  · intro x y h
    have hsub : typeE7CoordinatePairing.flip (x - y) = 0 := by
      rw [map_sub, h, sub_self]
    have hh := LinearMap.congr_fun hsub (x - y)
    have hz : dot (x.1 - y.1) (x.1 - y.1) = 0 := by
      simpa [typeE7CoordinatePairing, dot_sub_left_E7, dot_sub_right_E7,
        dot_smul_left_E7, dot_smul_right_E7, dot_comm] using hh
    apply Subtype.ext
    have hxy : x.1 - y.1 = 0 := dot_self_eq_zero_E7 hz
    exact sub_eq_zero.mp hxy

public lemma typeE7CoordinatePairing_apply (x y : typeE7Space) :
    typeE7CoordinatePairing x y = dot x.1 y.1 := by
  simp [typeE7CoordinatePairing]

public lemma typeE7Root_dot_self (r : typeE7Roots) :
    dot r.1 r.1 = 2 := by
  exact typeE8Root_dot_self ⟨r.1, r.2.1⟩

public lemma typeE7Root_reflection_mapsTo :
    ∀ r ∈ typeE7Roots,
      MapsTo (fun x => x - dot r x • r) typeE7Roots typeE7Roots := by
  intro r hr x hx
  have hE8 := (typeE8Root_reflection_mapsTo r hr.1) hx.1
  refine ⟨hE8, ?_⟩
  rw [dot_sub_left_E7, dot_smul_left_E7]
  rw [hx.2, hr.2]
  ring

public lemma typeE7Root_preReflection_mapsTo (r : typeE7Roots) :
    MapsTo
      (Module.preReflection (typeE7RootEmbedding r)
        (typeE7CoordinatePairing.flip (typeE7RootEmbedding r)))
      (range typeE7RootEmbedding) (range typeE7RootEmbedding) := by
  rintro _ ⟨s, rfl⟩
  have hmem := (typeE7Root_reflection_mapsTo r.1 r.2) s.2
  refine ⟨⟨_, hmem⟩, ?_⟩
  apply Subtype.ext
  rw [Module.preReflection_apply]
  simp only [typeE7RootEmbedding_apply]
  change s.1 - dot r.1 s.1 • r.1 =
    s.1 - typeE7CoordinatePairing (⟨s.1, s.2.2⟩ : typeE7Space)
      (⟨r.1, r.2.2⟩ : typeE7Space) • r.1
  rw [typeE7CoordinatePairing_apply, dot_comm]

@[expose] public noncomputable def typeE7SimpleRootIndex (i : Fin 7) : typeE7Roots :=
  ⟨typeE7SimpleRoot i, typeE7SimpleRoot_mem_typeE7Roots i⟩

@[simp] public lemma typeE7SimpleRootIndex_val (i : Fin 7) :
    (typeE7SimpleRootIndex i : typeE7Roots) = ⟨typeE7SimpleRoot i,
      typeE7SimpleRoot_mem_typeE7Roots i⟩ := rfl

public lemma typeE7RootEmbedding_span_eq_top :
    span ℝ (range typeE7RootEmbedding) = ⊤ := by
  apply top_unique
  rintro x -
  let c : Fin 7 → ℝ := fun i => typeE8SimpleCoefficient x.1 i.castSucc
  have hc : (typeE8SimpleCoefficient x.1 (7 : Fin 8)) = 0 := by
    change x.1 0 + x.1 1 = 0
    have hx := x.2
    change dot x.1 (basisVector 0 + basisVector 1) = 0 at hx
    simpa [dot, basisVector, Fin.sum_univ_succ] using hx
  have hrecon := typeE8SimpleCoefficient_reconstruction x.1
  have hxrep : x.1 = ∑ i : Fin 7, c i • typeE7SimpleRoot i := by
    rw [← hrecon]
    simp only [Fin.sum_univ_succ]
    simp [typeE7SimpleRoot, c, hc]
  let y : typeE7Space := ∑ i : Fin 7,
      c i • typeE7RootEmbedding (typeE7SimpleRootIndex i)
  have hy : y ∈ span ℝ (range typeE7RootEmbedding) := by
    dsimp [y]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    exact Submodule.subset_span (show typeE7RootEmbedding
      (typeE7SimpleRootIndex i) ∈ range typeE7RootEmbedding from ⟨_, rfl⟩)
  have hxy : x = y := by
    apply Subtype.ext
    dsimp [y, c]
    simpa using hxrep
  rw [hxy]
  exact hy

@[expose] public noncomputable def typeE7RootPairing :
    RootPairing typeE7Roots ℝ typeE7Space typeE7Space :=
  RootPairing.mk'' typeE7CoordinatePairing typeE7RootEmbedding typeE7RootEmbedding
    (fun r => by rw [typeE7CoordinatePairing_apply]; exact typeE7Root_dot_self r)
    typeE7Root_preReflection_mapsTo typeE7RootEmbedding_span_eq_top

@[simp] public lemma typeE7RootPairing_root (r : typeE7Roots) :
    typeE7RootPairing.root r = typeE7RootEmbedding r := rfl

@[simp] public lemma typeE7RootPairing_coroot (r : typeE7Roots) :
    typeE7RootPairing.coroot r = typeE7RootEmbedding r := rfl

@[simp] public lemma typeE7RootPairing_pairing (r s : typeE7Roots) :
    typeE7RootPairing.pairing r s = dot r.1 s.1 := by
  exact typeE7CoordinatePairing_apply _ _

public lemma typeE7RootPairing_pairing_eq_intCast (r s : typeE7Roots) :
    ∃ z : ℤ, (z : ℝ) = typeE7RootPairing.pairing r s := by
  obtain ⟨z, hz⟩ := typeE8RootPairing_pairing_eq_intCast
    (⟨r.1, r.2.1⟩ : typeE8Roots) (⟨s.1, s.2.1⟩ : typeE8Roots)
  refine ⟨z, ?_⟩
  simpa [typeE7RootPairing_pairing] using hz

public instance typeE7RootPairing_isCrystallographic :
    typeE7RootPairing.IsCrystallographic :=
  ⟨typeE7RootPairing_pairing_eq_intCast⟩

public instance typeE7RootPairing_isRootSystem :
    typeE7RootPairing.IsRootSystem := by
  unfold typeE7RootPairing
  apply RootPairing.isRootSystem_mk''
  exact typeE7RootPairing_pairing_eq_intCast

public instance typeE7RootPairing_isReduced : typeE7RootPairing.IsReduced := by
  constructor
  intro r s hdep
  have hsmul := typeE7RootPairing.pairing_smul_root_eq_of_not_linearIndependent hdep
  simp only [typeE7RootPairing_root] at hsmul
  change typeE7RootPairing.pairing s r • typeE7RootEmbedding r =
    (2 : ℝ) • typeE7RootEmbedding s at hsmul
  have hsmulval := congrArg Subtype.val hsmul
  have hnorm := congrArg (fun x : Vec 8 => dot x x) hsmulval
  change dot (typeE7RootPairing.pairing s r • r.1)
      (typeE7RootPairing.pairing s r • r.1) =
    dot ((2 : ℝ) • s.1) ((2 : ℝ) • s.1) at hnorm
  rw [dot_smul_self_E7, dot_smul_self_E7, typeE7Root_dot_self,
    typeE7Root_dot_self] at hnorm
  have hc : typeE7RootPairing.pairing s r = 2 ∨
      typeE7RootPairing.pairing s r = -2 := by
    apply eq_or_eq_neg_of_sq_eq_sq
    norm_num at hnorm ⊢
    nlinarith
  rcases hc with hc | hc
  · left
    rw [hc] at hsmul
    apply Subtype.ext
    have heq := (isUnit_iff_ne_zero.mpr (show (2 : ℝ) ≠ 0 by norm_num)).smul_left_cancel.mp hsmul
    exact congrArg Subtype.val heq
  · right
    rw [hc] at hsmul
    have hneg : (2 : ℝ) • (-(typeE7RootEmbedding r)) =
        (2 : ℝ) • typeE7RootEmbedding s := by
      rw [smul_neg, ← neg_smul]
      exact hsmul
    apply Subtype.ext
    have heq := (isUnit_iff_ne_zero.mpr (show (2 : ℝ) ≠ 0 by norm_num)).smul_left_cancel.mp hneg
    exact congrArg Subtype.val (neg_eq_iff_eq_neg.mp heq)

public lemma typeE7SimpleRootIndex_injective :
    Function.Injective typeE7SimpleRootIndex := by
  intro i j h
  have hv : typeE7SimpleRoot i = typeE7SimpleRoot j := congrArg Subtype.val h
  have hij : i.castSucc = j.castSucc := by
    apply typeE8SimpleRoots_linearIndependent.injective
    simpa [typeE7SimpleRoot] using hv
  exact Fin.ext (by simpa using congrArg Fin.val hij)

public lemma typeE7SimpleRoots_linearIndependent :
    LinearIndependent ℝ (fun i : Fin 7 =>
      typeE7RootPairing.root (typeE7SimpleRootIndex i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h0 := congrArg (fun x : typeE7Space => x.1 0) hg
  have h1 := congrArg (fun x : typeE7Space => x.1 1) hg
  have h2 := congrArg (fun x : typeE7Space => x.1 2) hg
  have h3 := congrArg (fun x : typeE7Space => x.1 3) hg
  have h4 := congrArg (fun x : typeE7Space => x.1 4) hg
  have h5 := congrArg (fun x : typeE7Space => x.1 5) hg
  have h6 := congrArg (fun x : typeE7Space => x.1 6) hg
  have h7 := congrArg (fun x : typeE7Space => x.1 7) hg
  simp [typeE7RootPairing_root, typeE7SimpleRootIndex, typeE7SimpleRoot,
    typeE8SimpleRoot, Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5 h6 h7
  have hg0 : g 0 = 0 := by linarith
  have hg1 : g 1 = 0 := by linarith
  have hg2 : g 2 = 0 := by linarith
  have hg3 : g 3 = 0 := by linarith
  have hg4 : g 4 = 0 := by linarith
  have hg5 : g 5 = 0 := by linarith
  have hg6 : g 6 = 0 := by linarith
  fin_cases i <;> assumption

public lemma typeE7RootPairing_linearIndepOn_simpleRoots :
    LinearIndepOn ℝ typeE7RootPairing.root (range typeE7SimpleRootIndex) := by
  rw [linearIndepOn_range_iff typeE7SimpleRootIndex_injective]
  simpa [Function.comp_def] using typeE7SimpleRoots_linearIndependent

public lemma typeE7SimpleRoot_pairing (i j : Fin 7) :
    dot (typeE7SimpleRoot i) (typeE7SimpleRoot j) =
      (typeE7CartanMatrix i j : ℝ) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [typeE7SimpleRoot, typeE8SimpleRoot, typeE7CartanMatrix, dot,
      Fin.sum_univ_succ]

public lemma typeE7RootPairing_simpleIndex_pairing (i j : Fin 7) :
    typeE7RootPairing.pairing (typeE7SimpleRootIndex i)
        (typeE7SimpleRootIndex j) = algebraMap ℤ ℝ (typeE7CartanMatrix i j) := by
  rw [typeE7RootPairing_pairing]
  exact typeE7SimpleRoot_pairing i j

@[expose] public noncomputable def typeE7SimpleCoefficient (x : Vec 8) : Fin 7 → ℝ :=
  fun i => typeE8SimpleCoefficient x i.castSucc

public lemma typeE7SimpleCoefficient_reconstruction (x : Vec 8)
    (hx : dot x (basisVector 0 + basisVector 1) = 0) :
    (∑ i, typeE7SimpleCoefficient x i • typeE7SimpleRoot i) = x := by
  funext i
  fin_cases i <;>
    simp [typeE7SimpleCoefficient, typeE8SimpleCoefficient, typeE7SimpleRoot,
      typeE8SimpleRoot, basisVector, dot, Fin.sum_univ_succ] at hx ⊢ <;>
    ring_nf at hx ⊢ <;>
    linarith

public lemma typeE7Root_simpleCoefficients_nat_or_neg (r : typeE7Roots) :
    (∀ i, ∃ n : ℕ, typeE7SimpleCoefficient r.1 i = n) ∨
      (∀ i, ∃ n : ℕ, typeE7SimpleCoefficient (-r.1) i = n) := by
  have h := typeE8Root_simpleCoefficients_nat_or_neg
    (⟨r.1, r.2.1⟩ : typeE8Roots)
  rcases h with h | h
  · left
    intro i
    exact h i.castSucc
  · right
    intro i
    exact h i.castSucc

@[expose] public noncomputable def typeE7SimpleClosure : AddSubmonoid typeE7Space :=
  AddSubmonoid.closure (typeE7RootPairing.root '' range typeE7SimpleRootIndex)

public lemma typeE7SimpleRoot_mem_simpleClosure (i : Fin 7) :
    typeE7RootPairing.root (typeE7SimpleRootIndex i) ∈ typeE7SimpleClosure := by
  apply AddSubmonoid.subset_closure
  exact ⟨_, ⟨i, rfl⟩, rfl⟩

public lemma typeE7RootPairing_root_mem_or_neg_mem_simpleClosure (r : typeE7Roots) :
    typeE7RootPairing.root r ∈ typeE7SimpleClosure ∨
      -typeE7RootPairing.root r ∈ typeE7SimpleClosure := by
  rcases typeE7Root_simpleCoefficients_nat_or_neg r with h | h
  · left
    choose n hn using h
    have hm : ∑ i, n i • typeE7RootPairing.root (typeE7SimpleRootIndex i) ∈
        typeE7SimpleClosure :=
      AddSubmonoid.sum_mem _ fun i _ =>
        AddSubmonoid.nsmul_mem _ (typeE7SimpleRoot_mem_simpleClosure i) (n i)
    have heq : typeE7RootPairing.root r =
        ∑ i, n i • typeE7RootPairing.root (typeE7SimpleRootIndex i) := by
      apply Subtype.ext
      simp only [typeE7RootPairing_root, typeE7SimpleRootIndex_val,
        typeE7RootEmbedding_apply]
      have hvec : r.1 = ∑ i, (n i : ℕ) • typeE7SimpleRoot i := by
        rw [← typeE7SimpleCoefficient_reconstruction r.1 r.2.2]
        apply Finset.sum_congr rfl
        intro i _
        rw [hn i]
        exact Nat.cast_smul_eq_nsmul ℝ (n i) (typeE7SimpleRoot i)
      simpa only [typeE7Space_coe_sum, typeE7RootEmbedding_apply,
        typeE7Space_coe_nsmul, Nat.cast_smul_eq_nsmul] using hvec
    rw [heq]
    exact hm
  · right
    choose n hn using h
    have hm : ∑ i, n i • typeE7RootPairing.root (typeE7SimpleRootIndex i) ∈
        typeE7SimpleClosure :=
      AddSubmonoid.sum_mem _ fun i _ =>
        AddSubmonoid.nsmul_mem _ (typeE7SimpleRoot_mem_simpleClosure i) (n i)
    have heq : -typeE7RootPairing.root r =
        ∑ i, n i • typeE7RootPairing.root (typeE7SimpleRootIndex i) := by
      apply Subtype.ext
      simp only [typeE7RootPairing_root, typeE7SimpleRootIndex_val,
        typeE7RootEmbedding_apply]
      have hvec : -r.1 = ∑ i, (n i : ℕ) • typeE7SimpleRoot i := by
        have hxneg : dot (-r.1) (basisVector 0 + basisVector 1) = 0 := by
          rw [dot_neg_left_E7, r.2.2, neg_zero]
        rw [← typeE7SimpleCoefficient_reconstruction (-r.1) hxneg]
        apply Finset.sum_congr rfl
        intro i _
        rw [hn i]
        exact Nat.cast_smul_eq_nsmul ℝ (n i) (typeE7SimpleRoot i)
      simpa only [typeE7Space_coe_neg, typeE7Space_coe_sum,
        typeE7RootEmbedding_apply,
        typeE7Space_coe_nsmul, Nat.cast_smul_eq_nsmul] using hvec
    rw [heq]
    exact hm

@[expose] public noncomputable def typeE7RootPairing_base :
    typeE7RootPairing.Base :=
  RootPairing.Base.mk' typeE7RootPairing (range typeE7SimpleRootIndex)
    typeE7RootPairing_linearIndepOn_simpleRoots
    typeE7RootPairing_root_mem_or_neg_mem_simpleClosure

public lemma typeE7RootPairing_base_support :
    (typeE7RootPairing_base.support : Set typeE7Roots) =
      range typeE7SimpleRootIndex := by
  simp [typeE7RootPairing_base, RootPairing.Base.mk']

@[expose] public noncomputable def typeE7RootPairing_baseEquiv :
    Fin 7 ≃ typeE7RootPairing_base.support :=
  (Equiv.ofInjective typeE7SimpleRootIndex typeE7SimpleRootIndex_injective).trans
    (Equiv.setCongr typeE7RootPairing_base_support.symm)

@[simp] public lemma typeE7RootPairing_baseEquiv_val (i : Fin 7) :
    (typeE7RootPairing_baseEquiv i : typeE7Roots) = typeE7SimpleRootIndex i := rfl

public lemma typeE7RootPairing_base_cartan_apply (i j : Fin 7) :
    typeE7RootPairing_base.cartanMatrix
        (typeE7RootPairing_baseEquiv i) (typeE7RootPairing_baseEquiv j) =
      typeE7CartanMatrix i j := by
  apply FaithfulSMul.algebraMap_injective ℤ ℝ
  rw [RootPairing.Base.algebraMap_cartanMatrixIn_apply]
  rw [typeE7RootPairing_baseEquiv_val, typeE7RootPairing_baseEquiv_val]
  exact typeE7RootPairing_simpleIndex_pairing i j

public theorem typeE7RootPairing_base_cartan :
    typeE7RootPairing_base.cartanMatrix.reindex
        typeE7RootPairing_baseEquiv.symm typeE7RootPairing_baseEquiv.symm =
      typeE7CartanMatrix := by
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  exact typeE7RootPairing_base_cartan_apply i j

public lemma typeE7Cartan_connected (i j : Fin 7) :
    Relation.ReflTransGen (fun u v : Fin 7 => typeE7CartanMatrix u v ≠ 0) i j := by
  let edge := fun u v : Fin 7 => typeE7CartanMatrix u v ≠ 0
  have h01 : edge 0 1 := by decide
  have h10 : edge 1 0 := by decide
  have h12 : edge 1 2 := by decide
  have h21 : edge 2 1 := by decide
  have h23 : edge 2 3 := by decide
  have h32 : edge 3 2 := by decide
  have h24 : edge 2 4 := by decide
  have h42 : edge 4 2 := by decide
  have h45 : edge 4 5 := by decide
  have h54 : edge 5 4 := by decide
  have h56 : edge 5 6 := by decide
  have h65 : edge 6 5 := by decide
  have hto : ∀ k : Fin 7, Relation.ReflTransGen edge k 0 := by
    intro k
    fin_cases k
    · exact .refl
    · exact .single h10
    · exact (Relation.ReflTransGen.single h21).tail h10
    · exact ((Relation.ReflTransGen.single h32).tail h21).tail h10
    · exact ((Relation.ReflTransGen.single h42).tail h21).tail h10
    · exact (((Relation.ReflTransGen.single h54).tail h42).tail h21).tail h10
    · exact ((((Relation.ReflTransGen.single h65).tail h54).tail h42).tail h21).tail h10
  have hfrom : ∀ k : Fin 7, Relation.ReflTransGen edge 0 k := by
    intro k
    fin_cases k
    · exact .refl
    · exact .single h01
    · exact (Relation.ReflTransGen.single h01).tail h12
    · exact ((Relation.ReflTransGen.single h01).tail h12).tail h23
    · exact ((Relation.ReflTransGen.single h01).tail h12).tail h24
    · exact (((Relation.ReflTransGen.single h01).tail h12).tail h24).tail h45
    · exact ((((Relation.ReflTransGen.single h01).tail h12).tail h24).tail h45).tail h56
  exact (hto i).trans (hfrom j)

public lemma typeE7RootPairing_base_cartan_connected
    (s t : typeE7RootPairing_base.support) :
    Relation.ReflTransGen
      (fun u v : typeE7RootPairing_base.support =>
        typeE7RootPairing_base.cartanMatrix u v ≠ 0) s t := by
  rw [← typeE7RootPairing_baseEquiv.apply_symm_apply s,
    ← typeE7RootPairing_baseEquiv.apply_symm_apply t]
  exact Relation.ReflTransGen.lift typeE7RootPairing_baseEquiv
    (fun i j h => by
      change typeE7RootPairing_base.cartanMatrix
        (typeE7RootPairing_baseEquiv i) (typeE7RootPairing_baseEquiv j) ≠ 0
      rw [typeE7RootPairing_base_cartan_apply]
      exact h)
    _ _ (typeE7Cartan_connected _ _)

public instance typeE7RootPairing_isIrreducible :
    typeE7RootPairing.IsIrreducible :=
  isIrreducible_of_cartan_connected typeE7RootPairing typeE7RootPairing_base
    ⟨(typeE7RootPairing_baseEquiv 0 : typeE7Roots),
      (typeE7RootPairing_baseEquiv 0).property⟩
    typeE7RootPairing_base_cartan_connected

/-! ## Integral Cartan-coordinate lattice -/

public abbrev typeE7WeightModule := Fin 7 → ℤ

@[expose] public noncomputable def typeE7CartanMap :
    typeE7WeightModule →+ typeE7WeightModule where
  toFun x := typeE7CartanMatrix.mulVec x
  map_zero' := by ext i; simp
  map_add' x y := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Pi.add_apply, mul_add,
      Finset.sum_add_distrib]

@[expose] public noncomputable def typeE7SimpleRootWeight (j : Fin 7) :
    typeE7WeightModule := fun i => typeE7CartanMatrix i j

@[expose] public noncomputable def typeE7RootLattice :
    AddSubgroup typeE7WeightModule := typeE7CartanMap.range

@[expose] public noncomputable def typeE7WeightLattice :
    AddSubgroup typeE7WeightModule := ⊤

public abbrev typeE7WeightLatticeQuotient :=
  typeE7WeightModule ⧸ typeE7RootLattice

@[expose] public noncomputable def typeE7CorootLattice :
    AddSubgroup typeE7WeightModule := typeE7RootLattice

@[expose] public noncomputable def typeE7CoweightLattice :
    AddSubgroup typeE7WeightModule := ⊤

public abbrev typeE7CoweightLatticeQuotient :=
  typeE7WeightModule ⧸ typeE7CorootLattice

@[expose] public noncomputable def typeE7CartanAdjugate : Matrix (Fin 7) (Fin 7) ℤ :=
  !![4, 6, 8, 4, 6, 4, 2;
     6, 12, 16, 8, 12, 8, 4;
     8, 16, 24, 12, 18, 12, 6;
     4, 8, 12, 7, 9, 6, 3;
     6, 12, 18, 9, 15, 10, 5;
     4, 8, 12, 6, 10, 8, 4;
     2, 4, 6, 3, 5, 4, 3]

public lemma typeE7CartanMatrix_mul_adjugate :
    typeE7CartanMatrix * typeE7CartanAdjugate =
      (2 : ℤ) • (1 : Matrix (Fin 7) (Fin 7) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [typeE7CartanAdjugate, typeE7CartanMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ]

public lemma typeE7CartanAdjugate_mul_matrix :
    typeE7CartanAdjugate * typeE7CartanMatrix =
      (2 : ℤ) • (1 : Matrix (Fin 7) (Fin 7) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [typeE7CartanAdjugate, typeE7CartanMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ]

@[expose] public noncomputable def typeE7WeightLatticeQuotientMap :
    typeE7WeightModule →+ ZMod 2 where
  toFun x := ((x 3 + x 4 + x 6 : ℤ) : ZMod 2)
  map_zero' := by simp
  map_add' x y := by
    change ((x 3 + y 3 + (x 4 + y 4) + (x 6 + y 6) : ℤ) : ZMod 2) = _
    simp only [Int.cast_add]
    ring

private lemma typeE7WeightLatticeQuotientMap_cartan (x : typeE7WeightModule) :
    typeE7WeightLatticeQuotientMap (typeE7CartanMap x) = 0 := by
  change (((typeE7CartanMatrix.mulVec x) 3 + (typeE7CartanMatrix.mulVec x) 4 +
      (typeE7CartanMatrix.mulVec x) 6 : ℤ) : ZMod 2) = 0
  norm_num [typeE7CartanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  push_cast
  ring_nf
  have hz : (2 : ZMod 2) = 0 := by decide
  simp [hz]

private lemma typeE7Adjugate_mulVec_dvd (x : typeE7WeightModule)
    (hx : typeE7WeightLatticeQuotientMap x = 0) :
    ∀ i, (2 : ℤ) ∣ (typeE7CartanAdjugate.mulVec x) i := by
  have hd : (2 : ℤ) ∣ x 3 + x 4 + x 6 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
    simpa [typeE7WeightLatticeQuotientMap] using hx
  intro i
  fin_cases i
  · refine ⟨2 * x 0 + 3 * x 1 + 4 * x 2 + 2 * x 3 + 3 * x 4 + 2 * x 5 + x 6, ?_⟩
    simp [typeE7CartanAdjugate, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · refine ⟨3 * x 0 + 6 * x 1 + 8 * x 2 + 4 * x 3 + 6 * x 4 + 4 * x 5 + 2 * x 6, ?_⟩
    simp [typeE7CartanAdjugate, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · refine ⟨4 * x 0 + 8 * x 1 + 12 * x 2 + 6 * x 3 + 9 * x 4 + 6 * x 5 + 3 * x 6, ?_⟩
    simp [typeE7CartanAdjugate, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · rcases hd with ⟨n, hn⟩
    refine ⟨n + 2 * x 0 + 4 * x 1 + 6 * x 2 + 3 * x 3 + 4 * x 4 + 3 * x 5 + x 6, ?_⟩
    simp [typeE7CartanAdjugate, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    omega
  · rcases hd with ⟨n, hn⟩
    refine ⟨n + 3 * x 0 + 6 * x 1 + 9 * x 2 + 4 * x 3 + 7 * x 4 + 5 * x 5 + 2 * x 6, ?_⟩
    simp [typeE7CartanAdjugate, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    omega
  · refine ⟨2 * x 0 + 4 * x 1 + 6 * x 2 + 3 * x 3 + 5 * x 4 + 4 * x 5 + 2 * x 6, ?_⟩
    simp [typeE7CartanAdjugate, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · rcases hd with ⟨n, hn⟩
    refine ⟨n + x 0 + 2 * x 1 + 3 * x 2 + x 3 + 2 * x 4 + 2 * x 5 + x 6, ?_⟩
    simp [typeE7CartanAdjugate, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    omega

private noncomputable def typeE7AdjugateCoefficient (x : typeE7WeightModule) :
    typeE7WeightModule := fun i =>
  (typeE7CartanAdjugate.mulVec x) i / 2

private lemma typeE7CartanMap_adjugateCoefficient (x : typeE7WeightModule)
    (hx : typeE7WeightLatticeQuotientMap x = 0) :
    typeE7CartanMap (typeE7AdjugateCoefficient x) = x := by
  have hc : ∀ i, 2 * typeE7AdjugateCoefficient x i =
      (typeE7CartanAdjugate.mulVec x) i := by
    intro i
    dsimp [typeE7AdjugateCoefficient]
    rw [mul_comm, Int.ediv_mul_cancel]
    exact typeE7Adjugate_mulVec_dvd x hx i
  have hc' : (2 : ℤ) • typeE7AdjugateCoefficient x =
      typeE7CartanAdjugate.mulVec x := by
    funext i
    exact hc i
  have hmain := congrArg (fun v : typeE7WeightModule =>
      typeE7CartanMatrix.mulVec v) hc'
  have hmul : typeE7CartanMatrix.mulVec
      (typeE7CartanAdjugate.mulVec x) = (2 : ℤ) • x := by
    calc
      typeE7CartanMatrix.mulVec (typeE7CartanAdjugate.mulVec x) =
          (typeE7CartanMatrix * typeE7CartanAdjugate).mulVec x :=
        Matrix.mulVec_mulVec x typeE7CartanMatrix typeE7CartanAdjugate
      _ = (2 : ℤ) • x := by
        rw [typeE7CartanMatrix_mul_adjugate]
        simp
  rw [Matrix.mulVec_smul, hmul] at hmain
  ext i
  have hi := congrArg (fun v : typeE7WeightModule => v i) hmain
  simpa [typeE7CartanMap, smul_eq_mul] using hi

public lemma typeE7WeightLatticeQuotientMap_ker :
    (typeE7WeightLatticeQuotientMap).ker = typeE7RootLattice := by
  ext x
  constructor
  · intro hx
    rw [typeE7RootLattice, AddMonoidHom.mem_range]
    exact ⟨typeE7AdjugateCoefficient x, typeE7CartanMap_adjugateCoefficient x hx⟩
  · rintro ⟨y, rfl⟩
    exact typeE7WeightLatticeQuotientMap_cartan y

public lemma typeE7WeightLatticeQuotientMap_surjective :
    Function.Surjective typeE7WeightLatticeQuotientMap := by
  intro z
  refine ⟨fun i => if i = 3 then ZMod.cast z else 0, ?_⟩
  change ((ZMod.cast z : ℤ) : ZMod 2) = z
  exact ZMod.intCast_zmod_cast z

@[expose] public noncomputable def typeE7WeightLatticeQuotientEquiv :
    typeE7WeightLatticeQuotient ≃+ ZMod 2 :=
  (QuotientAddGroup.quotientAddEquivOfEq typeE7WeightLatticeQuotientMap_ker.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective typeE7WeightLatticeQuotientMap
      typeE7WeightLatticeQuotientMap_surjective)

public noncomputable def typeE7_rootLattice_quotient_equiv_zmod2 :
    typeE7WeightLatticeQuotient ≃+ ZMod 2 :=
  typeE7WeightLatticeQuotientEquiv

public noncomputable def typeE7_corootLattice_quotient_equiv_zmod2 :
    typeE7CoweightLatticeQuotient ≃+ ZMod 2 := by
  exact typeE7WeightLatticeQuotientEquiv

public theorem typeE7_standardRootPairing_exists :
    typeE7RootPairing.IsRootSystem ∧ typeE7RootPairing.IsCrystallographic ∧
      typeE7RootPairing.IsReduced ∧ typeE7RootPairing.IsIrreducible ∧
      ∃ (b : typeE7RootPairing.Base) (numbering : Fin 7 ≃ b.support),
        b.cartanMatrix.reindex numbering.symm numbering.symm = typeE7CartanMatrix := by
  refine ⟨typeE7RootPairing_isRootSystem, typeE7RootPairing_isCrystallographic,
    typeE7RootPairing_isReduced, typeE7RootPairing_isIrreducible,
    typeE7RootPairing_base, typeE7RootPairing_baseEquiv, ?_⟩
  exact typeE7RootPairing_base_cartan

end Theory.AlgebraicGroup.StandardRootSystem
