module

public import Mathlib.LinearAlgebra.Matrix.Dual
public import Theory.AlgebraicGroup.RootSystems.Exceptional

/-!
# The standard root pairing of type G₂

This module constructs the explicit twelve-root G₂ pairing in the real coordinate plane.  The
short root is `+[1, 0]` and the long root is `+[0, 1]`; the coroot map is given by the
corresponding Cartan-dual coordinates, with a factor of `1/3` on long roots.  All reflection,
crystallographic, reducedness, base, and Cartan-matrix facts are proved by finite coordinate
calculations, independently of any algebraic-group carrier or classification theorem.
-/
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 2000000
namespace Theory.AlgebraicGroup.StandardRootSystem

open Set

private lemma dot_add_left_G2 (x y z : Vec 2) : dot (x + y) z = dot x z + dot y z := by
  simp [dot, add_mul, Finset.sum_add_distrib]
private lemma dot_add_right_G2 (x y z : Vec 2) : dot x (y + z) = dot x y + dot x z := by
  simp [dot, mul_add, Finset.sum_add_distrib]
private lemma dot_smul_left_G2 (c : ℝ) (x y : Vec 2) : dot (c • x) y = c * dot x y := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
private lemma dot_smul_right_G2 (c : ℝ) (x y : Vec 2) : dot x (c • y) = c * dot x y := by
  rw [dot_comm, dot_smul_left_G2]
  simp [dot_comm]

@[expose] public noncomputable def typeG2Short : Vec 2 := ![1, 0]
@[expose] public noncomputable def typeG2Long : Vec 2 := ![0, 1]

public abbrev typeG2Root : Type := typeG2Roots typeG2Long typeG2Short

public instance typeG2Root_finite : Finite typeG2Root :=
  Set.finite_coe_iff.mpr (typeG2Roots_finite typeG2Long typeG2Short)

@[expose] public noncomputable def typeG2StandardRootEmbedding : typeG2Root ↪ Vec 2 :=
  typeG2RootEmbedding typeG2Long typeG2Short

@[simp] public lemma typeG2StandardRootEmbedding_apply (r : typeG2Root) :
    typeG2StandardRootEmbedding r = r.1 := rfl

@[expose] public def typeG2LongRootSet : Set (Vec 2) :=
  {typeG2Long, -typeG2Long, typeG2Long + 3 • typeG2Short,
    -(typeG2Long + 3 • typeG2Short),
    2 • typeG2Long + 3 • typeG2Short,
    -(2 • typeG2Long + 3 • typeG2Short)}

@[expose] public noncomputable def typeG2CorootVector (r : typeG2Root) : Vec 2 :=
  @ite (Vec 2) (r.1 ∈ typeG2LongRootSet) (Classical.propDecidable _)
    ((1 / 3 : ℝ) • ![2 * r.1 0 - 3 * r.1 1, -3 * r.1 0 + 6 * r.1 1])
    (![2 * r.1 0 - 3 * r.1 1, -3 * r.1 0 + 6 * r.1 1])

public lemma typeG2CorootVector_injective : Function.Injective typeG2CorootVector := by
  rintro ⟨r, hr⟩ ⟨s, hs⟩ h
  simp only [typeG2Roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hr hs
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr
  all_goals
    rcases hs with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
    all_goals
      subst r
      subst s
      simp [typeG2CorootVector, typeG2LongRootSet, typeG2Long, typeG2Short] at h ⊢ <;>
        first | rfl | (exfalso; norm_num at h)

@[expose] public noncomputable def typeG2StandardCorootEmbedding : typeG2Root ↪ Vec 2 :=
  ⟨typeG2CorootVector, typeG2CorootVector_injective⟩

@[simp] public lemma typeG2StandardCorootEmbedding_apply (r : typeG2Root) :
    typeG2StandardCorootEmbedding r = typeG2CorootVector r := rfl

public noncomputable def typeG2CoordinatePairing :
    Vec 2 →ₗ[ℝ] Vec 2 →ₗ[ℝ] ℝ :=
  (dotProductEquiv ℝ (Fin 2)).toLinearMap

public instance typeG2CoordinatePairing_isPerfPair :
    typeG2CoordinatePairing.IsPerfPair := by
  unfold typeG2CoordinatePairing
  infer_instance

public lemma typeG2CoordinatePairing_apply (x y : Vec 2) :
    typeG2CoordinatePairing x y = dot x y := by
  simp [typeG2CoordinatePairing, dotProductEquiv, dot, dotProduct]

public lemma typeG2Root_coroot_self_pairing (r : typeG2Root) :
    typeG2CoordinatePairing (typeG2StandardRootEmbedding r)
      (typeG2StandardCorootEmbedding r) = 2 := by
  rw [typeG2CoordinatePairing_apply]
  rcases r with ⟨r, hr⟩
  change dot r (typeG2CorootVector ⟨r, hr⟩) = 2
  simp only [typeG2Roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr
  all_goals
    subst r
    simp [typeG2StandardRootEmbedding_apply, typeG2StandardCorootEmbedding_apply,
      typeG2CorootVector, typeG2LongRootSet, typeG2Long, typeG2Short,
      dot, Fin.sum_univ_succ, typeG2RootEmbedding, typeG2Roots] <;> norm_num

public lemma typeG2Root_preReflection_mapsTo (r : typeG2Root) :
    MapsTo
      (Module.preReflection (typeG2StandardRootEmbedding r)
        (typeG2CoordinatePairing.flip (typeG2StandardCorootEmbedding r)))
      (range typeG2StandardRootEmbedding) (range typeG2StandardRootEmbedding) := by
  classical
  rintro _ ⟨s, rfl⟩
  rcases r with ⟨r, hr⟩
  rcases s with ⟨s, hs⟩
  have hr_mem := hr
  have hs_mem := hs
  simp only [typeG2Roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hr hs
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr <;>
    rcases hs with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  all_goals
    let t : Vec 2 :=
      Module.preReflection
        r
        (typeG2CoordinatePairing.flip (typeG2CorootVector ⟨r, hr_mem⟩))
        s
    subst r
    subst s
    refine ⟨⟨t, ?_⟩, ?_⟩
    · simp [Module.preReflection_apply, typeG2CorootVector, typeG2LongRootSet,
        typeG2Long, typeG2Short, typeG2CoordinatePairing_apply,
        typeG2Roots, dot, Fin.sum_univ_succ, t] <;>
        norm_num [funext_iff, Fin.forall_fin_two]
    · simp [t, typeG2StandardRootEmbedding_apply, typeG2StandardCorootEmbedding_apply]

public lemma typeG2RootEmbedding_span_eq_top :
    Submodule.span ℝ (range typeG2StandardRootEmbedding) = ⊤ := by
  apply typeG2RootEmbedding_span_eq_top_of_simpleRoots
  apply top_unique
  intro x _
  rw [Submodule.mem_span_pair]
  refine ⟨x 1, x 0, ?_⟩
  ext i
  fin_cases i <;> simp [typeG2Short, typeG2Long, basisVector]

@[expose] public noncomputable def typeG2RootPairing :
    RootPairing typeG2Root ℝ (Vec 2) (Vec 2) :=
  RootPairing.mk'' typeG2CoordinatePairing typeG2StandardRootEmbedding
    typeG2StandardCorootEmbedding typeG2Root_coroot_self_pairing
    typeG2Root_preReflection_mapsTo typeG2RootEmbedding_span_eq_top

@[simp] public lemma typeG2RootPairing_root (r : typeG2Root) :
    typeG2RootPairing.root r = r.1 := rfl

@[simp] public lemma typeG2RootPairing_coroot (r : typeG2Root) :
    typeG2RootPairing.coroot r = typeG2CorootVector r := rfl

@[simp] public lemma typeG2RootPairing_pairing (r s : typeG2Root) :
    typeG2RootPairing.pairing r s = dot r.1 (typeG2CorootVector s) := by
  change typeG2CoordinatePairing r.1 (typeG2StandardCorootEmbedding s) = _
  rw [typeG2CoordinatePairing_apply, typeG2StandardCorootEmbedding_apply]

public lemma typeG2RootPairing_pairing_eq_intCast (r s : typeG2Root) :
    ∃ z : ℤ, (z : ℝ) = typeG2RootPairing.pairing r s := by
  have int_cases (x : ℝ)
      (hx : x = -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) :
      ∃ z : ℤ, (z : ℝ) = x := by
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨-3, by norm_num⟩
    · exact ⟨-2, by norm_num⟩
    · exact ⟨-1, by norm_num⟩
    · exact ⟨0, by norm_num⟩
    · exact ⟨1, by norm_num⟩
    · exact ⟨2, by norm_num⟩
    · exact ⟨3, by norm_num⟩
  rcases r with ⟨r, hr⟩
  rcases s with ⟨s, hs⟩
  simp only [typeG2Roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hr hs
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr <;>
    rcases hs with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  all_goals
    subst r
    subst s
    apply int_cases
    rw [typeG2RootPairing_pairing]
    simp [typeG2RootPairing_pairing, typeG2CorootVector,
      typeG2LongRootSet, typeG2Long, typeG2Short, dot, Fin.sum_univ_succ] <;>
      norm_num

public instance typeG2RootPairing_isCrystallographic :
    typeG2RootPairing.IsCrystallographic := by
  constructor
  exact typeG2RootPairing_pairing_eq_intCast

public instance typeG2RootPairing_isRootSystem : typeG2RootPairing.IsRootSystem := by
  unfold typeG2RootPairing
  apply RootPairing.isRootSystem_mk''
  exact typeG2RootPairing_pairing_eq_intCast

public instance typeG2RootPairing_isReduced : typeG2RootPairing.IsReduced := by
  constructor
  intro r s hdep
  simp only [typeG2RootPairing_root] at hdep ⊢
  rcases r with ⟨r, hr⟩
  rcases s with ⟨s, hs⟩
  change ¬LinearIndependent ℝ ![r, s] at hdep
  simp only [typeG2Roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hr hs
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr <;>
    rcases hs with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  all_goals
    subst r
    subst s
    first
    | exact Or.inl rfl
    | (apply Or.inr; ext i; fin_cases i <;>
        norm_num [typeG2Long, typeG2Short, Fin.sum_univ_succ] <;> done)
    | exfalso
      apply hdep
      rw [Fintype.linearIndependent_iff]
      norm_num [funext_iff, Fin.forall_fin_two, typeG2Long, typeG2Short,
        Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      all_goals
        try (intro g h0 h1; constructor <;> linarith)

@[expose] public noncomputable def typeG2SimpleRootIndex (i : Fin 2) : typeG2Root :=
  match i with
  | ⟨0, _⟩ => ⟨typeG2Short, by simp [typeG2Roots, typeG2Short]⟩
  | ⟨1, _⟩ => ⟨typeG2Long, by simp [typeG2Roots, typeG2Long]⟩

@[simp] public lemma typeG2SimpleRootIndex_val (i : Fin 2) :
    (typeG2SimpleRootIndex i : Vec 2) =
      if i.val = 0 then typeG2Short else typeG2Long := by
  fin_cases i <;> rfl

public lemma typeG2SimpleRootIndex_injective : Function.Injective typeG2SimpleRootIndex := by
  intro i j h
  have hv := congrArg Subtype.val h
  fin_cases i <;> fin_cases j <;> simp [typeG2SimpleRootIndex, typeG2Short, typeG2Long] at hv ⊢

public lemma typeG2SimpleRoots_linearIndependent :
    LinearIndependent ℝ (fun i : Fin 2 => typeG2RootPairing.root (typeG2SimpleRootIndex i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h0 := congrFun hg (0 : Fin 2)
  have h1 := congrFun hg (1 : Fin 2)
  simp [typeG2RootPairing_root, typeG2SimpleRootIndex, typeG2Short,
    typeG2Long, Fin.sum_univ_succ] at h0 h1
  have hg0 : g (0 : Fin 2) = 0 := by linarith
  have hg1 : g (1 : Fin 2) = 0 := by linarith
  fin_cases i
  · exact hg0
  · exact hg1

@[expose] public noncomputable def typeG2SimpleClosure : AddSubmonoid (Vec 2) :=
  AddSubmonoid.closure (typeG2RootPairing.root '' Set.range typeG2SimpleRootIndex)

public lemma typeG2SimpleRoot_mem_simpleClosure (i : Fin 2) :
    typeG2RootPairing.root (typeG2SimpleRootIndex i) ∈ typeG2SimpleClosure := by
  apply AddSubmonoid.subset_closure
  exact ⟨_, ⟨i, rfl⟩, rfl⟩

public lemma typeG2Root_mem_or_neg_mem_simpleClosure (r : typeG2Root) :
    typeG2RootPairing.root r ∈ typeG2SimpleClosure ∨
      -typeG2RootPairing.root r ∈ typeG2SimpleClosure := by
  have hshort := typeG2SimpleRoot_mem_simpleClosure (0 : Fin 2)
  have hlong := typeG2SimpleRoot_mem_simpleClosure (1 : Fin 2)
  rcases r with ⟨r, hr⟩
  simp only [typeG2Roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr
  all_goals
    subst r
    simp only [typeG2RootPairing_root]
    first
    | exact Or.inl hlong
    | exact Or.inr (by simpa using hlong)
    | exact Or.inl hshort
    | exact Or.inr (by simpa using hshort)
    | exact Or.inl (AddSubmonoid.add_mem _ hlong hshort)
    | exact Or.inr (by simpa using AddSubmonoid.add_mem _ hlong hshort)
    | exact Or.inl (AddSubmonoid.add_mem _ hlong (AddSubmonoid.nsmul_mem _ hshort 2))
    | exact Or.inr (by simpa using AddSubmonoid.add_mem _ hlong (AddSubmonoid.nsmul_mem _ hshort 2))
    | exact Or.inl (AddSubmonoid.add_mem _ hlong (AddSubmonoid.nsmul_mem _ hshort 3))
    | exact Or.inr (by simpa using AddSubmonoid.add_mem _ hlong (AddSubmonoid.nsmul_mem _ hshort 3))
    | exact Or.inl (by
        simpa [two_nsmul] using AddSubmonoid.add_mem _
          (AddSubmonoid.nsmul_mem _ hlong 2) (AddSubmonoid.nsmul_mem _ hshort 3))
    | exact Or.inr (by
        simpa [two_nsmul] using AddSubmonoid.add_mem _
          (AddSubmonoid.nsmul_mem _ hlong 2) (AddSubmonoid.nsmul_mem _ hshort 3))

@[expose] public noncomputable def typeG2RootPairing_base : typeG2RootPairing.Base :=
  RootPairing.Base.mk' typeG2RootPairing (Set.range typeG2SimpleRootIndex)
    (by
      rw [linearIndepOn_range_iff typeG2SimpleRootIndex_injective]
      simpa [Function.comp_def] using typeG2SimpleRoots_linearIndependent)
    (by
      intro r
      exact typeG2Root_mem_or_neg_mem_simpleClosure r)

public lemma typeG2RootPairing_base_support :
    (typeG2RootPairing_base.support : Set typeG2Root) =
      Set.range typeG2SimpleRootIndex := by
  simp [typeG2RootPairing_base, RootPairing.Base.mk']

@[expose] public noncomputable def typeG2RootPairing_baseEquiv :
    Fin 2 ≃ typeG2RootPairing_base.support :=
  (Equiv.ofInjective typeG2SimpleRootIndex typeG2SimpleRootIndex_injective).trans
    (Equiv.setCongr typeG2RootPairing_base_support.symm)

@[simp] public lemma typeG2RootPairing_baseEquiv_val (i : Fin 2) :
    (typeG2RootPairing_baseEquiv i : typeG2Root) = typeG2SimpleRootIndex i := rfl

public lemma typeG2RootPairing_simpleIndex_pairing (i j : Fin 2) :
    typeG2RootPairing.pairing (typeG2SimpleRootIndex i) (typeG2SimpleRootIndex j) =
      algebraMap ℤ ℝ (typeG2CartanMatrix i j) := by
  rw [typeG2RootPairing_pairing]
  simp only [typeG2SimpleRootIndex_val]
  change _ = (typeG2CartanMatrix i j : ℝ)
  fin_cases i <;> fin_cases j <;>
    norm_num [typeG2CorootVector, typeG2LongRootSet, typeG2Long,
      typeG2Short, typeG2CartanMatrix, dot, Fin.sum_univ_succ]

public lemma typeG2RootPairing_base_cartan_apply (i j : Fin 2) :
    typeG2RootPairing_base.cartanMatrix
        (typeG2RootPairing_baseEquiv i) (typeG2RootPairing_baseEquiv j) =
      typeG2CartanMatrix i j := by
  apply FaithfulSMul.algebraMap_injective ℤ ℝ
  rw [RootPairing.Base.algebraMap_cartanMatrixIn_apply]
  rw [typeG2RootPairing_baseEquiv_val, typeG2RootPairing_baseEquiv_val]
  exact typeG2RootPairing_simpleIndex_pairing i j

public theorem typeG2RootPairing_base_cartan :
    typeG2RootPairing_base.cartanMatrix.reindex
        typeG2RootPairing_baseEquiv.symm typeG2RootPairing_baseEquiv.symm =
      typeG2CartanMatrix := by
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  exact typeG2RootPairing_base_cartan_apply i j

public lemma typeG2Cartan_connected (i j : Fin 2) :
    Relation.ReflTransGen (fun u v : Fin 2 => typeG2CartanMatrix u v ≠ 0) i j := by
  let edge := fun u v : Fin 2 => typeG2CartanMatrix u v ≠ 0
  have h01 : edge 0 1 := by norm_num [edge, typeG2CartanMatrix]
  have h10 : edge 1 0 := by norm_num [edge, typeG2CartanMatrix]
  have hto : ∀ k : Fin 2, Relation.ReflTransGen edge k 0 := by
    intro k
    fin_cases k
    · exact .refl
    · exact .single h10
  have hfrom : ∀ k : Fin 2, Relation.ReflTransGen edge 0 k := by
    intro k
    fin_cases k
    · exact .refl
    · exact .single h01
  exact (hto i).trans (hfrom j)

public lemma typeG2RootPairing_base_cartan_connected
    (s t : typeG2RootPairing_base.support) :
    Relation.ReflTransGen
      (fun u v : typeG2RootPairing_base.support =>
        typeG2RootPairing_base.cartanMatrix u v ≠ 0) s t := by
  rw [← typeG2RootPairing_baseEquiv.apply_symm_apply s,
    ← typeG2RootPairing_baseEquiv.apply_symm_apply t]
  exact Relation.ReflTransGen.lift typeG2RootPairing_baseEquiv
    (fun i j h => by
      change typeG2RootPairing_base.cartanMatrix
        (typeG2RootPairing_baseEquiv i) (typeG2RootPairing_baseEquiv j) ≠ 0
      rw [typeG2RootPairing_base_cartan_apply]
      exact h)
    _ _ (typeG2Cartan_connected _ _)

public instance typeG2RootPairing_isIrreducible : typeG2RootPairing.IsIrreducible :=
  isIrreducible_of_cartan_connected typeG2RootPairing typeG2RootPairing_base
    ⟨(typeG2RootPairing_baseEquiv 0 : typeG2Root),
      (typeG2RootPairing_baseEquiv 0).property⟩
    typeG2RootPairing_base_cartan_connected

end Theory.AlgebraicGroup.StandardRootSystem
