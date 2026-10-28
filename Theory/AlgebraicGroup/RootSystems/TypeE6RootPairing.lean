module

public import Theory.AlgebraicGroup.RootSystems.TypeE8RootPairing
public import Mathlib.LinearAlgebra.Matrix.Dual
public meta import Mathlib.Data.Fintype.Pi
public meta import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# The standard root pairing of type E6

The E6 roots are the explicit roots from `Exceptional.lean` cut out by its two
orthogonality equations.  We restrict the Euclidean E8 pairing to their real
span.  Reflection stability is inherited from the coordinate E8 calculation,
while the displayed six simple roots are handled by direct coordinate
coefficients; this gives the base and the displayed E6 Cartan matrix without
using group classification or Chevalley existence.
-/

namespace Theory.AlgebraicGroup.StandardRootSystem

open Set

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

private lemma dot_add_left_E6 (x y z : Vec 8) :
    dot (x + y) z = dot x z + dot y z := by
  simp [dot, add_mul, Finset.sum_add_distrib]

private lemma dot_sub_left_E6 (x y z : Vec 8) :
    dot (x - y) z = dot x z - dot y z := by
    simp [dot, sub_mul, Finset.sum_sub_distrib]

private lemma dot_add_right_E6 (x y z : Vec 8) :
    dot x (y + z) = dot x y + dot x z := by
  rw [dot_comm x (y + z), dot_add_left_E6, dot_comm x y, dot_comm x z]

private lemma dot_sub_right_E6 (x y z : Vec 8) :
    dot x (y - z) = dot x y - dot x z := by
  rw [dot_comm x (y - z), dot_sub_left_E6, dot_comm x y, dot_comm x z]

private lemma dot_smul_left_E6 (c : ℝ) (x y : Vec 8) :
    dot (c • x) y = c * dot x y := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma dot_smul_right_E6 (c : ℝ) (x y : Vec 8) :
    dot x (c • y) = c * dot x y := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma dot_neg_left_E6 (x y : Vec 8) : dot (-x) y = -dot x y := by
  simpa using dot_smul_left_E6 (-1) x y

private lemma dot_basisVector_left_E6 (i : Fin 8) (x : Vec 8) :
    dot (basisVector i) x = x i := by
  classical
  simp [dot, basisVector, Pi.single_apply]

private lemma dot_basisVector_right_E6 (x : Vec 8) (i : Fin 8) :
    dot x (basisVector i) = x i := by
  rw [dot_comm, dot_basisVector_left_E6]

private lemma dot_smul_self_E6 (c : ℝ) (x : Vec 8) :
    dot (c • x) (c • x) = c ^ 2 * dot x x := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

public theorem typeE6Roots_finite : typeE6Roots.Finite := by
  exact typeE8Roots_finite.subset (by
    intro x hx
    exact hx.1.1)

public instance typeE6Roots_finiteType : Finite typeE6Roots :=
  Set.finite_coe_iff.mpr typeE6Roots_finite

@[expose] public noncomputable def typeE6RootEmbedding :
    typeE6Roots ↪ Vec 8 := Function.Embedding.subtype _

@[simp] public lemma typeE6RootEmbedding_apply (r : typeE6Roots) :
    typeE6RootEmbedding r = (r : Vec 8) := rfl

@[expose] public noncomputable def typeE6RootSpan :
    Submodule ℝ (Vec 8) := Submodule.span ℝ (range typeE6RootEmbedding)

@[expose] public noncomputable def typeE6RootInSpan :
    typeE6Roots ↪ typeE6RootSpan where
  toFun r := ⟨r.1, Submodule.subset_span ⟨r, rfl⟩⟩
  inj' _ _ h := Subtype.ext (congrArg (fun x : typeE6RootSpan => (x : Vec 8)) h)

@[simp] public lemma typeE6RootInSpan_val (r : typeE6Roots) :
    (typeE6RootInSpan r : Vec 8) = r.1 := rfl

@[expose] public noncomputable def typeE6RootFunctional (r : typeE6Roots) :
    Module.Dual ℝ typeE6RootSpan where
  toFun x := dot r.1 x.1
  map_add' x y := by simp [dot, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [RingHom.id_apply, smul_eq_mul, dot]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change r.1 i * (c * x.1 i) = c * (r.1 i * x.1 i)
    ring

public lemma typeE6RootFunctional_injective :
    Function.Injective typeE6RootFunctional := by
  intro r s h
  let x : typeE6RootSpan := typeE6RootInSpan r - typeE6RootInSpan s
  have hx : dot (r.1 - s.1) (r.1 - s.1) = 0 := by
    have he := LinearMap.congr_fun h x
    dsimp [typeE6RootFunctional, typeE6RootInSpan, x] at he
    rw [show dot (r.1 - s.1) (r.1 - s.1) =
      dot r.1 (r.1 - s.1) - dot s.1 (r.1 - s.1) by
        simp [dot, sub_mul, Finset.sum_sub_distrib]]
    exact sub_eq_zero.mpr he
  have hzero : ∀ i, (r.1 - s.1) i = 0 := by
    have hsum : ∑ i, (r.1 - s.1) i * (r.1 - s.1) i = 0 := hx
    have hall := (Finset.sum_mul_self_eq_zero_iff Finset.univ
      (fun i => (r.1 - s.1) i)).mp (by simpa using hsum)
    intro i
    simpa using hall i (Finset.mem_univ i)
  apply Subtype.ext
  funext i
  have := hzero i
  exact sub_eq_zero.mp this

@[expose] public noncomputable def typeE6CorootEmbedding :
    typeE6Roots ↪ Module.Dual ℝ typeE6RootSpan :=
  ⟨typeE6RootFunctional, typeE6RootFunctional_injective⟩

@[simp] public lemma typeE6CorootEmbedding_apply (r : typeE6Roots) :
    typeE6CorootEmbedding r = typeE6RootFunctional r := rfl

public lemma typeE6Root_dot_self (r : typeE6Roots) : dot r.1 r.1 = 2 := by
  exact typeE8Root_dot_self ⟨r.1, r.2.1.1⟩

private lemma typeE6Root_reflection_mapsTo :
    ∀ r ∈ typeE6Roots,
      MapsTo (fun x => x - dot r x • r) typeE6Roots typeE6Roots := by
  intro r hr x hx
  have hE8 := (typeE8Root_reflection_mapsTo r hr.1.1) hx.1.1
  refine ⟨⟨hE8, ?_⟩, ?_⟩
  · rw [dot_sub_left_E6, dot_smul_left_E6]
    rw [hr.1.2, hx.1.2]
    ring
  · rw [dot_sub_left_E6, dot_smul_left_E6]
    rw [hr.2, hx.2]
    ring

public lemma typeE6RootEmbedding_span_eq_top :
    Submodule.span ℝ (range (fun r : typeE6Roots =>
      (typeE6RootInSpan r : typeE6RootSpan))) = ⊤ := by
  apply top_unique
  intro x hx
  refine Submodule.span_induction (p := fun y hy =>
    (⟨y, hy⟩ : typeE6RootSpan) ∈
      Submodule.span ℝ (range typeE6RootInSpan)) ?_ ?_ ?_ ?_ x.property
  · intro y hy
    rcases hy with ⟨r, rfl⟩
    exact Submodule.subset_span ⟨r, rfl⟩
  · exact Submodule.zero_mem _
  · intro y z hy hz hy' hz'
    exact Submodule.add_mem _ hy' hz'
  · intro c y hy hy'
    exact Submodule.smul_mem _ c hy'

public lemma typeE6Root_coroot_eval (r : typeE6Roots) :
    Module.Dual.eval ℝ typeE6RootSpan (typeE6RootInSpan r)
      (typeE6CorootEmbedding r) = 2 := by
  change dot r.1 r.1 = 2
  exact typeE6Root_dot_self r

public lemma typeE6Root_preReflection_mapsTo (r : typeE6Roots) :
    MapsTo
      (Module.preReflection (typeE6RootInSpan r)
        ((Module.Dual.eval ℝ typeE6RootSpan).flip
          (typeE6CorootEmbedding r)))
      (range typeE6RootInSpan) (range typeE6RootInSpan) := by
  rintro _ ⟨s, rfl⟩
  have hmem := (typeE6Root_reflection_mapsTo r.1 r.2) s.2
  let t : typeE6Roots := ⟨s.1 - dot r.1 s.1 • r.1, hmem⟩
  refine ⟨t, ?_⟩
  rw [Module.preReflection_apply]
  apply Subtype.ext
  change s.1 - dot r.1 s.1 • r.1 = _
  simp only [typeE6RootInSpan_val, LinearMap.flip_apply,
    Module.Dual.eval_apply, typeE6CorootEmbedding, typeE6RootFunctional]
  rfl

@[expose] public noncomputable def typeE6RootPairing :
    RootPairing typeE6Roots ℝ typeE6RootSpan
      (Module.Dual ℝ typeE6RootSpan) := by
  letI : FiniteDimensional ℝ typeE6RootSpan :=
    FiniteDimensional.span_of_finite ℝ (Set.toFinite (range typeE6RootEmbedding))
  let B := Module.Dual.eval ℝ typeE6RootSpan
  letI : B.IsPerfPair := by infer_instance
  exact RootPairing.mk'' B typeE6RootInSpan typeE6CorootEmbedding
    typeE6Root_coroot_eval typeE6Root_preReflection_mapsTo
    typeE6RootEmbedding_span_eq_top

@[simp] public lemma typeE6RootPairing_root (r : typeE6Roots) :
    typeE6RootPairing.root r = typeE6RootInSpan r := rfl

@[simp] public lemma typeE6RootPairing_coroot (r : typeE6Roots) :
    typeE6RootPairing.coroot r = typeE6CorootEmbedding r := rfl

@[simp] public lemma typeE6RootPairing_pairing (r s : typeE6Roots) :
    typeE6RootPairing.pairing r s = dot r.1 s.1 := by
  change dot s.1 r.1 = dot r.1 s.1
  exact dot_comm _ _

public lemma typeE6RootPairing_pairing_eq_intCast (r s : typeE6Roots) :
    ∃ z : ℤ, (z : ℝ) = typeE6RootPairing.pairing r s := by
  classical
  rw [typeE6RootPairing_pairing]
  let rr : typeE8Roots := ⟨r.1, r.2.1.1⟩
  let ss : typeE8Roots := ⟨s.1, s.2.1.1⟩
  obtain ⟨z, hz⟩ := typeE8RootPairing_pairing_eq_intCast rr ss
  refine ⟨z, ?_⟩
  rw [typeE8RootPairing_pairing] at hz
  simpa [typeE6RootPairing_pairing] using hz

public instance typeE6RootPairing_isCrystallographic :
    typeE6RootPairing.IsCrystallographic where
  exists_value := typeE6RootPairing_pairing_eq_intCast

public instance typeE6RootPairing_isRootSystem :
    typeE6RootPairing.IsRootSystem := by
  unfold typeE6RootPairing
  apply RootPairing.isRootSystem_mk''
  exact typeE6RootPairing_pairing_eq_intCast

public instance typeE6RootPairing_isReduced : typeE6RootPairing.IsReduced := by
  constructor
  intro r s hdep
  have hsmul := typeE6RootPairing.pairing_smul_root_eq_of_not_linearIndependent hdep
  simp only [typeE6RootPairing_root] at hsmul
  have hnorm := congrArg (fun x : typeE6RootSpan => dot (x : Vec 8) x.1) hsmul
  change dot (typeE6RootPairing.pairing s r • (r.1 : Vec 8))
      (typeE6RootPairing.pairing s r • (r.1 : Vec 8)) =
    dot ((2 : ℝ) • (s.1 : Vec 8)) ((2 : ℝ) • (s.1 : Vec 8)) at hnorm
  rw [dot_smul_self_E6, dot_smul_self_E6,
    typeE6Root_dot_self, typeE6Root_dot_self] at hnorm
  have hc : typeE6RootPairing.pairing s r = 2 ∨
      typeE6RootPairing.pairing s r = -2 := by
    apply eq_or_eq_neg_of_sq_eq_sq
    norm_num at hnorm ⊢
    nlinarith
  rcases hc with hc | hc
  · left
    rw [hc] at hsmul
    exact (isUnit_iff_ne_zero.mpr (show (2 : ℝ) ≠ 0 by norm_num)).smul_left_cancel.mp hsmul
  · right
    rw [hc] at hsmul
    have hneg : (2 : ℝ) • (-typeE6RootInSpan r) =
        (2 : ℝ) • typeE6RootInSpan s := by
      rw [smul_neg, ← neg_smul]
      exact hsmul
    exact neg_eq_iff_eq_neg.mp
      ((isUnit_iff_ne_zero.mpr (show (2 : ℝ) ≠ 0 by norm_num)).smul_left_cancel.mp hneg)

@[expose] public noncomputable def typeE6SimpleRootIndex (i : Fin 6) : typeE6Roots :=
  ⟨typeE6SimpleRoot i, typeE6SimpleRoot_mem_typeE6Roots i⟩

@[simp] public lemma typeE6SimpleRootIndex_val (i : Fin 6) :
    (typeE6SimpleRootIndex i : Vec 8) = typeE6SimpleRoot i := rfl

private lemma typeE6SimpleRoot_eq_typeE8 (i : Fin 6) :
    typeE6SimpleRoot i = typeE8SimpleRoot (i.castSucc.castSucc) := by
  rfl

public lemma typeE6SimpleRoots_linearIndependent :
    LinearIndependent ℝ typeE6SimpleRoot := by
  change LinearIndependent ℝ
    (typeE8SimpleRoot ∘ (fun i : Fin 6 => i.castSucc.castSucc))
  exact typeE8SimpleRoots_linearIndependent.comp
    (fun i : Fin 6 => i.castSucc.castSucc)
    (by intro i j h; apply Fin.ext; simpa using congrArg Fin.val h)

public lemma typeE6SimpleRootIndex_injective : Function.Injective typeE6SimpleRootIndex := by
  intro i j h
  apply typeE6SimpleRoots_linearIndependent.injective
  exact congrArg Subtype.val h

public lemma typeE6RootPairing_linearIndepOn_simpleRoots :
    LinearIndepOn ℝ typeE6RootPairing.root (Set.range typeE6SimpleRootIndex) := by
  rw [linearIndepOn_range_iff typeE6SimpleRootIndex_injective]
  apply LinearIndependent.of_comp (typeE6RootSpan.subtype)
  simpa [Function.comp_def] using typeE6SimpleRoots_linearIndependent

@[expose] public noncomputable def typeE6SimpleCoefficient (x : Vec 8) : Fin 6 → ℝ
  | ⟨0, _⟩ => 2 * x 0
  | ⟨1, _⟩ => (7 * x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + x 6 - x 7) / 2
  | ⟨2, _⟩ => 5 * x 0 + x 1 + x 2 + x 3 + x 4 + x 5
  | ⟨3, _⟩ => (5 * x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7) / 2
  | ⟨4, _⟩ => 4 * x 0 + x 1 + x 2 + x 3 + x 4
  | ⟨5, _⟩ => 3 * x 0 + x 1 + x 2 + x 3

private lemma typeE6SimpleCoefficient_eq_typeE8 (x : Vec 8) (i : Fin 6) :
    typeE6SimpleCoefficient x i =
      typeE8SimpleCoefficient x (i.castSucc.castSucc) := by
  fin_cases i <;> rfl

public lemma typeE6SimpleCoefficient_reconstruction
    (x : Vec 8) (h0 : x 0 = -x 1) (h2 : x 2 = x 1) :
    (∑ i, typeE6SimpleCoefficient x i • typeE6SimpleRoot i) = x := by
  have h := typeE8SimpleCoefficient_reconstruction x
  have hc6 : typeE8SimpleCoefficient x (6 : Fin 8) = 0 := by
    simp [typeE8SimpleCoefficient]
    linarith [h0, h2]
  have hc7 : typeE8SimpleCoefficient x (7 : Fin 8) = 0 := by
    simp [typeE8SimpleCoefficient]
    linarith [h0]
  have hfirst : (∑ i : Fin 6, typeE6SimpleCoefficient x i • typeE6SimpleRoot i) =
      ∑ i : Fin 6, typeE8SimpleCoefficient x (i.castSucc.castSucc) •
        typeE8SimpleRoot (i.castSucc.castSucc) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [typeE6SimpleCoefficient_eq_typeE8, typeE6SimpleRoot_eq_typeE8]
  have hsum : (∑ i : Fin 6, typeE6SimpleCoefficient x i • typeE6SimpleRoot i) +
        typeE8SimpleCoefficient x 6 • typeE8SimpleRoot 6 +
        typeE8SimpleCoefficient x 7 • typeE8SimpleRoot 7 =
      (∑ i, typeE8SimpleCoefficient x i • typeE8SimpleRoot i) := by
    rw [hfirst]
    conv_rhs => rw [Fin.sum_univ_castSucc]
    conv_rhs => rw [Fin.sum_univ_castSucc]
    rfl
  calc
    (∑ i : Fin 6, typeE6SimpleCoefficient x i • typeE6SimpleRoot i) =
        (∑ i : Fin 6, typeE6SimpleCoefficient x i • typeE6SimpleRoot i) +
          typeE8SimpleCoefficient x 6 • typeE8SimpleRoot 6 +
          typeE8SimpleCoefficient x 7 • typeE8SimpleRoot 7 := by
      rw [hc6, hc7, zero_smul, zero_smul, add_zero, add_zero]
    _ = (∑ i, typeE8SimpleCoefficient x i • typeE8SimpleRoot i) := hsum
    _ = x := h

public lemma typeE6RootPairing_root_mem_or_neg_mem_simpleClosure (r : typeE6Roots) :
    typeE6RootPairing.root r ∈
        AddSubmonoid.closure (typeE6RootPairing.root '' Set.range typeE6SimpleRootIndex) ∨
      -typeE6RootPairing.root r ∈
        AddSubmonoid.closure (typeE6RootPairing.root '' Set.range typeE6SimpleRootIndex) := by
  let rr : typeE8Roots := ⟨r.1, r.2.1.1⟩
  have hr0 : r.1 0 = -r.1 1 := by
    have h := r.2.1.2
    rw [dot_add_right_E6, dot_basisVector_right_E6, dot_basisVector_right_E6] at h
    linarith
  have hr2 : r.1 2 = r.1 1 := by
    have h := r.2.2
    rw [dot_sub_right_E6, dot_basisVector_right_E6, dot_basisVector_right_E6] at h
    linarith
  rcases typeE8Root_simpleCoefficients_nat_or_neg rr with hpos | hneg
  · left
    have hpos6 : ∀ i : Fin 6, ∃ n : ℕ,
        typeE6SimpleCoefficient r.1 i = n := by
      intro i
      obtain ⟨n, hn⟩ := hpos (i.castSucc.castSucc)
      exact ⟨n, by simpa [typeE6SimpleCoefficient_eq_typeE8] using hn⟩
    choose n hn using hpos6
    have hmem : ∑ i, n i • typeE6RootPairing.root (typeE6SimpleRootIndex i) ∈
        AddSubmonoid.closure
          (typeE6RootPairing.root '' Set.range typeE6SimpleRootIndex) :=
      AddSubmonoid.sum_mem _ fun i _ =>
        AddSubmonoid.nsmul_mem _
          (AddSubmonoid.subset_closure
            (show typeE6RootPairing.root (typeE6SimpleRootIndex i) ∈
                typeE6RootPairing.root '' Set.range typeE6SimpleRootIndex from
              ⟨typeE6SimpleRootIndex i, ⟨i, rfl⟩, rfl⟩)) (n i)
    convert hmem using 1
    apply Subtype.ext
    simp only [typeE6RootInSpan_val, typeE6RootPairing_root, typeE6SimpleRootIndex_val]
    change (r.1 : Vec 8) = ∑ i, n i • (typeE6SimpleRoot i : Vec 8)
    rw [← typeE6SimpleCoefficient_reconstruction r.1 hr0 hr2]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Nat.cast_smul_eq_nsmul ℝ, ← hn i]
  · right
    have hneg0 : (-r.1) 0 = -(-r.1) 1 := by
      simpa [hr0]
    have hneg2 : (-r.1) 2 = (-r.1) 1 := by
      simpa [hr2]
    have hneg6 : ∀ i : Fin 6, ∃ n : ℕ,
        typeE6SimpleCoefficient (-r.1) i = n := by
      intro i
      obtain ⟨n, hn⟩ := hneg (i.castSucc.castSucc)
      exact ⟨n, by simpa [typeE6SimpleCoefficient_eq_typeE8] using hn⟩
    choose n hn using hneg6
    have hmem : ∑ i, n i • typeE6RootPairing.root (typeE6SimpleRootIndex i) ∈
        AddSubmonoid.closure
          (typeE6RootPairing.root '' Set.range typeE6SimpleRootIndex) :=
      AddSubmonoid.sum_mem _ fun i _ =>
        AddSubmonoid.nsmul_mem _
          (AddSubmonoid.subset_closure
            (show typeE6RootPairing.root (typeE6SimpleRootIndex i) ∈
                typeE6RootPairing.root '' Set.range typeE6SimpleRootIndex from
              ⟨typeE6SimpleRootIndex i, ⟨i, rfl⟩, rfl⟩)) (n i)
    convert hmem using 1
    apply Subtype.ext
    simp only [typeE6RootInSpan_val, typeE6RootPairing_root, typeE6SimpleRootIndex_val]
    change (-r.1 : Vec 8) = ∑ i, n i • (typeE6SimpleRoot i : Vec 8)
    rw [← typeE6SimpleCoefficient_reconstruction (-r.1) hneg0 hneg2]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Nat.cast_smul_eq_nsmul ℝ, ← hn i]

@[expose] public noncomputable def typeE6RootPairing_base : typeE6RootPairing.Base :=
  RootPairing.Base.mk' typeE6RootPairing (Set.range typeE6SimpleRootIndex)
    typeE6RootPairing_linearIndepOn_simpleRoots
    typeE6RootPairing_root_mem_or_neg_mem_simpleClosure

public lemma typeE6RootPairing_base_support :
    (typeE6RootPairing_base.support : Set typeE6Roots) =
      Set.range typeE6SimpleRootIndex := by
  simp [typeE6RootPairing_base, RootPairing.Base.mk']

@[expose] public noncomputable def typeE6RootPairing_baseEquiv :
    Fin 6 ≃ typeE6RootPairing_base.support :=
  (Equiv.ofInjective typeE6SimpleRootIndex typeE6SimpleRootIndex_injective).trans
    (Equiv.setCongr typeE6RootPairing_base_support.symm)

@[simp] public lemma typeE6RootPairing_baseEquiv_val (i : Fin 6) :
    (typeE6RootPairing_baseEquiv i : typeE6Roots) = typeE6SimpleRootIndex i := rfl

public lemma typeE6SimpleRoot_pairing (i j : Fin 6) :
    dot (typeE6SimpleRoot i) (typeE6SimpleRoot j) =
      (typeE6CartanMatrix i j : ℝ) := by
  rw [typeE6SimpleRoot_eq_typeE8 i, typeE6SimpleRoot_eq_typeE8 j]
  fin_cases i <;> fin_cases j <;>
    norm_num [typeE8SimpleRoot_pairing, typeE6CartanMatrix,
      typeE8CartanMatrix]

public lemma typeE6RootPairing_simpleIndex_pairing (i j : Fin 6) :
    typeE6RootPairing.pairing (typeE6SimpleRootIndex i) (typeE6SimpleRootIndex j) =
      algebraMap ℤ ℝ (typeE6CartanMatrix i j) := by
  rw [typeE6RootPairing_pairing, typeE6SimpleRootIndex_val]
  exact typeE6SimpleRoot_pairing i j

public lemma typeE6RootPairing_base_cartan_apply (i j : Fin 6) :
    typeE6RootPairing_base.cartanMatrix
        (typeE6RootPairing_baseEquiv i) (typeE6RootPairing_baseEquiv j) =
      typeE6CartanMatrix i j := by
  apply FaithfulSMul.algebraMap_injective ℤ ℝ
  rw [RootPairing.Base.algebraMap_cartanMatrixIn_apply]
  rw [typeE6RootPairing_baseEquiv_val, typeE6RootPairing_baseEquiv_val]
  exact typeE6RootPairing_simpleIndex_pairing i j

public theorem typeE6RootPairing_base_cartan :
    typeE6RootPairing_base.cartanMatrix.reindex
        typeE6RootPairing_baseEquiv.symm typeE6RootPairing_baseEquiv.symm =
      typeE6CartanMatrix := by
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  exact typeE6RootPairing_base_cartan_apply i j

public theorem typeE6_standardRootPairing_exists :
    typeE6RootPairing.IsRootSystem ∧ typeE6RootPairing.IsCrystallographic ∧
      typeE6RootPairing.IsReduced ∧
        ∃ (b : typeE6RootPairing.Base) (numbering : Fin 6 ≃ b.support),
          b.cartanMatrix.reindex numbering.symm numbering.symm = typeE6CartanMatrix := by
  refine ⟨typeE6RootPairing_isRootSystem, typeE6RootPairing_isCrystallographic,
    typeE6RootPairing_isReduced, typeE6RootPairing_base, typeE6RootPairing_baseEquiv, ?_⟩
  exact typeE6RootPairing_base_cartan

end Theory.AlgebraicGroup.StandardRootSystem
