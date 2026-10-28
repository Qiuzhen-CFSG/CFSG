module

public import Theory.AlgebraicGroup.Borel.RootStructure.theorem_1_12_4
public import Theory.AlgebraicGroup.Cartan.Kernels
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
The type `C` universal-center calculation from GLS3 Table 1.12.5.

For a rank `m` type-`C` Cartan matrix, the multiplicative coroot relations
have a one-dimensional kernel: all coordinates are trivial except the final
coordinate, which is a second root of unity.  The arithmetic is supplied by
`dynkinCartanRelationKernel_C`; this module packages it as an explicit
Cartan-kernel subgroup, proves the resulting equivalence with
`rootsOfUnity 2`, and leaves the geometric center-to-kernel equivalence as an
explicit hypothesis.  This keeps the reusable lattice computation below the
source-level center classification and avoids the placeholder-backed
`theorem_1_12_5`.
-/

namespace Theory.AlgebraicGroup

open scoped BigOperators

universe u

variable {k : Type u} [Field k]

/-- The common multiplicative kernel of the numbered type-`C` Cartan
relations. -/
public def typeCCartanRelationKernel (m : ℕ) : Subgroup (Fin m → kˣ) where
  carrier := {t | ∀ j, (∏ i, t i ^ dynkinCartanEntry ⟨.C, m⟩ i j) = 1}
  one_mem' := by
    intro j
    simp
  mul_mem' := by
    intro a b ha hb j
    simp only [Pi.mul_apply, mul_zpow]
    simp only [Finset.prod_mul_distrib]
    rw [ha, hb]
    simp
  inv_mem' := by
    intro a ha j
    simp only [Pi.inv_apply, inv_zpow]
    simp only [Finset.prod_inv_distrib]
    rw [ha]
    simp

/-- Insert a second root of unity in the terminal type-`C` coordinate. -/
public def typeCCartanRelationKernelMap (m : ℕ) (hm : 2 ≤ m) :
    rootsOfUnity 2 k →* typeCCartanRelationKernel (k := k) m := by
  let f : rootsOfUnity 2 k →* (Fin m → kˣ) :=
    { toFun := fun ω i => if i.val = m - 1 then ω else 1
      map_one' := by
        ext i
        simp
      map_mul' := by
        intro ω ζ
        funext i
        by_cases hi : i.val = m - 1 <;> simp [hi] }
  exact f.codRestrict _ (by
    intro ω j
    let last : Fin m := ⟨m - 1, by omega⟩
    have hprod : (∏ i, f ω i ^ dynkinCartanEntry ⟨.C, m⟩ i j) =
        f ω last ^ dynkinCartanEntry ⟨.C, m⟩ last j := by
      apply Fintype.prod_eq_single last
      intro i hi
      have hiv : i.val ≠ m - 1 := by
        intro hv
        apply hi
        apply Fin.ext
        simpa [last] using hv
      simp [f, hiv]
    rw [hprod]
    by_cases hj : j = last
    · subst j
      have hω : (ω : kˣ) ^ 2 = 1 :=
        (mem_rootsOfUnity 2 (ω : kˣ)).mp ω.property
      simpa [last, f, dynkinCartanEntry, zpow_ofNat] using hω
    · by_cases hjpred : j.val + 1 = m - 1
      · have hentry : dynkinCartanEntry ⟨.C, m⟩ last j = -2 := by
          have hj' : last ≠ j := by
            intro h
            exact hj h.symm
          have hmEq : m - 1 + 1 = m := by omega
          have hforward : ¬m = j.val := by
            have hjlt : j.val < m := j.isLt
            omega
          simp [dynkinCartanEntry, last, hj', hjpred, hmEq, hforward]
        rw [hentry]
        have hω : (ω : kˣ) ^ 2 = 1 :=
          (mem_rootsOfUnity 2 (ω : kˣ)).mp ω.property
        simpa [f, last, zpow_neg, zpow_ofNat] using hω
      · have hentry : dynkinCartanEntry ⟨.C, m⟩ last j = 0 := by
          have hj' : last ≠ j := by
            intro h
            exact hj h.symm
          have hnot : ¬m - 1 + 1 = j.val := by
            have hjlt : j.val < m := j.isLt
            omega
          simp [dynkinCartanEntry, last, hj', hjpred, hnot]
        rw [hentry]
        simp)

@[simp]
public lemma typeCCartanRelationKernelMap_apply
    (m : ℕ) (hm : 2 ≤ m) (ω : rootsOfUnity 2 k) (i : Fin m) :
    (typeCCartanRelationKernelMap (k := k) m hm ω).1 i =
      if i.val = m - 1 then ω else 1 := by
  change (if i.val = m - 1 then (ω : kˣ) else 1) =
    if i.val = m - 1 then ω else 1
  by_cases hi : i.val = m - 1 <;> simp [hi]

public lemma typeCCartanRelationKernelMap_injective
    (m : ℕ) (hm : 2 ≤ m) :
    Function.Injective (typeCCartanRelationKernelMap (k := k) m hm) := by
  intro ω ζ h
  have hlast := congrArg
    (fun t => t.1 (⟨m - 1, by omega⟩ : Fin m)) h
  simpa [typeCCartanRelationKernelMap_apply] using hlast

public lemma typeCCartanRelationKernelMap_surjective
    (m : ℕ) (hm : 2 ≤ m) :
    Function.Surjective (typeCCartanRelationKernelMap (k := k) m hm) := by
  intro t
  have hEq : m - 1 + 1 = m := by omega
  let e : Fin (m - 1 + 1) ≃ Fin m := finCongr hEq
  have hraw := dynkinCartanRelationKernel_C (k := k) (m - 1) (by omega)
    (fun i : Fin (m - 1 + 1) => t.1 (e i))
    (fun j => by
      have hrew :
          (∏ i : Fin (m - 1 + 1), t.1 (e i) ^
              dynkinCartanEntry ⟨.C, m - 1 + 1⟩ i j) =
            ∏ y : Fin m, t.1 y ^ dynkinCartanEntry ⟨.C, m⟩ y (e j) := by
        apply Fintype.prod_equiv e
        intro x
        have hentry : dynkinCartanEntry ⟨.C, m - 1 + 1⟩ x j =
            dynkinCartanEntry ⟨.C, m⟩ (e x) (e j) := by
          simp [e, hEq, dynkinCartanEntry]
        rw [hentry]
      rw [hrew]
      exact t.2 (e j))
  rcases hraw with ⟨ω, hω, ht⟩
  let ω' : rootsOfUnity 2 k :=
    ⟨ω, by simpa [mem_rootsOfUnity] using hω⟩
  refine ⟨ω', ?_⟩
  apply Subtype.ext
  funext i
  have hi := ht (e.symm i)
  rw [e.apply_symm_apply] at hi
  have hval : (e.symm i).val = i.val := by
    rfl
  rw [hval] at hi
  rw [typeCCartanRelationKernelMap_apply]
  by_cases hilast : i.val = m - 1
  · simpa [hilast, ω'] using hi.symm
  · simpa [hilast, ω'] using hi.symm

/-- The type-`C` Cartan kernel is canonically equivalent to the second roots
of unity. -/
public noncomputable def typeCCartanRelationKernelEquiv
    (m : ℕ) (hm : 2 ≤ m) :
    rootsOfUnity 2 k ≃* typeCCartanRelationKernel (k := k) m :=
  MulEquiv.ofBijective (typeCCartanRelationKernelMap (k := k) m hm)
    ⟨typeCCartanRelationKernelMap_injective (k := k) m hm,
      typeCCartanRelationKernelMap_surjective (k := k) m hm⟩

/-- Coordinate form of the type-`C` Cartan-kernel calculation. -/
public theorem typeC_cartan_kernel_coordinates
    (m : ℕ) (hm : 2 ≤ m) (t : Fin m → kˣ)
    (ht : t ∈ typeCCartanRelationKernel (k := k) m) :
    ∃ ω : kˣ, ω ^ 2 = 1 ∧
      ∀ i, t i = (if i.val = m - 1 then ω else 1) := by
  obtain ⟨ω, hω⟩ :=
    typeCCartanRelationKernelMap_surjective (k := k) m hm ⟨t, ht⟩
  have hωpow : (ω : kˣ) ^ 2 = 1 :=
    (mem_rootsOfUnity 2 (ω : kˣ)).mp ω.property
  refine ⟨ω, hωpow, ?_⟩
  intro i
  have hi := congrArg (fun s => s.1 i) hω
  rw [typeCCartanRelationKernelMap_apply] at hi
  by_cases hlast : i.val = m - 1
  · simp [hlast] at hi ⊢
    exact hi.symm
  · simp [hlast] at hi ⊢
    exact hi.symm

/-- Convert the center-to-Cartan-kernel bridge into the universal type-`C`
center shape. -/
public theorem typeC_hasCenterShape_of_centerRelationKernelEquiv
    {K : Variety k} [AlgebraicGroup K]
    (m : ℕ) (hm : 2 ≤ m)
    (hCenter : Nonempty
      (Subgroup.center (Variety.Point K) ≃*
        typeCCartanRelationKernel (k := k) m)) :
    HasCenterShape (K := K) (.rootsOfUnity 2) := by
  simpa only [HasCenterShape] using
    Nonempty.map
      (fun e => e.trans (typeCCartanRelationKernelEquiv (k := k) m hm).symm)
      hCenter

/-- Universal, semisimple-simple type-`C` specialization of the kernel
calculation.  The explicit center/kernel equivalence is the independent
center-character input; the present theorem supplies its Cartan arithmetic. -/
public theorem typeC_universal_center_shape_core
    {K : Variety k} [AlgebraicGroup K]
    (m : ℕ) (hm : 2 ≤ m)
    (_hK : IsSemisimpleAlgebraicGroup K)
    (_hSimple : IsSimpleAlgebraicGroup K)
    (_hType : HasRootSystemType K ⟨.C, m⟩)
    (_hValid : IsValidGeneratorTableClassification ⟨.C, m⟩)
    (_hUniversal : IsUniversalVersion K)
    (hCenter : Nonempty
      (Subgroup.center (Variety.Point K) ≃*
        typeCCartanRelationKernel (k := k) m)) :
    HasCenterShape (K := K) (universalCenterShape ⟨.C, m⟩) := by
  simpa [universalCenterShape] using
    typeC_hasCenterShape_of_centerRelationKernelEquiv m hm hCenter

/-- A compact wrapper exposing only the center/kernel and universal-version
inputs for clients that already carry the type-`C` setup. -/
public theorem typeC_universal_center_shape_of_cartan_kernel
    {K : Variety k} [AlgebraicGroup K]
    (m : ℕ) (hm : 2 ≤ m)
    (hCenter : Nonempty
      (Subgroup.center (Variety.Point K) ≃*
        typeCCartanRelationKernel (k := k) m))
    (_hUniversal : IsUniversalVersion K) :
    HasCenterShape (K := K) (universalCenterShape ⟨.C, m⟩) := by
  simpa [universalCenterShape] using
    typeC_hasCenterShape_of_centerRelationKernelEquiv m hm hCenter

end Theory.AlgebraicGroup
