module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/SingularReduction.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG import paths and Lean 4.33 public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.G2.WeylMaps
public import Theory.AtlasPort.LinearGroups.G2.Unipotent

/-! Root and Weyl operations reduce every nonzero singular trace-zero vector to the first basis vector, proving transitivity constructively. -/

@[expose] public section

namespace Atlas.G2
open Atlas.SplitOctonion Explicit
variable {K : Type*} [Field K]

/-- The root and Weyl subgroup, before any claim that it is the full group. -/
def rootWeylSubgroup : Subgroup (Model K) :=
  Subgroup.closure ((↑(unipotent (K := K)) : Set (Model K)) ∪ {weylR,weylS})

theorem nonzero_offdiagonal (x : Carrier K) (ht : trace x = 0) (hn : norm x = 0)
    (hx : x ≠ 0) :
    x 0 ≠ 0 ∨ x 1 ≠ 0 ∨ x 2 ≠ 0 ∨ x 5 ≠ 0 ∨ x 6 ≠ 0 ∨ x 7 ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨h0,h1,h2,h5,h6,h7⟩ := h
  have h4 : x 4 = -x 3 := eq_neg_of_add_eq_zero_right ht
  have h3 : x 3 * x 3 = 0 := by simpa [norm,h0,h1,h2,h4] using hn
  have h3 := mul_self_eq_zero.mp h3
  apply hx
  ext i; fin_cases i <;> simp [h0,h1,h2,h3,h4,h5,h6,h7]

/-- The elementary root/Weyl subgroup can move a singular vector to the open chart. -/
theorem exists_open_chart (x : Carrier K) (ht : trace x = 0) (hn : norm x = 0)
    (hx : x ≠ 0) : ∃ w : Model K, w ∈ rootWeylSubgroup ∧ w.val x 7 ≠ 0 := by
  have hr : (weylR : Model K) ∈ rootWeylSubgroup := Subgroup.subset_closure (by simp)
  have hs : (weylS : Model K) ∈ rootWeylSubgroup := Subgroup.subset_closure (by simp)
  have hw : (weylR * weylS : Model K) ∈ rootWeylSubgroup := rootWeylSubgroup.mul_mem hr hs
  rcases nonzero_offdiagonal x ht hn hx with h|h|h|h|h|h
  · refine ⟨(weylR*weylS)^3,rootWeylSubgroup.pow_mem hw 3,?_⟩
    simpa [pow_succ,weylR,weylS,weylREquiv,weylSEquiv,weylRLinear,weylSLinear,weylRApply,weylSApply] using h
  · refine ⟨(weylR*weylS)^4,rootWeylSubgroup.pow_mem hw 4,?_⟩
    simpa [pow_succ,weylR,weylS,weylREquiv,weylSEquiv,weylRLinear,weylSLinear,weylRApply,weylSApply] using h
  · refine ⟨(weylR*weylS)^2,rootWeylSubgroup.pow_mem hw 2,?_⟩
    simpa [pow_succ,weylR,weylS,weylREquiv,weylSEquiv,weylRLinear,weylSLinear,weylRApply,weylSApply] using h
  · refine ⟨(weylR*weylS)^5,rootWeylSubgroup.pow_mem hw 5,?_⟩
    simpa [pow_succ,weylR,weylS,weylREquiv,weylSEquiv,weylRLinear,weylSLinear,weylRApply,weylSApply] using h
  · refine ⟨weylR*weylS,hw,?_⟩
    simpa [weylR,weylS,weylREquiv,weylSEquiv,weylRLinear,weylSLinear,weylRApply,weylSApply] using h
  · exact ⟨1,rootWeylSubgroup.one_mem,h⟩

/-- Successive elementary elimination on the chart with nonzero last coordinate. -/
def chartReducer (x : Carrier K) : Model K :=
  let f := -x 6 / x 7
  let y := (rootF f).val x
  let d := -y 5 / y 7
  let z := (rootD d).val y
  let c := z 3 / z 7
  let w := (rootC c).val z
  let a := -w 1 / w 7
  let b := -w 2 / w 7
  rootB b * rootA a * rootC c * rootD d * rootF f


theorem chartReducer_mem (x : Carrier K) : chartReducer x ∈ rootWeylSubgroup := by
  have hu : unipotent (K := K) ≤ rootWeylSubgroup :=
    fun _ hg => Subgroup.subset_closure (Or.inl hg)
  have hrootA : ∀ a, rootA a ∈ rootWeylSubgroup := fun a => hu
    (Subgroup.subset_closure (by simp))
  have hrootB : ∀ a, rootB a ∈ rootWeylSubgroup := fun a => hu
    (Subgroup.subset_closure (by simp))
  have hrootC : ∀ a, rootC a ∈ rootWeylSubgroup := fun a => hu
    (Subgroup.subset_closure (by simp))
  have hrootD : ∀ a, rootD a ∈ rootWeylSubgroup := fun a => hu
    (Subgroup.subset_closure (by simp))
  have hrootF : ∀ a, rootF a ∈ rootWeylSubgroup := fun a => hu
    (Subgroup.subset_closure (by simp))
  exact rootWeylSubgroup.mul_mem (rootWeylSubgroup.mul_mem (rootWeylSubgroup.mul_mem
    (rootWeylSubgroup.mul_mem (hrootB _) (hrootA _)) (hrootC _)) (hrootD _)) (hrootF _)

theorem chartReducer_last_coordinates (x : Carrier K) (ht : trace x = 0) (hx : x 7 ≠ 0) :
    (chartReducer x).val x 1 = 0 ∧ (chartReducer x).val x 2 = 0 ∧
    (chartReducer x).val x 3 = 0 ∧ (chartReducer x).val x 4 = 0 ∧
    (chartReducer x).val x 5 = 0 ∧ (chartReducer x).val x 6 = 0 ∧
    (chartReducer x).val x 7 = x 7 := by
  have ht4 : x 4 = -x 3 := eq_neg_of_add_eq_zero_right ht
  repeat' constructor
  all_goals
    simp [chartReducer,rootA,rootB,rootC,rootD,rootF,rootAEquiv,rootBEquiv,rootCEquiv,
      rootDEquiv,rootFEquiv,rootALinear,rootBLinear,rootCLinear,rootDLinear,rootFLinear,
      rootAApply,rootBApply,rootCApply,rootDApply,rootFApply,ht4]
    field_simp
    ring


theorem chartReducer_eq (x : Carrier K) (ht : trace x = 0) (hn : norm x = 0)
    (hx : x 7 ≠ 0) : (chartReducer x).val x = x 7 • basisVector 7 := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7⟩ := chartReducer_last_coordinates x ht hx
  have hz := (automorphism_norm (chartReducer x) x).trans hn
  simp only [norm,h1,h2,h3,h4,h5,h6,h7,zero_mul,add_zero] at hz
  have h0 : (chartReducer x).val x 0 = 0 := (mul_eq_zero.mp hz).resolve_right hx
  ext i; fin_cases i <;> simp [basisVector,h0,h1,h2,h3,h4,h5,h6,h7]

/-- Root/Weyl reduction of every nonzero singular vector to a nonzero basis multiple. -/
theorem singular_vector_reduction (x : Carrier K) (ht : trace x = 0) (hn : norm x = 0)
    (hx : x ≠ 0) : ∃ g : Model K, g ∈ rootWeylSubgroup ∧
      ∃ r : K, r ≠ 0 ∧ g.val x = r • basisVector 7 := by
  obtain ⟨w,hw,hwx⟩ := exists_open_chart x ht hn hx
  refine ⟨chartReducer (w.val x) * w,
    rootWeylSubgroup.mul_mem (chartReducer_mem _) hw,w.val x 7,hwx,?_⟩
  exact chartReducer_eq (w.val x) ((automorphism_trace w x).trans ht)
    ((automorphism_norm w x).trans hn) hwx

theorem weylCycle_cube_basis7 : ((weylR * weylS : Model K)^3).val (basisVector 7) =
    basisVector 0 := by
  ext i; fin_cases i <;>
    simp [pow_succ,weylR,weylS,weylREquiv,weylSEquiv,weylRLinear,weylSLinear,
      weylRApply,weylSApply,basisVector]

/-- Reduction to the designated singular line, using only roots and Weyl maps. -/
theorem singular_vector_reduction_first (x : Carrier K) (ht : trace x = 0)
    (hn : norm x = 0) (hx : x ≠ 0) : ∃ g : Model K, g ∈ rootWeylSubgroup ∧
      ∃ r : K, r ≠ 0 ∧ g.val x = r • basisVector 0 := by
  obtain ⟨g,hg,r,hr,hgx⟩ := singular_vector_reduction x ht hn hx
  have hw : (weylR * weylS : Model K) ∈ rootWeylSubgroup :=
    rootWeylSubgroup.mul_mem (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  refine ⟨(weylR*weylS)^3*g,
    rootWeylSubgroup.mul_mem (rootWeylSubgroup.pow_mem hw 3) hg,r,hr,?_⟩
  change ((weylR*weylS : Model K)^3).val (g.val x) = _
  rw [hgx,map_smul,weylCycle_cube_basis7]
end Atlas.G2
