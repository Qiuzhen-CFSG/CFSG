module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/PointOrbits.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, public module boundaries, and Lean 4.33 proof adaptation.
-/

public import Theory.AtlasPort.LinearGroups.G2.Parabolic

/-! Explicit parabolic elements reduce singular points to representatives of the four point-stabilizer orbits. -/

@[expose] public section

noncomputable section
namespace Atlas.G2
open Atlas.SplitOctonion Explicit
variable {K : Type*} [Field K]

/-- Normalize the third stratum after its last nonzero pair has been aligned. -/
def middleReducer (x : Carrier K) : Model K :=
  let y := (rootE (-x 5 / x 6)).val x
  let z := (rootD (y 3 / y 6)).val y
  let w := (rootC (-z 2 / z 6)).val z
  rootA (w 0 / w 6) * rootC (-z 2 / z 6) * rootD (y 3 / y 6) * rootE (-x 5 / x 6)

theorem middleReducer_mem (x : Carrier K) : middleReducer x ∈ parabolic := by
  have hA : ∀ a : K, rootA a ∈ parabolic := fun a => unipotent_le_parabolic
    (Subgroup.subset_closure (by simp))
  have hC : ∀ a : K, rootC a ∈ parabolic := fun a => unipotent_le_parabolic
    (Subgroup.subset_closure (by simp))
  have hD : ∀ a : K, rootD a ∈ parabolic := fun a => unipotent_le_parabolic
    (Subgroup.subset_closure (by simp))
  exact parabolic.mul_mem (parabolic.mul_mem (parabolic.mul_mem (hA _) (hC _)) (hD _))
    (rootE_mem_parabolic _)

theorem middleReducer_eq (x : Carrier K) (ht : trace x = 0)
    (hn : SplitOctonion.norm x = 0) (h7 : x 7 = 0) (h6 : x 6 ≠ 0) :
    (middleReducer x).val x = x 6 • basisVector 6 := by
  have h4 : x 4 = -x 3 := eq_neg_of_add_eq_zero_right ht
  have hcoords : ∀ i : Fin 8, i ≠ 1 →
      (middleReducer x).val x i = (x 6 • basisVector 6) i := by
    intro i hi
    fin_cases i <;> try contradiction
    all_goals simp [middleReducer,rootA,rootC,rootD,rootE,rootAEquiv,rootCEquiv,
      rootDEquiv,rootEEquiv,rootALinear,rootCLinear,rootDLinear,rootELinear,
      rootAApply,rootCApply,rootDApply,rootEApply,basisVector,h7,h4]
    all_goals field_simp
    all_goals ring
  have hz := (automorphism_norm (middleReducer x) x).trans hn
  have hzero : (middleReducer x).val x 1 = 0 := by
    simp only [SplitOctonion.norm] at hz
    rw [hcoords 0 (by decide),hcoords 2 (by decide),hcoords 3 (by decide),
      hcoords 4 (by decide),hcoords 5 (by decide),hcoords 6 (by decide),hcoords 7 (by decide)] at hz
    simp [basisVector] at hz
    exact hz.resolve_right h6
  funext i
  by_cases hi : i = 1
  · subst i; simp [hzero,basisVector]
  · exact hcoords i hi

theorem middle_vector_reduction (x : Carrier K) (ht : trace x = 0)
    (hn : SplitOctonion.norm x = 0) (h7 : x 7 = 0) (hpair : x 5 ≠ 0 ∨ x 6 ≠ 0) :
    ∃ g ∈ parabolic (F := K), ∃ a : K, a ≠ 0 ∧ g.val x = a • basisVector 6 := by
  by_cases h6 : x 6 = 0
  · have h5 := hpair.resolve_right (not_not.mpr h6)
    let y := (weylR : Model K).val x
    have hy6 : y 6 ≠ 0 := by simpa [y,weylR,weylREquiv,weylRLinear,weylRApply] using h5
    have hy7 : y 7 = 0 := by simp [y,weylR,weylREquiv,weylRLinear,weylRApply,h7]
    refine ⟨middleReducer y * weylR,parabolic.mul_mem (middleReducer_mem _) weylR_mem_parabolic,
      y 6,hy6,?_⟩
    exact middleReducer_eq y ((automorphism_trace weylR x).trans ht)
      ((automorphism_norm weylR x).trans hn) hy7 hy6
  · exact ⟨middleReducer x,middleReducer_mem x,x 6,h6,middleReducer_eq x ht hn h7 h6⟩

/-- The bottom two strata lie in the three-dimensional totally singular subspace. -/
theorem lower_stratum_diagonal_zero (x : Carrier K) (ht : trace x = 0)
    (hn : SplitOctonion.norm x = 0) (h5 : x 5 = 0) (h6 : x 6 = 0) (h7 : x 7 = 0) :
    x 3 = 0 ∧ x 4 = 0 := by
  have h4 : x 4 = -x 3 := eq_neg_of_add_eq_zero_right ht
  have hs : x 3 = 0 := by
    have hh : x 3 * x 3 = 0 := by simpa [SplitOctonion.norm,h5,h6,h7,h4] using hn
    exact (mul_self_eq_zero.mp hh)
  exact ⟨hs,by simpa [hs] using h4⟩

theorem lower_vector_reduction (x : Carrier K) (ht : trace x = 0)
    (hn : SplitOctonion.norm x = 0) (h5 : x 5 = 0) (h6 : x 6 = 0) (h7 : x 7 = 0)
    (hpair : x 1 ≠ 0 ∨ x 2 ≠ 0) :
    ∃ g ∈ parabolic (F := K), ∃ a : K, a ≠ 0 ∧ g.val x = a • basisVector 1 := by
  obtain ⟨h3,h4⟩ := lower_stratum_diagonal_zero x ht hn h5 h6 h7
  have hF : ∀ a : K, rootF a ∈ parabolic := fun a => unipotent_le_parabolic
    (Subgroup.subset_closure (by simp))
  by_cases h2 : x 2 = 0
  · have h1 := hpair.resolve_right (not_not.mpr h2)
    refine ⟨rootF (x 0 / x 1),hF _,x 1,h1,?_⟩
    funext i
    fin_cases i <;> simp [rootF,rootFEquiv,rootFLinear,rootFApply,basisVector,
      h2,h3,h4,h5,h6,h7]
    field_simp
    ring
  · let y := (weylR * rootE (x 1 / x 2) : Model K).val x
    have hy : y = ![-x 0,-x 2,0,0,0,0,0,0] := by
      funext i
      fin_cases i <;> simp [y,weylR,weylREquiv,weylRLinear,weylRApply,
        rootE,rootEEquiv,rootELinear,rootEApply,h3,h4,h5,h6,h7]
      field_simp
      ring
    refine ⟨rootF (x 0 / x 2) * (weylR * rootE (x 1 / x 2)),
      parabolic.mul_mem (hF _) (parabolic.mul_mem weylR_mem_parabolic (rootE_mem_parabolic _)),
      -x 2,neg_ne_zero.mpr h2,?_⟩
    change (rootF (x 0 / x 2)).val y = _
    rw [hy]
    funext i
    fin_cases i <;> simp [rootF,rootFEquiv,rootFLinear,rootFApply,basisVector]
    field_simp
    ring

/-- Every nonzero singular vector reduces under the actual point stabilizer to
one of the four distinguished coordinate lines. -/
theorem parabolic_four_vector_representatives (x : Carrier K) (ht : trace x = 0)
    (hn : SplitOctonion.norm x = 0) (hx : x ≠ 0) :
    ∃ g ∈ parabolic (F := K), ∃ i : Fin 8, (i = 0 ∨ i = 1 ∨ i = 6 ∨ i = 7) ∧
      ∃ a : K, a ≠ 0 ∧ g.val x = a • basisVector i := by
  by_cases h7 : x 7 = 0
  · by_cases hm : x 5 ≠ 0 ∨ x 6 ≠ 0
    · obtain ⟨g,hg,a,ha,he⟩ := middle_vector_reduction x ht hn h7 hm
      exact ⟨g,hg,6,by simp,a,ha,he⟩
    · push Not at hm
      by_cases hl : x 1 ≠ 0 ∨ x 2 ≠ 0
      · obtain ⟨g,hg,a,ha,he⟩ := lower_vector_reduction x ht hn hm.1 hm.2 h7 hl
        exact ⟨g,hg,1,by simp,a,ha,he⟩
      · push Not at hl
        obtain ⟨h3,h4⟩ := lower_stratum_diagonal_zero x ht hn hm.1 hm.2 h7
        have he : x = x 0 • basisVector 0 := by
          funext i
          fin_cases i <;> simp [basisVector,hl.1,hl.2,h3,h4,hm.1,hm.2,h7]
        have h0 : x 0 ≠ 0 := by
          intro hh
          apply hx
          rw [he,hh,zero_smul]
        exact ⟨1,parabolic.one_mem,0,by simp,x 0,h0,he⟩
  · exact ⟨chartReducer x,unipotent_le_parabolic (chartReducer_mem_unipotent x),
      7,by simp,x 7,h7,chartReducer_eq x ht hn h7⟩

/-- The hyperplane polar to the first singular vector is preserved by its point stabilizer. -/
theorem pointStabilizer_last_coordinate (g : pointStabilizer (K := K)) (x : Carrier K) :
    (lineScalar g : K) * (g.val.val x) 7 = x 7 := by
  have hnorm (a : K) (x : Carrier K) :
      SplitOctonion.norm (a • basisVector 0 + x) = SplitOctonion.norm x + a*x 7 := by
    simp [SplitOctonion.norm,basisVector]
    ring
  have h := automorphism_norm g.val (basisVector 0 + x)
  rw [map_add,lineScalar_action,hnorm,automorphism_norm] at h
  have he : SplitOctonion.norm (basisVector 0 + x) = SplitOctonion.norm x + x 7 := by
    simpa using hnorm 1 x
  rw [he] at h
  exact add_left_cancel h

theorem pointStabilizer_last_zero_iff (g : pointStabilizer (K := K)) (x : Carrier K) :
    g.val.val x 7 = 0 ↔ x 7 = 0 := by
  have h := pointStabilizer_last_coordinate g x
  constructor
  · intro hx; simpa [hx] using h.symm
  · intro hx
    rw [hx] at h
    exact (mul_eq_zero.mp h).resolve_left (lineScalar g).ne_zero

def inLowerPlane (x : Carrier K) : Prop :=
  x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0 ∧ x 6 = 0 ∧ x 7 = 0

theorem inLowerPlane_iff_annihilator (x : Carrier K) : inLowerPlane x ↔
    SplitOctonion.mul (basisVector 0) x = 0 ∧ SplitOctonion.mul x (basisVector 0) = 0 := by
  constructor
  · rintro ⟨h3,h4,h5,h6,h7⟩
    constructor <;> funext i <;> fin_cases i <;>
      simp [SplitOctonion.mul,basisVector,h3,h4,h5,h6,h7]
  · rintro ⟨hl,hr⟩
    have h3 := congrFun hr 0
    have h4 := congrFun hl 0
    have h5 := congrFun hl 1
    have h6 := congrFun hl 2
    have h7 := congrFun hl 3
    simp [SplitOctonion.mul,basisVector] at h3 h4 h5 h6 h7
    exact ⟨h3,h4,h5,h6,h7⟩

theorem pointStabilizer_lowerPlane_iff (g : pointStabilizer (K := K)) (x : Carrier K) :
    inLowerPlane (g.val.val x) ↔ inLowerPlane x := by
  rw [inLowerPlane_iff_annihilator,inLowerPlane_iff_annihilator]
  have hl := automorphism_mul g.val (basisVector 0) x
  have hr := automorphism_mul g.val x (basisVector 0)
  rw [lineScalar_action,smul_mul] at hl
  rw [lineScalar_action,SplitOctonion.mul_smul] at hr
  constructor
  · rintro ⟨h1,h2⟩
    constructor
    · apply g.val.val.injective
      rw [hl,h1,smul_zero,map_zero]
    · apply g.val.val.injective
      rw [hr,h2,smul_zero,map_zero]
  · rintro ⟨h1,h2⟩
    rw [h1,map_zero] at hl
    rw [h2,map_zero] at hr
    constructor
    · exact (smul_eq_zero.mp hl.symm).resolve_left (lineScalar g).ne_zero
    · exact (smul_eq_zero.mp hr.symm).resolve_left (lineScalar g).ne_zero

def orbitBasisIndex : Fin 4 → Fin 8 := ![0,1,6,7]

def orbitPoint (i : Fin 4) : SingularPoints K :=
  singularPointMk K (basisVector (orbitBasisIndex i))
    (by intro h; have hh := congrFun h (orbitBasisIndex i); simp [basisVector] at hh)
    (by fin_cases i <;> simp [trace,basisVector,orbitBasisIndex])
    (by fin_cases i <;> simp [SplitOctonion.norm,basisVector,orbitBasisIndex])

/-- Four explicit singular lines cover the point-stabilizer orbits. -/
theorem parabolic_four_point_representatives (p : SingularPoints K) :
    ∃ g : parabolic (F := K), ∃ i : Fin 4, g.val • p = orbitPoint i := by
  obtain ⟨g,hg,i,hi,a,ha,he⟩ := parabolic_four_vector_representatives p.val.rep
    p.property.1 p.property.2 p.val.rep_nonzero
  have hline (j : Fin 4) (hj : orbitBasisIndex j = i) : g • p = orbitPoint j := by
    rw [← singularPointMk_rep K p,singularPointMk_smul,orbitPoint]
    apply Subtype.ext
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    exact ⟨a,by simpa [hj] using he.symm⟩
  rcases hi with rfl|rfl|rfl|rfl
  · exact ⟨⟨g,hg⟩,0,hline 0 rfl⟩
  · exact ⟨⟨g,hg⟩,1,hline 1 rfl⟩
  · exact ⟨⟨g,hg⟩,2,hline 2 rfl⟩
  · exact ⟨⟨g,hg⟩,3,hline 3 rfl⟩

theorem pointStabilizer_firstLine_iff (g : pointStabilizer (K := K)) (x : Carrier K) :
    (∃ a : K, g.val.val x = a • basisVector 0) ↔ ∃ a : K, x = a • basisVector 0 := by
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨a/(lineScalar g : K),?_⟩
    apply g.val.val.injective
    rw [ha,map_smul,lineScalar_action,smul_smul,div_mul_cancel₀ _ (lineScalar g).ne_zero]
  · rintro ⟨a,rfl⟩
    exact ⟨a*(lineScalar g : K),by rw [map_smul,lineScalar_action,smul_smul]⟩

private theorem firstLine_basis_iff (i : Fin 8) (a : K) (ha : a ≠ 0) :
    (∃ b : K, a • (basisVector i : Carrier K) = b • basisVector 0) ↔ i = 0 := by
  constructor
  · rintro ⟨b,hb⟩
    by_contra hi
    have h := congrFun hb i
    simp [basisVector,hi] at h
    exact ha h
  · rintro rfl
    exact ⟨a,rfl⟩

/-- The four distinguished lines lie in pairwise different actual stabilizer orbits. -/
theorem parabolic_orbitPoint_distinct (g : parabolic (F := K)) (i j : Fin 4)
    (h : g.val • orbitPoint (K := K) i = orbitPoint j) : i = j := by
  let p : pointStabilizer (K := K) := ⟨g.val,parabolic_le_pointStabilizer g.prop⟩
  rw [orbitPoint,singularPointMk_smul,orbitPoint] at h
  have hproj := congrArg Subtype.val h
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ _ _).mp hproj
  have he : p.val.val (basisVector (orbitBasisIndex i)) =
      (a : K) • basisVector (orbitBasisIndex j) := by
    simpa only [Units.smul_def] using ha.symm
  have hl := pointStabilizer_last_zero_iff p (basisVector (orbitBasisIndex i))
  have hw := pointStabilizer_lowerPlane_iff p (basisVector (orbitBasisIndex i))
  have hf := pointStabilizer_firstLine_iff p (basisVector (orbitBasisIndex i))
  rw [he] at hl hw hf
  have hf' : orbitBasisIndex j = 0 ↔ orbitBasisIndex i = 0 := by
    have hi : (∃ b : K, (basisVector (orbitBasisIndex i) : Carrier K) = b • basisVector 0) ↔
        orbitBasisIndex i = 0 := by
      simpa only [one_smul] using firstLine_basis_iff (orbitBasisIndex i) (1 : K) one_ne_zero
    rwa [firstLine_basis_iff _ _ a.ne_zero,hi] at hf
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals simp [orbitBasisIndex,basisVector,inLowerPlane,a.ne_zero] at hl hw hf'

end Atlas.G2
