module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/OrbitClasses.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, public module boundaries, and Lean 4.33 proof adaptation.
-/

public import Theory.AtlasPort.LinearGroups.G2.PointStrataCount
public import Mathlib.Data.Fintype.Sum

/-! The four geometric orbit classes coincide with the parabolic orbits; their fibers have the computed subdegrees. -/

@[expose] public section

noncomputable section
namespace Atlas.G2
open Atlas.SplitOctonion
variable {K : Type*} [Field K]

def orbitTransport (p : SingularPoints K) : parabolic (F := K) :=
  (parabolic_four_point_representatives p).choose

def orbitClass (p : SingularPoints K) : Fin 4 :=
  (parabolic_four_point_representatives p).choose_spec.choose

theorem orbitTransport_action (p : SingularPoints K) :
    (orbitTransport p).val • p = orbitPoint (orbitClass p) :=
  (parabolic_four_point_representatives p).choose_spec.choose_spec

@[simp] theorem orbitClass_orbitPoint (i : Fin 4) : orbitClass (orbitPoint (K := K) i) = i :=
  (parabolic_orbitPoint_distinct _ _ _ (orbitTransport_action (orbitPoint i))).symm

theorem orbitClass_eq_iff (p q : SingularPoints K) : orbitClass p = orbitClass q ↔
    ∃ g : parabolic (F := K), g.val • p = q := by
  constructor
  · intro h
    refine ⟨(orbitTransport q)⁻¹ * orbitTransport p,?_⟩
    change ((orbitTransport q).val⁻¹ * (orbitTransport p).val) • p = q
    rw [SemigroupAction.mul_smul,orbitTransport_action,h,← orbitTransport_action q,inv_smul_smul]
  · rintro ⟨g,hg⟩
    apply parabolic_orbitPoint_distinct ((orbitTransport q) * g * (orbitTransport p)⁻¹)
    change (((orbitTransport q).val * g.val) * (orbitTransport p).val⁻¹) • _ = _
    rw [← orbitTransport_action p,SemigroupAction.mul_smul,inv_smul_smul,
      SemigroupAction.mul_smul,hg,orbitTransport_action]

@[simp] theorem orbitClass_smul (g : parabolic (F := K)) (p : SingularPoints K) :
    orbitClass (g.val • p) = orbitClass p :=
  ((orbitClass_eq_iff p (g.val • p)).mpr ⟨g,rfl⟩).symm

theorem orbitClass_zero_iff (p : SingularPoints K) : orbitClass p = 0 ↔ p = firstPoint := by
  have h0 : orbitPoint (K := K) 0 = firstPoint := rfl
  constructor
  · intro h
    have he := orbitTransport_action p
    rw [h,h0] at he
    have hfix : (orbitTransport p).val • firstPoint = firstPoint :=
      parabolic_le_pointStabilizer (orbitTransport p).prop
    exact (MulAction.injective (orbitTransport p).val) (he.trans hfix.symm)
  · rintro rfl
    rw [← h0,orbitClass_orbitPoint]

theorem orbitTransport_rep (p : SingularPoints K) : ∃ a : Kˣ,
    (orbitTransport p).val.val p.val.rep = (a : K) • basisVector (orbitBasisIndex (orbitClass p)) := by
  have h := orbitTransport_action p
  rw [← singularPointMk_rep K p,singularPointMk_smul,orbitPoint] at h
  have he := congrArg Subtype.val h
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ _ _).mp he
  exact ⟨a,by simpa only [Units.smul_def,singularPointMk_rep] using ha.symm⟩

theorem orbitClass_le_one_iff (p : SingularPoints K) : orbitClass p ≤ 1 ↔ inLowerPlane p.val.rep := by
  let g : pointStabilizer (K := K) := ⟨(orbitTransport p).val,
    parabolic_le_pointStabilizer (orbitTransport p).prop⟩
  obtain ⟨a,ha⟩ := orbitTransport_rep p
  have hw := pointStabilizer_lowerPlane_iff g p.val.rep
  change inLowerPlane ((orbitTransport p).val.val p.val.rep) ↔ _ at hw
  rw [ha] at hw
  have hflag : inLowerPlane ((a : K) • ((basisVector (orbitBasisIndex (orbitClass p))) : Carrier K)) ↔
      orbitClass p ≤ 1 := by
    generalize orbitClass p = i
    fin_cases i <;> simp [inLowerPlane,orbitBasisIndex,basisVector,a.ne_zero]
  exact hflag.symm.trans hw

theorem orbitClass_le_two_iff (p : SingularPoints K) : orbitClass p ≤ 2 ↔ p.val.rep 7 = 0 := by
  let g : pointStabilizer (K := K) := ⟨(orbitTransport p).val,
    parabolic_le_pointStabilizer (orbitTransport p).prop⟩
  obtain ⟨a,ha⟩ := orbitTransport_rep p
  have hw := pointStabilizer_last_zero_iff g p.val.rep
  change (orbitTransport p).val.val p.val.rep 7 = 0 ↔ _ at hw
  rw [ha] at hw
  have hflag : ((a : K) • ((basisVector (orbitBasisIndex (orbitClass p))) : Carrier K)) 7 = 0 ↔
      orbitClass p ≤ 2 := by
    generalize orbitClass p = i
    fin_cases i <;> simp [orbitBasisIndex,basisVector,a.ne_zero]
  exact hflag.symm.trans hw

private theorem card_class_step [Finite K] (k : Fin 4) (hk : k.val < 3) :
    Nat.card {p : SingularPoints K // orbitClass p ≤ ⟨k.val+1,by omega⟩} =
      Nat.card {p : SingularPoints K // orbitClass p ≤ k} +
        Nat.card {p : SingularPoints K // orbitClass p = ⟨k.val+1,by omega⟩} := by
  classical
  let l : Fin 4 := ⟨k.val+1,by omega⟩
  have h : ∀ p : SingularPoints K, orbitClass p ≤ l ↔ orbitClass p ≤ k ∨ orbitClass p = l := by
    intro p
    simp only [Fin.le_def,Fin.ext_iff,l]
    omega
  rw [Nat.card_congr (Equiv.subtypeEquivRight h),
    Nat.card_congr (subtypeOrEquiv _ _ (show Disjoint
      (fun p : SingularPoints K => orbitClass p ≤ k) (fun p => orbitClass p = l) from by
        apply Set.disjoint_left.mpr
        intro p h1 h2
        have hh := congrArg Fin.val h2
        change (orbitClass p).val = k.val+1 at hh
        change (orbitClass p).val ≤ k.val at h1
        omega)),Nat.card_sum]

theorem card_orbitClass_zero [Finite K] : Nat.card {p : SingularPoints K // orbitClass p = 0} = 1 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight orbitClass_zero_iff)]
  exact Nat.card_unique

theorem card_orbitClass_le_one [Finite K] :
    Nat.card {p : SingularPoints K // orbitClass p ≤ 1} = 1 + Nat.card K + Nat.card K^2 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight orbitClass_le_one_iff),card_lowerSingularPoints]
  rw [← Nat.geomSum_eq (Finite.one_lt_card (α := K)) 3]
  simp [Finset.sum_range_succ]

theorem card_orbitClass_le_two [Finite K] :
    Nat.card {p : SingularPoints K // orbitClass p ≤ 2} =
      1 + Nat.card K + Nat.card K^2 + Nat.card K^3 + Nat.card K^4 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight orbitClass_le_two_iff),card_polarSingularPoints]
  rw [← Nat.geomSum_eq (Finite.one_lt_card (α := K)) 5]
  simp [Finset.sum_range_succ]

theorem card_orbitClass_le_three [Finite K] :
    Nat.card {p : SingularPoints K // orbitClass p ≤ 3} =
      1 + Nat.card K + Nat.card K^2 + Nat.card K^3 + Nat.card K^4 + Nat.card K^5 := by
  have he : {p : SingularPoints K // orbitClass p ≤ 3} ≃ SingularPoints K :=
    { toFun := Subtype.val
      invFun := fun p => ⟨p,by have := (orbitClass p).isLt; omega⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr he,card_singularPoints_sum]
  simp [Finset.sum_range_succ]

theorem card_orbitClass_one [Finite K] :
    Nat.card {p : SingularPoints K // orbitClass p = 1} = Nat.card K * (Nat.card K+1) := by
  have h := card_class_step (K := K) 0 (by decide)
  have h0 : Nat.card {p : SingularPoints K // orbitClass p ≤ 0} = 1 := by
    simpa only [le_zero_iff] using card_orbitClass_zero (K := K)
  change Nat.card {p : SingularPoints K // orbitClass p ≤ 1} =
    Nat.card {p : SingularPoints K // orbitClass p ≤ 0} +
      Nat.card {p : SingularPoints K // orbitClass p = 1} at h
  rw [card_orbitClass_le_one,h0] at h
  nlinarith

theorem card_orbitClass_two [Finite K] :
    Nat.card {p : SingularPoints K // orbitClass p = 2} = Nat.card K^3 * (Nat.card K+1) := by
  have h := card_class_step (K := K) 1 (by decide)
  change Nat.card {p : SingularPoints K // orbitClass p ≤ 2} =
    Nat.card {p : SingularPoints K // orbitClass p ≤ 1} +
      Nat.card {p : SingularPoints K // orbitClass p = 2} at h
  rw [card_orbitClass_le_two,card_orbitClass_le_one] at h
  nlinarith

theorem card_orbitClass_three [Finite K] :
    Nat.card {p : SingularPoints K // orbitClass p = 3} = Nat.card K^5 := by
  have h := card_class_step (K := K) 2 (by decide)
  change Nat.card {p : SingularPoints K // orbitClass p ≤ 3} =
    Nat.card {p : SingularPoints K // orbitClass p ≤ 2} +
      Nat.card {p : SingularPoints K // orbitClass p = 3} at h
  rw [card_orbitClass_le_three,card_orbitClass_le_two] at h
  omega

end Atlas.G2
