module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.IcosianComparison.Generators.Orbit.Data
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.IcosianComparison.Generators.GenerationCriterion
/-!
# From integer reflection matrices to the genuine root orbit

A reached matrix is witnessed by an element of the actual Hermitian lattice
stabilizer whose projective image belongs to the fixed pair subgroup. The
spanning-tree step preserves that witness. A sixth commutator power supplies
the axis reflection after quotienting by the central signs, and equality of
root points forces equality of their line reflections. Thus 315 distinct
reached matrices complete the existing root-orbit generation criterion.

The model and coordinate conventions are Gerald Höhn's ATLAS construction
(see LICENSES/ATLAS.txt); the fixed pair is for ATLAS `J2G1-P2`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
namespace Sporadic.LeechRelated.J2.IcosianComparison.Generators.OrbitCertificate
open Atlas.Conway Atlas.Algebra RelatorMatrices

abbrev pairSubgroup : Subgroup IcosianProjectiveModel := Subgroup.closure ({x, y} : Set IcosianProjectiveModel)

def Reached (R : ZMatrix) : Prop := ∃ g : icosianHermitianGroup,
  icosianProjectiveProjection g ∈ pairSubgroup ∧
  matrixHom (g * icosianAxisReflection 0 * g⁻¹) = decode R

theorem matrix_x : matrixHom xLift = decode zx := by
  rw [matrixHom_xLift, zx, decode_ofCoeffs]
  rfl

theorem matrix_y : matrixHom yLift = decode zy := by
  rw [matrixHom_yLift, zy, decode_ofCoeffs]
  rfl

theorem matrix_x_inv : matrixHom xLift⁻¹ = decode zxi := by
  rw [matrixHom_xLift_inv, zxi, decode_ofCoeffs]
  rfl

theorem matrix_y_inv : matrixHom yLift⁻¹ = decode zyi := by
  rw [matrixHom_yLift_inv, zyi, decode_ofCoeffs]
  rfl

theorem matrix_axis : matrixHom (icosianAxisReflection 0) = decode r0 := by
  rw [r0, decode_ofCoeffs]
  apply Matrix.ext
  intro i j
  change (icosianAxisReflection 0).val (Pi.single j 1) i = _
  rw [icosianAxisReflection_apply]
  fin_cases i <;> fin_cases j <;> ext <;> decide +kernel

theorem reached_zero : Reached r0 := by
  refine ⟨1, ?_, ?_⟩
  · rw [map_one]
    exact pairSubgroup.one_mem
  · simpa using matrix_axis

theorem reached_mul (g : icosianHermitianGroup) {A Ai R M S : ZMatrix}
    (hm : icosianProjectiveProjection g ∈ pairSubgroup)
    (hA : matrixHom g = decode A) (hAi : matrixHom g⁻¹ = decode Ai)
    (hR : Reached R) (hL : A * R = (8 : ℤ) • M)
    (hRight : M * Ai = (8 : ℤ) • S) : Reached S := by
  obtain ⟨w, hw, hmat⟩ := hR
  refine ⟨g * w, ?_, ?_⟩
  · rw [map_mul]
    exact pairSubgroup.mul_mem hm hw
  · have he : g * w * icosianAxisReflection 0 * (g * w)⁻¹ =
        g * (w * icosianAxisReflection 0 * w⁻¹) * g⁻¹ := by group
    rw [he, map_mul, map_mul, hA, hmat, hAi, decode_mul A R M hL,
      decode_mul M Ai S hRight]

theorem reached_x {R M S : ZMatrix} (hR : Reached R)
    (hL : zx * R = (8 : ℤ) • M) (hRight : M * zxi = (8 : ℤ) • S) : Reached S :=
  reached_mul xLift (Subgroup.subset_closure (by simp [x])) matrix_x matrix_x_inv hR hL hRight

theorem reached_y {R M S : ZMatrix} (hR : Reached R)
    (hL : zy * R = (8 : ℤ) • M) (hRight : M * zyi = (8 : ℤ) • S) : Reached S :=
  reached_mul yLift (Subgroup.subset_closure (by simp [y])) matrix_y matrix_y_inv hR hL hRight


theorem decode_neg (R : ZMatrix) : decode (-R) = -decode R := by
  simp [decode]

theorem sixth_matrix (hprod : zcomm4 * zcomm2 = (8 : ℤ) • (-r313)) :
    matrixHom ((xLift⁻¹ * yLift⁻¹ * xLift * yLift) ^ 6) = -decode r313 := by
  have h2 : decode zcomm2 = comm2 := by rw [zcomm2, decode_ofCoeffs]; rfl
  have h4 : decode zcomm4 = comm4 := by rw [zcomm4, decode_ofCoeffs]; rfl
  have hp := decode_mul zcomm4 zcomm2 (-r313) hprod
  rw [h2, h4, decode_neg] at hp
  simp only [map_pow, map_mul, matrixHom_xLift_inv, matrixHom_yLift_inv,
    matrixHom_xLift, matrixHom_yLift, c0_mul, c1_mul, comm_mul]
  calc
    comm ^ 6 = (comm ^ 2) ^ 2 * comm ^ 2 := by noncomm_ring
    _ = -decode r313 := by simp only [pow_two, comm2_mul, comm4_mul]; exact hp

theorem axis_mem_of_reached (hr : Reached r313)
    (hc : matrixHom ((xLift⁻¹ * yLift⁻¹ * xLift * yLift) ^ 6) = -decode r313) :
    icosianProjectiveReflection (icosianRootAxisPoint 0) ∈ pairSubgroup := by
  obtain ⟨g, hg, hmat⟩ := hr
  have he : (xLift⁻¹ * yLift⁻¹ * xLift * yLift) ^ 6 =
      icosianCentralSign * (g * icosianAxisReflection 0 * g⁻¹) := by
    apply matrixHom_injective
    rw [map_mul, matrixHom_centralSign, hmat, neg_one_mul]
    exact hc
  have hx : x ∈ pairSubgroup := Subgroup.subset_closure (by simp)
  have hy : y ∈ pairSubgroup := Subgroup.subset_closure (by simp)
  have hm : icosianProjectiveProjection ((xLift⁻¹ * yLift⁻¹ * xLift * yLift) ^ 6)
      ∈ pairSubgroup := by
    simp only [map_pow, map_mul, map_inv]
    exact pairSubgroup.pow_mem
      (pairSubgroup.mul_mem (pairSubgroup.mul_mem
        (pairSubgroup.mul_mem (pairSubgroup.inv_mem hx) (pairSubgroup.inv_mem hy)) hx) hy) 6
  have hs : icosianProjectiveProjection icosianCentralSign = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Or.inr rfl)
  rw [he, map_mul, hs, one_mul] at hm
  have ha := pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.inv_mem hg) hm) hg
  simp only [map_mul, map_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] at ha
  rw [← icosianProjectiveAxisReflection_line]
  exact ha

theorem top_of_certificate (hr : ∀ i : Fin 315, Reached (matrices i))
    (ha : icosianProjectiveReflection (icosianRootAxisPoint 0) ∈ pairSubgroup) :
    pairSubgroup = ⊤ := by
  classical
  choose g hg hmat using hr
  let gs : Fin 315 → pairSubgroup := fun i => ⟨icosianProjectiveProjection (g i), hg i⟩
  apply subgroup_eq_top_of_315_translates pairSubgroup (icosianRootAxisPoint 0) ha gs
  intro i j hij
  change icosianProjectiveProjection (g i) • icosianRootAxisPoint 0 =
    icosianProjectiveProjection (g j) • icosianRootAxisPoint 0 at hij
  simp only [icosianProjectivePointAction_mk] at hij
  have he := congrArg (fun p => matrixHom (icosianLineReflection p)) hij
  have haxis : icosianLineReflection (icosianRootAxisPoint 0) = icosianAxisReflection 0 :=
    icosianLineReflection_root _
  rw [← icosianLineReflection_conjugate, ← icosianLineReflection_conjugate, haxis,
    hmat i, hmat j] at he
  exact matrices_injective (decode_injective he)

end Sporadic.LeechRelated.J2.IcosianComparison.Generators.OrbitCertificate
