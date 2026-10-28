module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechModTwoAction

/-!
# Explicit integral coordinates for the binary Leech quotient

The columns of `basisMatrix` and rows of `dualMatrix` lie in the literal
Leech lattice, and both matrix products are eight times the identity.
Integral Leech pairings therefore give inverse coordinate maps. Reducing these
integral coordinates identifies Λ/2Λ with the binary space of dimension 24 and
intertwines every actual Leech isometry with its matrix in this basis.

The small integer tables were derived from the existing Golay encoder and are
checked by kernel reduction. Membership is checked through `mem_leech`, rather
than inferred from ambient reduction modulo two. The construction is independent
of the noncomputably chosen `leechBasis`.

Source context: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284.
The Golay encoder and integral Leech model are the existing attributed ATLAS
ports; the explicit basis and reciprocal-matrix proof here are new.
-/

open Atlas.Codes Atlas.Lattices
open scoped BigOperators Matrix
@[expose] public section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.StandardCoordinates

def flat : Omega ≃ Fin 24 := (hexIndexEquiv.prodCongr (Equiv.refl (Fin 4))).trans finProdFinEquiv

def basisMatrix : Matrix (Fin 24) (Fin 24) ℤ :=
  ![![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![1,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![1,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![1,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![1,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![1,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![1,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![1,2,2,2,2,2,2,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![1,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![1,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![1,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![1,2,2,2,0,0,0,0,2,2,2,4,0,0,0,0,0,0,0,0,0,0,0,0],
    ![1,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0],
    ![1,2,0,0,2,2,0,0,2,2,0,0,2,4,0,0,0,0,0,0,0,0,0,0],
    ![1,2,2,0,2,0,2,0,0,2,2,0,2,0,4,0,0,0,0,0,0,0,0,0],
    ![1,2,0,2,0,2,2,0,2,0,2,0,2,0,0,4,0,0,0,0,0,0,0,0],
    ![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0],
    ![1,0,2,0,2,0,2,0,2,2,0,0,0,0,0,0,2,4,0,0,0,0,0,0],
    ![1,0,0,2,2,2,0,0,2,0,2,0,0,0,0,0,2,0,4,0,0,0,0,0],
    ![1,2,0,0,0,2,2,0,0,2,2,0,0,0,0,0,2,0,0,4,0,0,0,0],
    ![1,2,2,2,2,0,0,0,2,0,0,0,2,0,0,0,2,0,0,0,4,0,0,0],
    ![1,0,0,2,2,2,2,0,0,2,0,0,2,0,0,0,2,0,0,0,0,4,0,0],
    ![1,0,2,0,0,2,0,0,2,2,2,0,2,0,0,0,2,0,0,0,0,0,4,0],
    ![5,0,2,2,0,0,2,4,0,0,2,4,2,4,4,4,2,4,4,4,4,4,4,8]]

def dualMatrix : Matrix (Fin 24) (Fin 24) ℤ :=
  ![![8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![-4,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![-4,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![-4,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![-4,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![-4,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![-4,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![10,-2,-2,-2,-2,-2,-2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![-4,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![-4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![-4,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![10,-2,-2,-2,0,0,0,0,-2,-2,-2,2,0,0,0,0,0,0,0,0,0,0,0,0],
    ![-4,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0],
    ![10,-2,0,0,-2,-2,0,0,-2,-2,0,0,-2,2,0,0,0,0,0,0,0,0,0,0],
    ![12,-2,-2,0,-2,0,-2,0,0,-2,-2,0,-2,0,2,0,0,0,0,0,0,0,0,0],
    ![12,-2,0,-2,0,-2,-2,0,-2,0,-2,0,-2,0,0,2,0,0,0,0,0,0,0,0],
    ![-4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0],
    ![10,0,-2,0,-2,0,-2,0,-2,-2,0,0,0,0,0,0,-2,2,0,0,0,0,0,0],
    ![10,0,0,-2,-2,-2,0,0,-2,0,-2,0,0,0,0,0,-2,0,2,0,0,0,0,0],
    ![10,-2,0,0,0,-2,-2,0,0,-2,-2,0,0,0,0,0,-2,0,0,2,0,0,0,0],
    ![12,-2,-2,-2,-2,0,0,0,-2,0,0,0,-2,0,0,0,-2,0,0,0,2,0,0,0],
    ![12,0,0,-2,-2,-2,-2,0,0,-2,0,0,-2,0,0,0,-2,0,0,0,0,2,0,0],
    ![12,0,-2,0,0,-2,0,0,-2,-2,-2,0,-2,0,0,0,-2,0,0,0,0,0,2,0],
    ![-59,7,5,5,7,7,5,-1,7,7,5,-1,5,-1,-1,-1,5,-1,-1,-1,-1,-1,-1,1]]

def basisColumn (j : Fin 24) : IntegerCoordinates := fun i => basisMatrix (flat i) j
def dualRow (j : Fin 24) : IntegerCoordinates := fun i => dualMatrix j (flat i)

def golayCheck (w : BinaryWord) : Prop :=
  let d := golayRawDecoder w
  (∑ i, d.2.1 i) = 0 ∧
    jWord (hexEncoder (hexDecoder d.1)) + rho d.2.1 + d.2.2 • eta = w

instance (w : BinaryWord) : Decidable (golayCheck w) := inferInstanceAs (Decidable (_ ∧ _))

theorem golayCheck_sound {w : BinaryWord} (h : golayCheck w) : w ∈ golay := by
  let d := golayRawDecoder w
  refine ⟨(⟨hexEncoder (hexDecoder d.1), ⟨_, rfl⟩⟩,
    ⟨d.2.1, (parityCode_mem 5 _).mpr h.1⟩, d.2.2), h.2⟩

def leechCheck (x : IntegerCoordinates) : Prop :=
  let m := x ((0,0),0) % 2
  (∀ i, x i % 2 = m) ∧ golayCheck (halfResidue x m) ∧ (∑ i, x i) % 8 = 4 * m

instance (x : IntegerCoordinates) : Decidable (leechCheck x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem leechCheck_sound {x : IntegerCoordinates} (h : leechCheck x) : x ∈ leech := by
  apply (mem_leech _).mpr
  refine ⟨x ((0,0),0) % 2, ?_, h.1, golayCheck_sound h.2.1, h.2.2⟩
  omega

theorem basisColumn_mem (j : Fin 24) : basisColumn j ∈ leech := by
  apply leechCheck_sound
  revert j
  decide

-- The dual rows are checked separately to bound kernel reduction and memory.
set_option Elab.async false in
private theorem dualCheck0 : leechCheck (dualRow 0) := by decide

set_option Elab.async false in
private theorem dualCheck1 : leechCheck (dualRow 1) := by decide

set_option Elab.async false in
private theorem dualCheck2 : leechCheck (dualRow 2) := by decide

set_option Elab.async false in
private theorem dualCheck3 : leechCheck (dualRow 3) := by decide

set_option Elab.async false in
private theorem dualCheck4 : leechCheck (dualRow 4) := by decide

set_option Elab.async false in
private theorem dualCheck5 : leechCheck (dualRow 5) := by decide

set_option Elab.async false in
private theorem dualCheck6 : leechCheck (dualRow 6) := by decide

set_option Elab.async false in
private theorem dualCheck7 : leechCheck (dualRow 7) := by decide

set_option Elab.async false in
private theorem dualCheck8 : leechCheck (dualRow 8) := by decide

set_option Elab.async false in
private theorem dualCheck9 : leechCheck (dualRow 9) := by decide

set_option Elab.async false in
private theorem dualCheck10 : leechCheck (dualRow 10) := by decide

set_option Elab.async false in
private theorem dualCheck11 : leechCheck (dualRow 11) := by decide

set_option Elab.async false in
private theorem dualCheck12 : leechCheck (dualRow 12) := by decide

set_option Elab.async false in
private theorem dualCheck13 : leechCheck (dualRow 13) := by decide

set_option Elab.async false in
private theorem dualCheck14 : leechCheck (dualRow 14) := by decide

set_option Elab.async false in
private theorem dualCheck15 : leechCheck (dualRow 15) := by decide

set_option Elab.async false in
private theorem dualCheck16 : leechCheck (dualRow 16) := by decide

set_option Elab.async false in
private theorem dualCheck17 : leechCheck (dualRow 17) := by decide

set_option Elab.async false in
private theorem dualCheck18 : leechCheck (dualRow 18) := by decide

set_option Elab.async false in
private theorem dualCheck19 : leechCheck (dualRow 19) := by decide

set_option Elab.async false in
private theorem dualCheck20 : leechCheck (dualRow 20) := by decide

set_option Elab.async false in
private theorem dualCheck21 : leechCheck (dualRow 21) := by decide

set_option Elab.async false in
private theorem dualCheck22 : leechCheck (dualRow 22) := by decide

set_option Elab.async false in
private theorem dualCheck23 : leechCheck (dualRow 23) := by decide

set_option Elab.async false in
theorem dualRow_mem (j : Fin 24) : dualRow j ∈ leech := by
  apply leechCheck_sound
  fin_cases j
  · exact dualCheck0
  · exact dualCheck1
  · exact dualCheck2
  · exact dualCheck3
  · exact dualCheck4
  · exact dualCheck5
  · exact dualCheck6
  · exact dualCheck7
  · exact dualCheck8
  · exact dualCheck9
  · exact dualCheck10
  · exact dualCheck11
  · exact dualCheck12
  · exact dualCheck13
  · exact dualCheck14
  · exact dualCheck15
  · exact dualCheck16
  · exact dualCheck17
  · exact dualCheck18
  · exact dualCheck19
  · exact dualCheck20
  · exact dualCheck21
  · exact dualCheck22
  · exact dualCheck23

theorem basis_mul_dual : basisMatrix * dualMatrix = (8 : ℤ) • (1 : Matrix (Fin 24) (Fin 24) ℤ) := by
  ext i j
  revert i j
  decide

theorem dual_mul_basis : dualMatrix * basisMatrix = (8 : ℤ) • (1 : Matrix (Fin 24) (Fin 24) ℤ) := by
  ext i j
  revert i j
  decide

noncomputable section

def basisVector (j : Fin 24) : leech := ⟨basisColumn j, basisColumn_mem j⟩
def dualVector (j : Fin 24) : leech := ⟨dualRow j, dualRow_mem j⟩

def latticeCoordinates : leech →ₗ[ℤ] (Fin 24 → ℤ) where
  toFun x j := leechIntegralPairing (dualVector j) x
  map_add' x y := by funext j; exact leechIntegralPairing_add_right _ _ _
  map_smul' r x := by
    funext j
    have ha := leechIntegralPairing_mul (dualVector j) (r • x)
    have hb := leechIntegralPairing_mul (dualVector j) x
    change 8 * _ = integerDot (dualRow j) (r • x.val) at ha
    change 8 * _ = integerDot (dualRow j) x.val at hb
    simp only [integerDot, Pi.smul_apply, smul_eq_mul] at ha hb ⊢
    have hr : (∑ i, dualRow j i * (r * x.val i)) = r * ∑ i, dualRow j i * x.val i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hr, ← hb] at ha
    change _ = r * _
    nlinarith only [ha]

def latticeSynthesis : (Fin 24 → ℤ) →ₗ[ℤ] leech :=
  Fintype.linearCombination ℤ basisVector

theorem latticeCoordinates_formula (x : leech) :
    (8 : ℤ) • latticeCoordinates x = dualMatrix *ᵥ (fun i => x.val (flat.symm i)) := by
  funext j
  change 8 * leechIntegralPairing (dualVector j) x = _
  rw [leechIntegralPairing_mul]
  change (∑ i, dualMatrix j (flat i) * x.val i) = _
  simpa only [Matrix.mulVec, dotProduct, Equiv.symm_apply_apply] using (Equiv.sum_comp flat (fun i => dualMatrix j i * x.val (flat.symm i)))

theorem latticeSynthesis_formula (x : Fin 24 → ℤ) (i : Omega) :
    (latticeSynthesis x).val i = (basisMatrix *ᵥ x) (flat i) := by
  simp only [latticeSynthesis, Fintype.linearCombination_apply,
    Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul, basisVector, basisColumn, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem synthesis_coordinates (x : leech) : latticeSynthesis (latticeCoordinates x) = x := by
  apply Subtype.ext
  funext i
  have he := congrFun (congrArg (fun v => basisMatrix *ᵥ v) (latticeCoordinates_formula x)) (flat i)
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, basis_mul_dual,
    Matrix.smul_mulVec, Matrix.one_mulVec] at he
  simp only [Pi.smul_apply, smul_eq_mul, Equiv.symm_apply_apply] at he
  rw [latticeSynthesis_formula]
  linarith

theorem coordinates_synthesis (x : Fin 24 → ℤ) : latticeCoordinates (latticeSynthesis x) = x := by
  have he := latticeCoordinates_formula (latticeSynthesis x)
  have hs : (fun i => (latticeSynthesis x).val (flat.symm i)) = basisMatrix *ᵥ x := by
    funext i
    rw [latticeSynthesis_formula, Equiv.apply_symm_apply]
  rw [hs, Matrix.mulVec_mulVec, dual_mul_basis, Matrix.smul_mulVec,
    Matrix.one_mulVec] at he
  funext j
  have hj := congrFun he j
  change 8 * _ = 8 * _ at hj
  linarith

def latticeCoordinatesEquiv : leech ≃ₗ[ℤ] (Fin 24 → ℤ) :=
  { latticeCoordinates with
    invFun := latticeSynthesis
    left_inv := synthesis_coordinates
    right_inv := coordinates_synthesis }

def binaryReduction : leech →+ (Fin 24 → Bit) where
  toFun x j := (latticeCoordinates x j : Bit)
  map_zero' := by ext j; simp
  map_add' x y := by ext j; simp

theorem binaryReduction_surjective : Function.Surjective binaryReduction := by
  intro x
  refine ⟨latticeSynthesis (fun i => (x i).val), ?_⟩
  ext j
  change ((latticeCoordinates (latticeSynthesis _) j : ℤ) : Bit) = x j
  rw [coordinates_synthesis]
  simp

theorem binaryReduction_kernel : twiceLeech = binaryReduction.ker := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change binaryReduction ((2 : ℕ) • y) = 0
    rw [map_nsmul]
    ext j
    simp
  · intro hx
    have hd (j : Fin 24) : (2 : ℤ) ∣ latticeCoordinates x j := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
      exact congrFun hx j
    choose w hw using hd
    refine ⟨latticeSynthesis w, ?_⟩
    apply latticeCoordinatesEquiv.injective
    change latticeCoordinates ((2 : ℕ) • latticeSynthesis w) = latticeCoordinates x
    rw [map_nsmul, coordinates_synthesis]
    funext j
    exact (hw j).symm

def binaryCoordinates : LeechModTwo ≃ₗ[Bit] (Fin 24 → Bit) :=
  let e := (QuotientAddGroup.quotientAddEquivOfEq binaryReduction_kernel).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective binaryReduction binaryReduction_surjective)
  { e with map_smul' := ZMod.map_smul e }

theorem binaryCoordinates_reduce (x : leech) :
    binaryCoordinates (leechReduction x) = binaryReduction x := rfl

theorem latticeCoordinates_basisVector (j : Fin 24) :
    latticeCoordinates (basisVector j) = Pi.single j 1 := by
  have h := coordinates_synthesis (Pi.single j 1)
  simpa only [latticeSynthesis, Fintype.linearCombination_apply_single, one_smul] using h

theorem binaryCoordinates_basisVector (j : Fin 24) :
    binaryCoordinates (leechReduction (basisVector j)) = Pi.single j 1 := by
  rw [binaryCoordinates_reduce]
  ext i
  change ((latticeCoordinates (basisVector j) i : ℤ) : Bit) = _
  rw [latticeCoordinates_basisVector]
  by_cases h : i = j <;> simp [h]

def actionMatrix (g : LeechIsometryGroup) : Matrix (Fin 24) (Fin 24) Bit :=
  fun i j => (latticeCoordinates (g.val (basisVector j)) i : Bit)

theorem binaryCoordinates_action (g : LeechIsometryGroup) (v : LeechModTwo) :
    binaryCoordinates (leechModTwoRepresentation g v) = actionMatrix g *ᵥ binaryCoordinates v := by
  have hm : binaryCoordinates.toLinearMap.comp
      ((leechModTwoRepresentation g).toLinearMap.comp binaryCoordinates.symm.toLinearMap) =
      Matrix.mulVecLin (actionMatrix g) := by
    apply (Pi.basisFun Bit (Fin 24)).ext
    intro j
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Pi.basisFun_apply]
    have hj : binaryCoordinates.symm (Pi.single j 1) = leechReduction (basisVector j) := by
      apply binaryCoordinates.injective
      rw [binaryCoordinates.apply_symm_apply, binaryCoordinates_basisVector]
    rw [hj, leechModTwoRepresentation_reduce, binaryCoordinates_reduce]
    ext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply,
      mul_ite, actionMatrix, binaryReduction]
  have h := congrArg (fun f : (Fin 24 → Bit) →ₗ[Bit] (Fin 24 → Bit) => f (binaryCoordinates v)) hm
  simpa using h

end
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.StandardCoordinates
