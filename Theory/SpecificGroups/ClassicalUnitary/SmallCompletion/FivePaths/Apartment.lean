module
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.PlaneCore.Levi.Kernel
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourParabolicCardinality
public import Theory.GroupAction.RankTwoCosetGeometry.PathCardinality
public import Theory.GroupAction.RankTwoCosetGeometry.PathOrderLowerBound
public import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# A native Hermitian five-path and its fixer

In a hyperbolic basis of the five-dimensional unitary space, two explicit
reflections give the standard apartment. Its ordered five-path fixer injects
into the diagonal subgroup of GL₂, hence has order at most (|F| - 1)².
All calculations take place in SU₅, before the actual projective quotient.
This supplies the native path action used in Aschbacher–Smith F.4.5–6
(`refs/quasithin.pdf`, pp.275–278); it makes no assertion about Weyl
relations in an arbitrary completion.
-/

@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.UnitaryFive.SmallCompletion.FivePaths
open PlaneCore
variable {F : Type*} [Field F] [CharP F 2]
variable (J : HermitianForm 5 F) (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)

def blockPerm (s : Equiv.Perm (Fin 5)) : GL (Fin 5) F :=
  Matrix.permMatrixHom.toHomUnits s

omit [CharP F 2] in
theorem blockPerm_val (s : Equiv.Perm (Fin 5)) :
    (blockPerm (F := F) s).val = (1 : Matrix (Fin 5) (Fin 5) F).submatrix s.symm id := by
  ext i j
  simp [blockPerm, Equiv.Perm.permMatrix, Matrix.submatrix, Matrix.one_apply]

def basisConjugate : Equiv.Perm (Fin 5) →* GL (Fin 5) F :=
  (MulAut.conj (planeBasisGL c)).toMonoidHom.comp Matrix.permMatrixHom.toHomUnits

theorem basisConjugate_val (s : Equiv.Perm (Fin 5)) :
    (basisConjugate c s).val = planeBasis c * (blockPerm s).val * planeBasisInv c := rfl

omit [CharP F 2] in
theorem ct_mul (A B : Matrix (Fin 5) (Fin 5) F) :
    J.conjTranspose (A*B) = J.conjTranspose B * J.conjTranspose A := by
  change ((A*B).map J.conj).transpose = (B.map J.conj).transpose * (A.map J.conj).transpose
  rw [Matrix.map_mul, Matrix.transpose_mul]

include hc hJ in
theorem basisConjugate_mem (s : Equiv.Perm (Fin 5))
    (hs : J.conjTranspose (blockPerm s).val * planeGram * (blockPerm s).val = planeGram) :
    basisConjugate c s ∈ J.specialSubgroup := by
  rw [J.mem_specialSubgroup_iff]
  constructor
  · rw [basisConjugate_val, ct_mul, ct_mul]
    have hgram : J.conjTranspose (planeBasis c) * J.form * planeBasis c = planeGram :=
      planeBasis_gram J c hc hJ
    have hi : J.conjTranspose (planeBasisInv c) * J.conjTranspose (planeBasis c) = 1 := by
      rw [← ct_mul, planeBasis_mul_inv]
      change ((J.conj : F →+* F).mapMatrix 1).transpose = 1
      rw [map_one, Matrix.transpose_one]
    calc
      _ = J.conjTranspose (planeBasisInv c) *
          (J.conjTranspose (blockPerm s).val *
            (J.conjTranspose (planeBasis c) * J.form * planeBasis c) *
              (blockPerm s).val) * planeBasisInv c := by simp only [mul_assoc]
      _ = J.conjTranspose (planeBasisInv c) * planeGram * planeBasisInv c := by rw [hgram,hs]
      _ = J.form := by
        rw [← hgram]
        calc
          _ = (J.conjTranspose (planeBasisInv c) * J.conjTranspose (planeBasis c)) *
            J.form * (planeBasis c * planeBasisInv c) := by simp only [mul_assoc]
          _ = _ := by rw [hi, planeBasis_mul_inv]; simp
  · apply Units.ext
    rw [GeneralLinearGroup.val_det_apply]
    have hd : (blockPerm (F := F) s).val.det = 1 := by
      change ((s⁻¹).permMatrix F).det = 1
      rw [Matrix.det_permutation]
      rcases Int.units_eq_one_or (Equiv.Perm.sign s⁻¹) with h | h <;> simp [h, CharTwo.neg_eq]
    rw [basisConjugate_val, Matrix.det_mul, Matrix.det_mul, hd, mul_one,
      ← Matrix.det_mul, planeBasis_mul_inv, Matrix.det_one]
    rfl

-- The reflections on a native hyperbolic apartment.
def pairPerm : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 3 4
def middlePerm : Equiv.Perm (Fin 5) := Equiv.swap 1 4

omit [CharP F 2] in
theorem pair_matrix : (blockPerm (F := F) pairPerm).val =
    !![0,1,0,0,0; 1,0,0,0,0; 0,0,1,0,0; 0,0,0,0,1; 0,0,0,1,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

omit [CharP F 2] in
theorem middle_matrix : (blockPerm (F := F) middlePerm).val =
    !![1,0,0,0,0; 0,0,0,0,1; 0,0,1,0,0; 0,0,0,1,0; 0,1,0,0,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

omit [CharP F 2] in
theorem pair_preserves :
    J.conjTranspose (blockPerm (F := F) pairPerm).val * planeGram *
      (blockPerm pairPerm).val = planeGram := by
  rw [pair_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_succ, planeGram]

omit [CharP F 2] in
theorem middle_preserves :
    J.conjTranspose (blockPerm (F := F) middlePerm).val * planeGram *
      (blockPerm middlePerm).val = planeGram := by
  rw [middle_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_succ, planeGram]

def pairSwap : J.specialSubgroup :=
  ⟨basisConjugate c pairPerm, basisConjugate_mem J c hc hJ pairPerm (pair_preserves J)⟩
def middleSwap : J.specialSubgroup :=
  ⟨basisConjugate c middlePerm, basisConjugate_mem J c hc hJ middlePerm (middle_preserves J)⟩


theorem pairSwap_sq : pairSwap J c hc hJ ^ 2 = 1 := by
  apply Subtype.ext
  change basisConjugate c pairPerm ^ 2 = 1
  rw [← map_pow, show pairPerm^2 = 1 from by decide, map_one]

theorem middleSwap_sq : middleSwap J c hc hJ ^ 2 = 1 := by
  apply Subtype.ext
  change basisConjugate c middlePerm ^ 2 = 1
  rw [← map_pow, show middlePerm^2 = 1 from by decide, map_one]

theorem pairSwap_act (v : Fin 5 → F) (hv : v ∈ plane F) :
    linearAction J (pairSwap J c hc hJ) v = ![v 2,v 2,v 0,v 0,0] := by
  have hThree : (3 : F) = 1 := by
    calc (3 : F) = 2 + 1 := by norm_num
         _ = 1 := by rw [CharTwo.two_eq_zero,zero_add]
  have hFour : (4 : F) = 0 := by
    calc (4 : F) = 2 * 2 := by norm_num
         _ = 0 := by rw [CharTwo.two_eq_zero,mul_zero]
  change (basisConjugate c pairPerm).val *ᵥ v = _
  rw [basisConjugate_val, pair_matrix, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  obtain ⟨h1,h3,h4⟩ := hv
  ext i
  fin_cases i <;> simp [planeBasis, planeBasisInv, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, h1,h3,h4] <;> ring_nf <;> simp only [hThree,hFour,mul_zero,zero_add,mul_one]

theorem middleSwap_act (v : Fin 5 → F) (hv : v ∈ line F) :
    linearAction J (middleSwap J c hc hJ) v = v := by
  have hThree : (3 : F) = 1 := by
    calc (3 : F) = 2 + 1 := by norm_num
         _ = 1 := by rw [CharTwo.two_eq_zero,zero_add]
  have hFour : (4 : F) = 0 := by
    calc (4 : F) = 2 * 2 := by norm_num
         _ = 0 := by rw [CharTwo.two_eq_zero,mul_zero]
  change (basisConjugate c middlePerm).val *ᵥ v = _
  rw [basisConjugate_val, middle_matrix, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  obtain ⟨h1,h2,h3,h4⟩ := hv
  ext i
  fin_cases i <;> simp [planeBasis, planeBasisInv, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, h1,h2,h3,h4] <;> ring_nf <;> simp only [hThree,hFour,mul_zero,zero_add,mul_one]

omit [CharP F 2] in
private theorem mem_stabilizer_of_involution (g : J.specialSubgroup) (hg : g^2 = 1)
    (W : Submodule F (Fin 5 → F)) (h : ∀ v ∈ W, linearAction J g v ∈ W) :
    g ∈ specialStabilizer J W := by
  rw [mem_specialStabilizer_iff]
  intro v
  constructor
  · intro hv
    have hh := h _ hv
    change linearAction J g (linearAction J g v) ∈ W at hh
    have he : linearAction J g (linearAction J g v) = v := by
      change (linearAction J g * linearAction J g) v = v
      rw [← map_mul, ← pow_two,hg,map_one]
      rfl
    rwa [he] at hh
  · exact h v

theorem pairSwap_mem_plane : pairSwap J c hc hJ ∈ specialStabilizer J (plane F) := by
  apply mem_stabilizer_of_involution J _ (pairSwap_sq J c hc hJ)
  intro v hv
  rw [pairSwap_act J c hc hJ v hv]
  simp [plane]

theorem middleSwap_mem_line : middleSwap J c hc hJ ∈ specialStabilizer J (line F) := by
  apply mem_stabilizer_of_involution J _ (middleSwap_sq J c hc hJ)
  intro v hv
  rwa [middleSwap_act J c hc hJ v hv]

/-- Matrices in the native hyperbolic basis. -/
def coordinates : J.specialSubgroup →* GL (Fin 5) F :=
  (MulAut.conj (planeBasisGL c)⁻¹).toMonoidHom.comp J.specialSubgroup.subtype

theorem coordinates_injective : Function.Injective (coordinates J c) :=
  (MulAut.conj (planeBasisGL c)⁻¹).injective.comp Subtype.val_injective

theorem coordinates_val (g : J.specialSubgroup) :
    (coordinates J c g).val = planeBasisInv c * g.val.val * planeBasis c := rfl

theorem coordinates_pairSwap : coordinates J c (pairSwap J c hc hJ) = blockPerm pairPerm := by
  change (planeBasisGL c)⁻¹ *
    (planeBasisGL c * blockPerm pairPerm * (planeBasisGL c)⁻¹) * planeBasisGL c = _
  group

theorem coordinates_middleSwap : coordinates J c (middleSwap J c hc hJ) = blockPerm middlePerm := by
  change (planeBasisGL c)⁻¹ *
    (planeBasisGL c * blockPerm middlePerm * (planeBasisGL c)⁻¹) * planeBasisGL c = _
  group

def rotation : J.specialSubgroup := pairSwap J c hc hJ * middleSwap J c hc hJ

theorem rotation_coordinates : (coordinates J c (rotation J c hc hJ)).val =
    !![0,0,0,0,1; 1,0,0,0,0; 0,0,1,0,0; 0,1,0,0,0; 0,0,0,1,0] := by
  rw [rotation,map_mul,coordinates_pairSwap,coordinates_middleSwap]
  change (blockPerm pairPerm).val * (blockPerm middlePerm).val = _
  rw [pair_matrix,middle_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem rotation_sq_coordinates : (coordinates J c (rotation J c hc hJ ^ 2)).val =
    planeGram := by
  rw [map_pow,pow_two]
  change (coordinates J c (rotation J c hc hJ)).val *
    (coordinates J c (rotation J c hc hJ)).val = _
  rw [rotation_coordinates]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ,planeGram]

theorem rotation_fourth : rotation J c hc hJ ^ 4 = 1 := by
  apply coordinates_injective J c
  apply Units.ext
  rw [show 4 = 2*2 from rfl,pow_mul,map_pow,pow_two]
  change (coordinates J c (rotation J c hc hJ ^ 2)).val *
    (coordinates J c (rotation J c hc hJ ^ 2)).val = _
  rw [rotation_sq_coordinates,map_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planeGram,Matrix.mul_apply,Fin.sum_univ_succ]


theorem coordinate_column (g : J.specialSubgroup) (j : Fin 5) :
    (fun i => (coordinates J c g).val i j) =
      planeBasisInv c *ᵥ (g.val.val *ᵥ (fun i => planeBasis c i j)) := by
  ext i
  rw [coordinates_val,Matrix.mul_assoc]
  rfl

theorem coordinates_line (g : J.specialSubgroup)
    (hg : g ∈ specialStabilizer J (line F)) (i : Fin 5) (hi : i ≠ 0) :
    (coordinates J c g).val i 0 = 0 := by
  have hv := (mem_specialStabilizer_iff J (line F) g).mp hg
    (fun i => planeBasis c i 0) |>.mpr (by simp [planeBasis,line])
  let v := g.val.val *ᵥ (fun i => planeBasis c i 0)
  change v 1 = v 0 ∧ v 2 = 0 ∧ v 3 = 0 ∧ v 4 = 0 at hv
  have he := congrFun (coordinate_column J c g 0) i
  rw [he]
  change (planeBasisInv c *ᵥ v) i = 0
  fin_cases i <;> simp_all [planeBasisInv,Matrix.mulVec,dotProduct,
    Fin.sum_univ_succ,CharTwo.add_self_eq_zero]

theorem coordinates_plane (g : J.specialSubgroup)
    (hg : g ∈ specialStabilizer J (plane F)) (i j : Fin 5)
    (hi : i = 2 ∨ i = 3 ∨ i = 4) (hj : j = 0 ∨ j = 1) :
    (coordinates J c g).val i j = 0 := by
  have hw : (fun i => planeBasis c i j) ∈ plane F := by
    rcases hj with rfl | rfl <;> simp [planeBasis,plane]
  have hv := (mem_specialStabilizer_iff J (plane F) g).mp hg _ |>.mpr hw
  let v := g.val.val *ᵥ (fun i => planeBasis c i j)
  change v 1 = v 0 ∧ v 3 = v 2 ∧ v 4 = 0 at hv
  have he := congrFun (coordinate_column J c g j) i
  rw [he]
  change (planeBasisInv c *ᵥ v) i = 0
  rcases hi with rfl | rfl | rfl <;>
    simp [planeBasisInv,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
      hv.1,hv.2.1,hv.2.2,CharTwo.add_self_eq_zero]

abbrev family (i : Bool) : Subgroup J.specialSubgroup :=
  if i then specialStabilizer J (plane F) else specialStabilizer J (line F)

open Subgroup.CosetGeometry.RankTwo SimpleGraph
open Subgroup.CosetGeometry (translationGraphIso incident_base incident_base_iff)
local notation "Pₛ" => family J
local notation "r" => rotation J c hc hJ

theorem rotation_not_mem (i : Bool) : r ∉ Pₛ i := by
  cases i
  · intro h
    have hh := coordinates_line J c r h 1 (by decide)
    rw [rotation_coordinates] at hh
    exact one_ne_zero hh
  · intro h
    have hh := coordinates_plane J c r h 3 1 (Or.inr (Or.inl rfl)) (Or.inr rfl)
    rw [rotation_coordinates] at hh
    exact one_ne_zero hh

def apartmentVertex (k : ℕ) (i : Bool) : Vertex Pₛ := r ^ k • base Pₛ i
local notation "a" => apartmentVertex J c hc hJ

theorem edge (k : ℕ) : (graph Pₛ).Adj (a k false) (a k true) :=
  (translationGraphIso Pₛ (r^k)).toHom.map_adj
    ⟨Bool.false_ne_true, incident_base Pₛ false true⟩

private theorem crossing_zero : (graph Pₛ).Adj (base Pₛ true) (r • base Pₛ false) := by
  have he : r • base Pₛ false = mkVertex Pₛ false (pairSwap J c hc hJ) := by
    change mkVertex Pₛ false (r * 1) = _
    rw [mul_one, mkVertex_eq]
    change r⁻¹ * pairSwap J c hc hJ ∈ specialStabilizer J (line F)
    have hh : r⁻¹ * pairSwap J c hc hJ = (middleSwap J c hc hJ)⁻¹ := by
      dsimp [rotation]
      group
    rw [hh]
    exact (specialStabilizer J (line F)).inv_mem (middleSwap_mem_line J c hc hJ)
  rw [he]
  refine ⟨show true ≠ false from Bool.false_ne_true.symm, ?_⟩
  exact (incident_base_iff Pₛ true _).mpr
    ⟨pairSwap J c hc hJ, pairSwap_mem_plane J c hc hJ, rfl⟩

theorem crossing (k : ℕ) : (graph Pₛ).Adj (a k true) (a (k+1) false) := by
  have h := (translationGraphIso Pₛ (r^k)).toHom.map_adj (crossing_zero J c hc hJ)
  change (graph Pₛ).Adj (r^k • base Pₛ true) (r^k • (r • base Pₛ false)) at h
  simpa only [apartmentVertex, pow_succ, mul_smul] using h

theorem different (k : ℕ) (i : Bool) : a (k+1) i ≠ a k i := by
  intro he
  have hh : r • base Pₛ i = base Pₛ i :=
    (MulAction.injective (r^k)) (by simpa only [apartmentVertex, pow_succ, mul_smul] using he)
  apply rotation_not_mem J c hc hJ i
  have hm : r ∈ MulAction.stabilizer J.specialSubgroup (base Pₛ i) := hh
  simpa only [base, CosetGeometry.stabilizer_base] using hm

def fivePath : BasedWalk (graph Pₛ) 5 (a 0 false) :=
  ⟨⟨a 0 true,edge J c hc hJ 0⟩, ⟨⟨a 1 false,crossing J c hc hJ 0⟩,
    ⟨⟨a 1 true,edge J c hc hJ 1⟩, ⟨⟨a 2 false,crossing J c hc hJ 1⟩,
      ⟨⟨a 2 true,edge J c hc hJ 2⟩, PUnit.unit⟩⟩⟩⟩⟩

def reverseFivePath : BasedWalk (graph Pₛ) 5 (a 2 true) :=
  ⟨⟨a 2 false,(edge J c hc hJ 2).symm⟩, ⟨⟨a 1 true,(crossing J c hc hJ 1).symm⟩,
    ⟨⟨a 1 false,(edge J c hc hJ 1).symm⟩, ⟨⟨a 0 true,(crossing J c hc hJ 0).symm⟩,
      ⟨⟨a 0 false,(edge J c hc hJ 0).symm⟩, PUnit.unit⟩⟩⟩⟩⟩

theorem fivePath_nonbacktracking : (fivePath J c hc hJ).Nonbacktracking :=
  ⟨different J c hc hJ 0 false, different J c hc hJ 0 true,
    different J c hc hJ 1 false, different J c hc hJ 1 true, trivial⟩

theorem reverseFivePath_nonbacktracking : (reverseFivePath J c hc hJ).Nonbacktracking :=
  ⟨(different J c hc hJ 1 true).symm, (different J c hc hJ 1 false).symm,
    (different J c hc hJ 0 true).symm, (different J c hc hJ 0 false).symm, trivial⟩


theorem rotation_inv_coordinates : (coordinates J c r⁻¹).val =
    !![0,1,0,0,0; 0,0,0,1,0; 0,0,1,0,0; 0,0,0,0,1; 1,0,0,0,0] := by
  have he : r⁻¹ = r^2*r := by
    apply inv_eq_of_mul_eq_one_left
    rw [← pow_succ, ← pow_succ, rotation_fourth]
  rw [he,map_mul]
  change (coordinates J c (r^2)).val * (coordinates J c r).val = _
  rw [rotation_sq_coordinates,rotation_coordinates]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planeGram,Matrix.mul_apply,Fin.sum_univ_succ]

theorem rotation_sq_inv : (r^2)⁻¹ = r^2 := by
  apply inv_eq_of_mul_eq_one_left
  rw [← pow_add,show 2+2=4 from rfl,rotation_fourth]

theorem coordinates_parameters (u : Parameters J) :
    (coordinates J c (Parameters.toSU hJ u)).val = Parameters.matrix u := by
  have hFour : (4 : F) = 0 := by
    calc (4 : F) = 2 * 2 := by norm_num
         _ = 0 := by rw [CharTwo.two_eq_zero,mul_zero]
  rw [coordinates_val]
  change planeBasisInv c * (Parameters.ambientGL u).val * planeBasis c = _
  rw [Parameters.ambientGL_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeBasisInv,planeBasis,Parameters.ambientMatrix,Parameters.matrix,
      Matrix.mul_apply,Fin.sum_univ_succ] <;> ring_nf <;>
        simp only [CharTwo.two_eq_zero,hFour,mul_zero,add_zero,zero_add]

theorem mem_stabilizer_apartment (g : J.specialSubgroup) (k : ℕ) (i : Bool) :
    g • a k i = a k i ↔ (r^k)⁻¹ * g * r^k ∈ Pₛ i := by
  change g ∈ MulAction.stabilizer J.specialSubgroup (r^k • base Pₛ i) ↔ _
  have hv : r^k • base Pₛ i = mkVertex Pₛ i (r^k) := by
    change mkVertex Pₛ i (r^k * 1) = _
    rw [mul_one]
  rw [hv]
  exact CoverData.mem_stabilizer_mk i _ g

theorem fivePath_fixer_le_plane :
    pathStabilizer Pₛ (fivePath J c hc hJ) ≤ specialStabilizer J (plane F) := by
  intro g hg
  have h := (mem_stabilizer_apartment J c hc hJ g 0 true).mp
    (hg (a 0 true) (by simp [fivePath,BasedWalk.vertices]))
  simpa only [pow_zero,inv_one,one_mul,mul_one,family,ite_true] using h

theorem fivePath_fixer_line (g : J.specialSubgroup)
    (hg : g ∈ pathStabilizer Pₛ (fivePath J c hc hJ)) :
    g ∈ specialStabilizer J (line F) := by
  have h := (mem_stabilizer_apartment J c hc hJ g 0 false).mp
    (hg (a 0 false) (by simp [fivePath,BasedWalk.vertices]))
  simpa only [pow_zero,inv_one,one_mul,mul_one,family,Bool.false_eq_true,ite_false] using h

theorem fivePath_fixer_otherLine (g : J.specialSubgroup)
    (hg : g ∈ pathStabilizer Pₛ (fivePath J c hc hJ)) :
    r⁻¹ * g * r ∈ specialStabilizer J (line F) := by
  simpa only [pow_one,family,Bool.false_eq_true,ite_false] using
    (mem_stabilizer_apartment J c hc hJ g 1 false).mp
      (hg (a 1 false) (by simp [fivePath,BasedWalk.vertices]))

theorem fivePath_fixer_opposite (g : J.specialSubgroup)
    (hg : g ∈ pathStabilizer Pₛ (fivePath J c hc hJ)) :
    r^2 * g * r^2 ∈ specialStabilizer J (plane F) := by
  have hh := (mem_stabilizer_apartment J c hc hJ g 2 true).mp
    (hg (a 2 true) (by simp [fivePath,BasedWalk.vertices]))
  simpa only [rotation_sq_inv,family,ite_true] using hh

def fivePathRestriction : pathStabilizer Pₛ (fivePath J c hc hJ) →* GL (Fin 2) F :=
  (planeRestriction J).comp (inclusion (fivePath_fixer_le_plane J c hc hJ))

theorem fivePathRestriction_injective : Function.Injective (fivePathRestriction J c hc hJ) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro g hg
  apply Subtype.ext
  change g.val = 1
  have hf : planeRestriction J (inclusion (fivePath_fixer_le_plane J c hc hJ) g) = 1 := hg
  obtain ⟨u,hu⟩ := exists_parameters_of_fixes_plane J hJ g.val
    ((planeRestriction_eq_one_iff J _).mp hf)
  have ho := fivePath_fixer_opposite J c hc hJ g.val g.property
  have hz (i j : Fin 5) (hi : i = 2 ∨ i = 3 ∨ i = 4) (hj : j = 0 ∨ j = 1) :=
    coordinates_plane J c _ ho i j hi hj
  have h20 := hz 2 0 (Or.inl rfl) (Or.inl rfl)
  have h21 := hz 2 1 (Or.inl rfl) (Or.inr rfl)
  have h30 := hz 3 0 (Or.inr (Or.inl rfl)) (Or.inl rfl)
  have h31 := hz 3 1 (Or.inr (Or.inl rfl)) (Or.inr rfl)
  have h40 := hz 4 0 (Or.inr (Or.inr rfl)) (Or.inl rfl)
  have h41 := hz 4 1 (Or.inr (Or.inr rfl)) (Or.inr rfl)
  have he : (coordinates J c (r^2*g.val*r^2)).val =
      planeGram * Parameters.matrix u * planeGram := by
    rw [←hu,map_mul,map_mul]
    change (coordinates J c (r^2)).val * (coordinates J c (Parameters.toSU hJ u)).val *
      (coordinates J c (r^2)).val = _
    rw [rotation_sq_coordinates,coordinates_parameters]
  rw [he] at h20 h21 h30 h31 h40 h41
  simp only [planeGram,Parameters.matrix,Matrix.mul_apply,Fin.sum_univ_succ] at h20 h21 h30 h31 h40 h41
  simp at h20 h21 h30 h31 h40 h41
  have hu1 : u = 1 := by
    apply Parameters.ext
    · ext i
      fin_cases i
      · exact J.conj.injective (by simpa using h20)
      · exact J.conj.injective (by simpa using h21)
    · ext i j
      fin_cases i <;> fin_cases j <;> assumption
  rw [←hu,hu1,map_one]


theorem rotation_line (v : Fin 5 → F) (hv : v ∈ line F) :
    linearAction J r v = ![0,0,v 0,v 0,0] := by
  rw [rotation,map_mul]
  change linearAction J (pairSwap J c hc hJ) (linearAction J (middleSwap J c hc hJ) v) = _
  rw [middleSwap_act J c hc hJ v hv,pairSwap_act J c hc hJ v (line_le_plane F hv),hv.2.1]

theorem fivePathRestriction_diagonal (g : pathStabilizer Pₛ (fivePath J c hc hJ)) :
    (fivePathRestriction J c hc hJ g).val 1 0 = 0 ∧
      (fivePathRestriction J c hc hJ g).val 0 1 = 0 := by
  let A := fivePathRestriction J c hc hJ g
  let v₀ : Fin 5 → F := ![1,1,0,0,0]
  let v₁ : Fin 5 → F := ![0,0,1,1,0]
  have hv₀ : v₀ ∈ line F := by simp [v₀,line]
  have h₀ := planeRestriction_mulVec J (inclusion (fivePath_fixer_le_plane J c hc hJ) g) ![1,0]
  have h₁ := planeRestriction_mulVec J (inclusion (fivePath_fixer_le_plane J c hc hJ) g) ![0,1]
  change A.val *ᵥ ![1,0] = ![(linearAction J g.val v₀) 0,(linearAction J g.val v₀) 2] at h₀
  change A.val *ᵥ ![0,1] = ![(linearAction J g.val v₁) 0,(linearAction J g.val v₁) 2] at h₁
  constructor
  · have hh := (mem_specialStabilizer_iff J (line F) g.val).mp
      (fivePath_fixer_line J c hc hJ g.val g.property) v₀ |>.mpr hv₀
    have hz : (linearAction J g.val v₀) 2 = 0 := hh.2.1
    have he := congrFun h₀ 1
    simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_two,hz] using he
  · let b := r⁻¹*g.val*r
    have hb := (mem_specialStabilizer_iff J (line F) b).mp
      (fivePath_fixer_otherLine J c hc hJ g.val g.property) v₀ |>.mpr hv₀
    have hh := rotation_line J c hc hJ (linearAction J b v₀) hb
    have hr : linearAction J r v₀ = v₁ := rotation_line J c hc hJ v₀ hv₀
    have heq : linearAction J r (linearAction J b v₀) = linearAction J g.val v₁ := by
      rw [←hr]
      change (linearAction J r * linearAction J b) v₀ =
        (linearAction J g.val * linearAction J r) v₀
      rw [←map_mul,←map_mul]
      congr 2
      dsimp [b]
      group
    rw [heq] at hh
    have hz := congrFun hh 0
    have he := congrFun h₁ 0
    simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_two,hz] using he

/-- The ordered five-path fixer is bounded by the two free nonzero
hyperbolic eigenvalues. This bound is in SU, before its scalar quotient. -/
theorem fivePath_fixer_card [Finite F] :
    Nat.card (pathStabilizer Pₛ (fivePath J c hc hJ)) ≤ (Nat.card F - 1)^2 := by
  have hne (g : pathStabilizer Pₛ (fivePath J c hc hJ)) :
      (fivePathRestriction J c hc hJ g).val 0 0 ≠ 0 ∧
        (fivePathRestriction J c hc hJ g).val 1 1 ≠ 0 := by
    have hd := (fivePathRestriction J c hc hJ g).det_ne_zero
    obtain ⟨h10,h01⟩ := fivePathRestriction_diagonal J c hc hJ g
    rw [Matrix.det_fin_two,h10,h01,mul_zero,sub_zero] at hd
    exact mul_ne_zero_iff.mp hd
  let f (g : pathStabilizer Pₛ (fivePath J c hc hJ)) : Fˣ × Fˣ :=
    (Units.mk0 _ (hne g).1,Units.mk0 _ (hne g).2)
  have hf : Function.Injective f := by
    intro g h he
    apply fivePathRestriction_injective J c hc hJ
    apply Units.ext
    ext i j
    have h00 := congrArg (fun p : Fˣ × Fˣ => p.1.val) he
    have h11 := congrArg (fun p : Fˣ × Fˣ => p.2.val) he
    obtain ⟨g10,g01⟩ := fivePathRestriction_diagonal J c hc hJ g
    obtain ⟨h10,h01⟩ := fivePathRestriction_diagonal J c hc hJ h
    fin_cases i <;> fin_cases j
    · exact h00
    · exact g01.trans h01.symm
    · exact g10.trans h10.symm
    · exact h11
  have hh := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_prod,Nat.card_units,pow_two] using hh

theorem reverseFivePath_fixer :
    pathStabilizer Pₛ (reverseFivePath J c hc hJ) = pathStabilizer Pₛ (fivePath J c hc hJ) := by
  ext g
  change (∀ w ∈ (reverseFivePath J c hc hJ).vertices, g • w = w) ↔
    (∀ w ∈ (fivePath J c hc hJ).vertices, g • w = w)
  simp only [fivePath,reverseFivePath,BasedWalk.vertices,List.mem_cons,List.not_mem_nil,
    or_false,forall_eq_or_imp,forall_eq]
  tauto

end Theory.SpecificGroups.UnitaryFive.SmallCompletion.FivePaths
