module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.HighestWeight
public import Theory.AlgebraicGroup.RootSystems.IntegralRootCurveSimpleGeneration

/-!
# Coroot and simple-root geometry for the basic F4 weight cases

The faithful map from the algebraic carrier to its defining matrix units
identifies the positive coroot word with the inverse-parameter diagonal.
The integral Tits grading then gives the simple-reflection conjugation law.
Signed simple root curves generate all root curves by their chosen Tits routes.
These identities concern the actual closed carrier over an algebraically
closed field, with no finite-group recognition hypothesis.

The diagonal computations adapt
`ReeF4/ParabolicAmalgam/Geometry/CorootRealization.lean` from finite coefficient
fields to algebraically closed fields. Source: GLS3, §§1.9, 1.12, and 1.14;
Steinberg, *Lectures on Chevalley Groups*, Theorem 1 and Lemmas 5–6.
-/

public section

set_option linter.unusedSectionVars false

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
noncomputable section
namespace ReeF4.BinaryDegree.ExceptionalTensor.ZeroAndMiddle
variable {F : Type*} [Field F] [IsAlgClosed F]
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

def matrixToAmbient : (Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex F)ˣ →*
    Variety.Point (F4Chevalley.Ambient F) where
  toFun A := generalLinearRepresentationPoint
    (carrierBasis (P := typeF4RootPairing) (b := typeF4RootPairing_base))
    (Matrix.GeneralLinearGroup.toLin A)
  map_one' := by rw [map_one, generalLinearRepresentationPoint_one]
  map_mul' A B := by rw [map_mul, generalLinearRepresentationPoint_mul]

theorem matrixToAmbient_bijective : Function.Bijective (matrixToAmbient (F := F)) := by
  let e := glPointEquivOf F (F4Chevalley.BasisIndex → F)
    (carrierBasis (P := typeF4RootPairing) (b := typeF4RootPairing_base))
  have he (A : (Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex F)ˣ) :
      e (matrixToAmbient A) = Matrix.GeneralLinearGroup.toLin A :=
    glPointEquivOf_generalLinearRepresentationPoint _ _
  constructor
  · intro A B h
    apply Matrix.GeneralLinearGroup.toLin.injective
    rw [← he, ← he, h]
  · intro g
    refine ⟨Matrix.GeneralLinearGroup.toLin.symm (e g), ?_⟩
    apply e.injective
    rw [he, MulEquiv.apply_symm_apply]

def matrixAmbientEquiv := MulEquiv.ofBijective (matrixToAmbient (F := F)) matrixToAmbient_bijective

def carrierMatrix : Variety.Point (F4Chevalley.Carrier (k := F)) →*
    (Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex F)ˣ :=
  matrixAmbientEquiv.symm.toMonoidHom.comp (F4Chevalley.ambientClosedCarrier (k := F)).inclusion.onPoints

theorem carrierMatrix_injective : Function.Injective (carrierMatrix (F := F)) :=
  matrixAmbientEquiv.symm.injective.comp (F4Chevalley.ambientClosedCarrier (k := F)).inclusion_injective

@[simp] theorem carrierMatrix_root (r : F4Chevalley.Root) (t : F) :
    carrierMatrix (algebraicRootElement r t) = F4Chevalley.rootCurve r t := by
  apply matrixAmbientEquiv.injective
  change matrixAmbientEquiv (matrixAmbientEquiv.symm _) = _
  rw [MulEquiv.apply_symm_apply]
  rw [algebraicRootElement, F4Chevalley.rootMorphism_inclusion_apply,
    F4Chevalley.ambientRootMorphism_apply]
  rfl

def matrixN (r : F4Chevalley.Root) (t : F) : (Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex F)ˣ :=
  F4Chevalley.rootCurve r t * F4Chevalley.rootCurve (-r) (-t⁻¹) * F4Chevalley.rootCurve r t

def matrixH (r : F4Chevalley.Root) (t : F) : (Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex F)ˣ :=
  matrixN r t * matrixN (F := F) r (-1)

private abbrev diag (i : typeF4RootPairing_base.support) (u : Fˣ) :=
  integralChevalleyTorusElement (P := typeF4RootPairing)
    (integralChevalleySimpleCorootParameter i u)

private theorem diag_tits (i : typeF4RootPairing_base.support) (u : Fˣ) :
    rootCurveTitsWord (S := F) [i] * diag i u =
      (diag i u)⁻¹ * rootCurveTitsWord (S := F)
        [i] := by
  apply Units.ext
  change specializeMatrix (titsWord [i]) * Matrix.diagonal _ =
    Matrix.diagonal _ * specializeMatrix (titsWord [i])
  simp only [titsWord, Matrix.mul_one]
  ext row col
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hz : titsLift i row col = 0
  · simp [specializeMatrix, hz]
  · have hw := titsLift_respectsChevalleyGrading i
      row col hz (i : F4Chevalley.Root)
    have hn : chevalleyBasisWeight (P := typeF4RootPairing) row (i : F4Chevalley.Root) =
        -chevalleyBasisWeight (P := typeF4RootPairing) col (i : F4Chevalley.Root) := by
      rw [hw]
      cases col with
      | inl j => simp [chevalleyBasisWeight]
      | inr j =>
        exact typeF4RootPairing.pairingIn_reflectionPerm_self_right ℤ j _
    have heval (a : F4Chevalley.BasisIndex) :
        chevalleyBasisTorusUnit (P := typeF4RootPairing)
          (integralChevalleySimpleCorootParameter i u) a =
        u ^ (-chevalleyBasisWeight (P := typeF4RootPairing) a (i : F4Chevalley.Root)) := by
      unfold chevalleyBasisTorusUnit integralChevalleySimpleCorootParameter
      rw [Finset.prod_eq_single i]
      · simp only [if_true]
      · intro j _ hj
        simp [hj]
      · simp
    have hu : chevalleyBasisTorusUnit (P := typeF4RootPairing)
        (integralChevalleySimpleCorootParameter i u) col =
        (chevalleyBasisTorusUnit (P := typeF4RootPairing)
        (integralChevalleySimpleCorootParameter i u) row)⁻¹ := by
      rw [heval, heval, hn]
      simp

    rw [hu]
    exact mul_comm _ _

private theorem diag_root (i : typeF4RootPairing_base.support) (u : Fˣ)
    (r : F4Chevalley.Root) (t : F) :
    (diag i u)⁻¹ * F4Chevalley.rootCurve r t * diag i u =
      F4Chevalley.rootCurve r
        (((u ^ typeF4RootPairing.pairingIn ℤ r (i : F4Chevalley.Root) :
          Fˣ) : F) * t) := by
  exact integralChevalleyRootCurve_simpleCoroot_conjugation
    i u r t

private theorem diag_mul (i : typeF4RootPairing_base.support) (u v : Fˣ) :
    diag i (u * v) = diag i u * diag i v := by
  rw [diag, ← integralChevalleyTorusElement_mul]
  congr 1
  funext j
  simp only [integralChevalleySimpleCorootParameter, Pi.mul_apply]
  split_ifs <;> simp

theorem matrixN_one (i : typeF4RootPairing_base.support) :
    (matrixN (F := F) (i : F4Chevalley.Root) 1) =
      rootCurveTitsWord (S := F) [i] := by
  rw [rootCurveTitsWord_cons, rootCurveTitsWord_nil, mul_one]
  change F4Chevalley.rootCurve _ 1 * F4Chevalley.rootCurve _ (-1⁻¹) *
    F4Chevalley.rootCurve _ 1 = _
  simp only [F4Chevalley.rootCurve, F4Chevalley.integralOperators,
    rootCurveUnit_simple, rootCurveUnit_neg_simple,
    inv_one]

theorem matrixN_neg_one (i : typeF4RootPairing_base.support) :
    matrixN (F := F) (i : F4Chevalley.Root) (-1) =
      (matrixN (F := F) (i : F4Chevalley.Root) 1)⁻¹ := by
  change F4Chevalley.rootCurve _ (-1) * F4Chevalley.rootCurve _ (-(-1)⁻¹) *
      F4Chevalley.rootCurve _ (-1) =
    (F4Chevalley.rootCurve _ 1 * F4Chevalley.rootCurve _ (-1⁻¹) *
      F4Chevalley.rootCurve _ 1)⁻¹
  simp [mul_inv_rev, F4Chevalley.rootCurve_inv, mul_assoc]

private theorem matrixN_square (i : typeF4RootPairing_base.support) (u : Fˣ) :
    (matrixN (F := F) (i : F4Chevalley.Root) (u ^ 2)) =
      (diag i u)⁻¹ * (matrixN (F := F) (i : F4Chevalley.Root) 1) * diag i u := by
  change F4Chevalley.rootCurve _ _ * F4Chevalley.rootCurve _ _ *
    F4Chevalley.rootCurve _ _ =
    (diag i u)⁻¹ * (F4Chevalley.rootCurve _ 1 * F4Chevalley.rootCurve _ (-1⁻¹) *
    F4Chevalley.rootCurve _ 1) * diag i u
  symm
  calc
    _ = ((diag i u)⁻¹ * F4Chevalley.rootCurve (i : F4Chevalley.Root) 1 * diag i u) *
        ((diag i u)⁻¹ * F4Chevalley.rootCurve (-(i : F4Chevalley.Root)) (-1⁻¹) * diag i u) *
        ((diag i u)⁻¹ * F4Chevalley.rootCurve (i : F4Chevalley.Root) 1 * diag i u) := by group
    _ = _ := by simp [diag_root]

private theorem torus_square (i : typeF4RootPairing_base.support) (u : Fˣ) :
    (matrixH (F := F) (i : F4Chevalley.Root) (u ^ 2)) = (diag i (u ^ 2))⁻¹ := by
  change (matrixN (F := F) _ (u ^ 2)) * (matrixN (F := F) _ (-1)) = _
  rw [matrixN_square, matrixN_neg_one]
  change (diag i u)⁻¹ * (matrixN (F := F) _ 1) * diag i u *
    ((matrixN (F := F) _ 1))⁻¹ = _
  rw [matrixN_one, mul_assoc (diag i u)⁻¹, diag_tits]
  rw [pow_two, diag_mul, mul_inv_rev]
  group

private theorem unit_square_surjective (t : Fˣ) :
    ∃ u : Fˣ, u ^ 2 = t := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (t : F) (by decide : 0 < 2)
  have hane : a ≠ 0 := by
    intro hz
    exact t.ne_zero (by simpa [hz] using ha.symm)
  refine ⟨Units.mk0 a hane, ?_⟩
  apply Units.ext
  exact ha

/-- The coroot word uses the inverse of the diagonal parameter convention. -/
theorem matrixH_simple (i : typeF4RootPairing_base.support)
    (t : Fˣ) :
    (matrixH (F := F) i t) = integralChevalleyTorusElement (P := typeF4RootPairing)
      (integralChevalleySimpleCorootParameter i t⁻¹) := by
  obtain ⟨u, rfl⟩ := unit_square_surjective t
  simp only [Units.val_pow_eq_pow_val]
  rw [torus_square]
  change (diag i (u ^ 2))⁻¹ = diag i ((u ^ 2)⁻¹)
  rw [diag, ← integralChevalleyTorusElement_inv]
  congr 1
  funext j
  simp only [integralChevalleySimpleCorootParameter, Pi.inv_apply]
  split_ifs <;> simp

private theorem basisUnit_simple (q : typeF4RootPairing_base.support)
    (u : Fˣ) (a : F4Chevalley.BasisIndex) :
    chevalleyBasisTorusUnit (P := typeF4RootPairing)
      (integralChevalleySimpleCorootParameter q u) a =
      u ^ (-chevalleyBasisWeight (P := typeF4RootPairing) a q) := by
  unfold chevalleyBasisTorusUnit integralChevalleySimpleCorootParameter
  rw [Finset.prod_eq_single q]
  · simp
  · intro j _ hj; simp [hj]
  · simp

private theorem weight_reflection (a : F4Chevalley.BasisIndex)
    (i q : F4Chevalley.Root) :
    chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4RootPairing.reflectionPerm i q) =
      chevalleyBasisWeight (P := typeF4RootPairing) a q -
        typeF4RootPairing.pairingIn ℤ i q * chevalleyBasisWeight (P := typeF4RootPairing) a i := by
  cases a with
  | inl j => simp [chevalleyBasisWeight]
  | inr r =>
    simp only [chevalleyBasisWeight, typeF4RootPairing.pairingIn_reflectionPerm]
    have hr : typeF4RootPairing.root (typeF4RootPairing.reflectionPerm i r) =
        (1 : ℤ) • typeF4RootPairing.root r +
          (-typeF4RootPairing.pairingIn ℤ r i) • typeF4RootPairing.root i := by
      rw [typeF4RootPairing.root_reflectionPerm, typeF4RootPairing.reflection_apply_root]
      simp [sub_eq_add_neg, ← typeF4RootPairing.algebraMap_pairingIn ℤ,
        Int.cast_smul_eq_zsmul]
    simpa [smul_eq_mul, sub_eq_add_neg, mul_comm] using
      (typeF4RootPairing.pairingIn_eq_add_of_root_eq_smul_add_smul (S := ℤ) (j := q) hr)

private theorem tits_simple_diag (i q : typeF4RootPairing_base.support)
    (u : Fˣ) :
    rootCurveTitsWord [i] * diag q u =
      (diag q u * diag i (u ^ (-typeF4RootPairing.pairingIn ℤ i q))) *
        rootCurveTitsWord [i] := by
  apply Units.ext
  change specializeMatrix (titsWord [i]) * Matrix.diagonal _ =
    (Matrix.diagonal _ * Matrix.diagonal _) * specializeMatrix (titsWord [i])
  simp only [titsWord, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
  ext row col
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hz : titsLift i row col = 0
  · simp [specializeMatrix, hz]
  · have hw := titsLift_respectsChevalleyGrading i row col hz
      (typeF4RootPairing.reflectionPerm i q)
    rw [typeF4RootPairing.reflectionPerm_self, weight_reflection] at hw
    have hu : chevalleyBasisTorusUnit (P := typeF4RootPairing)
        (integralChevalleySimpleCorootParameter q u) col =
        chevalleyBasisTorusUnit (P := typeF4RootPairing)
          (integralChevalleySimpleCorootParameter q u) row *
        chevalleyBasisTorusUnit (P := typeF4RootPairing)
          (integralChevalleySimpleCorootParameter i
            (u ^ (-typeF4RootPairing.pairingIn ℤ i q))) row := by
      rw [basisUnit_simple, basisUnit_simple, basisUnit_simple, ← zpow_mul, ← zpow_add]
      congr 1
      rw [← hw]
      ring
    rw [hu, Units.val_mul]
    exact mul_comm _ _


@[simp] theorem carrierMatrix_n (r : F4Chevalley.Root) (t : Fˣ) :
    carrierMatrix (algebraicNElement r t) = matrixN (F := F) r t := by
  simp only [algebraicNElement, map_mul, carrierMatrix_root, matrixN]

@[simp] private theorem carrierMatrix_coroot (i : typeF4RootPairing_base.support) (t : Fˣ) :
    carrierMatrix (algebraicCorootElement i t) = diag i t⁻¹ := by
  rw [algebraicCorootElement, map_mul, map_inv, carrierMatrix_n, carrierMatrix_n]
  simp only [Units.val_one]
  rw [← matrixN_neg_one]
  exact matrixH_simple i t

private theorem normalizer_transfer {G : Type*} [Group G] (n d e : G)
    (hd : n * d = (d * e) * n) (he : n * e = e⁻¹ * n) :
    d * n = n * (d * e) := by
  symm
  calc
    n * (d * e) = (d * e) * (n * e) := by rw [← mul_assoc, hd, mul_assoc]
    _ = d * n := by rw [he]; group

theorem coroot_n_commute (i j : Fin 4) (t : Fˣ) :
    algebraicCorootElement (typeF4SimpleRootIndex j) t *
        algebraicNElement (typeF4SimpleRootIndex i) 1 =
      algebraicNElement (typeF4SimpleRootIndex i) 1 *
        (algebraicCorootElement (typeF4SimpleRootIndex j) t *
          algebraicCorootElement (typeF4SimpleRootIndex i) (t ^ (-typeF4CartanMatrix i j))) := by
  apply carrierMatrix_injective
  change carrierMatrix (algebraicCorootElement (typeF4RootPairing_baseEquiv j) t *
        algebraicNElement (typeF4RootPairing_baseEquiv i) 1) =
    carrierMatrix (algebraicNElement (typeF4RootPairing_baseEquiv i) 1 *
      (algebraicCorootElement (typeF4RootPairing_baseEquiv j) t *
        algebraicCorootElement (typeF4RootPairing_baseEquiv i) (t ^ (-typeF4CartanMatrix i j))))
  simp only [map_mul, carrierMatrix_coroot, carrierMatrix_n, Units.val_one]
  rw [matrixN_one]
  have hpair : typeF4RootPairing.pairingIn ℤ (typeF4RootPairing_baseEquiv i)
      (typeF4RootPairing_baseEquiv j) = typeF4CartanMatrix i j :=
    typeF4RootPairing_base_cartan_apply i j
  have h := tits_simple_diag (typeF4RootPairing_baseEquiv i)
    (typeF4RootPairing_baseEquiv j) t⁻¹
  rw [hpair] at h
  have he := diag_tits (typeF4RootPairing_baseEquiv i)
    ((t⁻¹) ^ (-typeF4CartanMatrix i j))
  simpa only [inv_zpow] using normalizer_transfer _ _ _ h he

@[simp] theorem root_zero (r : F4Chevalley.Root) :
    algebraicRootElement (F := F) r 0 = 1 := by
  apply carrierMatrix_injective
  simp

@[simp] theorem root_inv (r : F4Chevalley.Root) (t : F) :
    (algebraicRootElement r t)⁻¹ = algebraicRootElement r (-t) := by
  apply carrierMatrix_injective
  simp only [map_inv, carrierMatrix_root, F4Chevalley.rootCurve_inv]

theorem coroot_n_inverse (i : Fin 4) (t : Fˣ) :
    algebraicCorootElement (typeF4SimpleRootIndex i) t *
        algebraicNElement (typeF4SimpleRootIndex i) 1 =
      algebraicNElement (typeF4SimpleRootIndex i) 1 *
        algebraicCorootElement (typeF4SimpleRootIndex i) t⁻¹ := by
  apply carrierMatrix_injective
  change carrierMatrix (algebraicCorootElement (typeF4RootPairing_baseEquiv i) t *
        algebraicNElement (typeF4RootPairing_baseEquiv i) 1) =
    carrierMatrix (algebraicNElement (typeF4RootPairing_baseEquiv i) 1 *
        algebraicCorootElement (typeF4RootPairing_baseEquiv i) t⁻¹)
  simp only [map_mul, carrierMatrix_coroot, carrierMatrix_n, Units.val_one, inv_inv,
    matrixN_one]
  rw [diag_tits]
  congr 1
  rw [diag, ← integralChevalleyTorusElement_inv]
  congr 1
  funext j
  simp only [integralChevalleySimpleCorootParameter, Pi.inv_apply]
  split_ifs <;> simp

theorem root_fixed_of_signed_simple_fixed (B : AlgebraicFactor F) (v : B.Space)
    (hpos : ∀ i : Fin 4, ∀ t : F,
      (B.action.action (algebraicRootElement (typeF4SimpleRootIndex i) t) : Module.End F B.Space) v = v)
    (hneg : ∀ i : Fin 4, ∀ t : F,
      (B.action.action (algebraicRootElement (-typeF4SimpleRootIndex i) t) : Module.End F B.Space) v = v)
    (r : F4Chevalley.Root) (t : F) :
    (B.action.action (algebraicRootElement r t) : Module.End F B.Space) v = v := by
  let K : Subgroup (Variety.Point (F4Chevalley.Carrier (k := F))) :=
    { carrier := {g | (B.action.action g : Module.End F B.Space) v = v}
      one_mem' := by simp
      mul_mem' := by
        intro g h hg hh
        change (B.action.action g : Module.End F B.Space) v = v at hg
        change (B.action.action h : Module.End F B.Space) v = v at hh
        change (B.action.action (g * h) : Module.End F B.Space) v = v
        simpa only [map_mul, Units.val_mul, Module.End.mul_apply, hh] using hg
      inv_mem' := by
        intro g hg
        have he := congrArg (fun w => (B.action.action g⁻¹ : Module.End F B.Space) w) hg
        simpa [← Module.End.mul_apply, ← Units.val_mul, ← map_mul] using he.symm }
  have hs : RootPairing.SimpleGeckGroup.subgroup typeF4RootPairing_base F ≤
      K.map carrierMatrix := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨⟨s, i⟩, a, rfl⟩
    have hp := hpos (typeF4RootPairing_baseEquiv.symm i) a
    have hn := hneg (typeF4RootPairing_baseEquiv.symm i) a
    rw [← typeF4RootPairing_baseEquiv_val, Equiv.apply_symm_apply] at hp hn
    cases s
    · refine ⟨algebraicRootElement (-i : F4Chevalley.Root) a, hn, ?_⟩
      simp only [carrierMatrix_root, F4Chevalley.rootCurve, F4Chevalley.integralOperators,
        rootCurveUnit_neg_simple]
      rfl
    · refine ⟨algebraicRootElement i a, hp, ?_⟩
      simp only [carrierMatrix_root, F4Chevalley.rootCurve, F4Chevalley.integralOperators,
        rootCurveUnit_simple]
      rfl
  have hm : carrierMatrix (algebraicRootElement r t) ∈ K.map carrierMatrix := by
    rw [carrierMatrix_root]
    exact hs (rootCurveUnit_mem_simpleSubgroup r t)
  obtain ⟨g, hg, he⟩ := hm
  have hge : g = algebraicRootElement r t := carrierMatrix_injective he
  exact hge ▸ hg

end ReeF4.BinaryDegree.ExceptionalTensor.ZeroAndMiddle
