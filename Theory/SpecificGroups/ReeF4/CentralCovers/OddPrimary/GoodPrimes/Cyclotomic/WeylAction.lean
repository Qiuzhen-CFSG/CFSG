module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Cyclotomic.AlgebraicTwist
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent.BruhatParameters.RestrictedCells.NormalizerWords


/-!
# The two literal cyclotomic Weyl actions in algebraic F4

The root word `x_i(1) x_{-i}(-1) x_i(1)` conjugates the existing split
torus by the simple coroot reflection. We prove this in the faithful matrix
representation: each nonzero entry of the Tits lift respects the reflected
weight grading. Thus the calculation does not expand products of 52-by-52
matrices. The private weight calculation is adapted from
`RestrictedCells.NormalizerWords`, preserving that module's public boundary.

The exceptional morphism reverses the four simple coroots, squaring the
short-root parameters. Positive coroot words use inverse diagonal parameters;
the comparison below retains that convention. The exceptional matrix squares
to twice the identity. Composing its odd power with the two simple reflections
gives the minus action; the sixth power of the Coxeter word acts by inversion
and gives the plus action. Only the resulting 4-by-4 integer identities are
checked by finite computation.

The two exports supply exactly the geometric premises of
`Cyclotomic.embeddings_of_weyl_actions`. They hold also at `m = 0`; the
consumer's restriction `m ≥ 1` is needed for its separate Lang argument.

Sources: Steinberg, *Lectures on Chevalley Groups*, Lemma 19 and its weight
calculation (`refs/KGroup/GLS3/Chapter2St1.tex`, pp. 28–30); GLS3 §§2.1–2.4
and §4.10 (`refs/KGroup/GLS3/chapter2.tex` and `chapter4.tex`).
-/

public section

noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open F4Chevalley F4Chevalley.DenseParameters
open RootPairing.IntegralGeckConstruction ReeF4.WordRelations
open ReeF4.BinaryDegree.ExceptionalTensor
open ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg
open ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry
open ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent.BruhatParameters
open ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent.BruhatParameters.RestrictedCells
open scoped Matrix
namespace ReeF4.CentralCovers.OddPrimary.Cyclotomic
variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G : Type*} [CommGroup G]

private def latticeAction (A : Matrix (Fin 4) (Fin 4) ℤ) : (Fin 4 → G) →* (Fin 4 → G) where
  toFun u j := ∏ k, u k ^ A j k
  map_one' := by ext j; simp
  map_mul' u v := by ext j; simp [mul_zpow, Finset.prod_mul_distrib]

private theorem latticeAction_mul (A B : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → G) :
    latticeAction (A * B) u = latticeAction A (latticeAction B u) := by
  funext i
  change (∏ k, u k ^ (∑ j, A i j * B j k)) =
    ∏ j, (∏ k, u k ^ B j k) ^ A i j
  have hs (s : Finset (Fin 4)) (x : G) (f : Fin 4 → ℤ) :
      x ^ (∑ j ∈ s, f j) = ∏ j ∈ s, x ^ f j := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => simp [ha, zpow_add, ih]
  simp_rw [hs, ← Finset.prod_zpow, ← zpow_mul]
  rw [Finset.prod_comm]
  simp only [mul_comm]

private theorem latticeAction_one (u : Fin 4 → G) : latticeAction 1 u = u := by
  ext i
  simp [latticeAction, Matrix.one_apply]

private theorem latticeAction_neg (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → G) :
    latticeAction (-A) u = (latticeAction A u)⁻¹ := by
  ext i
  simp [latticeAction]

private def reflectionMatrix (i : Fin 4) : Matrix (Fin 4) (Fin 4) ℤ :=
  fun j k => (if j = k then 1 else 0) - if j = i then typeF4CartanMatrix i k else 0

private theorem latticeAction_single (A : Matrix (Fin 4) (Fin 4) ℤ) (q : Fin 4) (t : G) :
    latticeAction A (Pi.mulSingle q t) = fun j => t ^ A j q := by
  ext j
  simp [latticeAction, Pi.mulSingle_apply]

private theorem reflectionMatrix_single (i q : Fin 4) (t : G) :
    latticeAction (reflectionMatrix i) (Pi.mulSingle q t) =
      Pi.mulSingle q t * Pi.mulSingle i (t ^ (-typeF4CartanMatrix i q)) := by
  rw [latticeAction_single]
  funext j
  simp only [reflectionMatrix, Pi.mul_apply, Pi.mulSingle_apply]
  split_ifs <;> simp_all [zpow_sub]

private def exceptionalMatrix : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0,0,0,2; 0,0,2,0; 0,1,0,0; 1,0,0,0]

private theorem minus_matrix : reflectionMatrix 0 * reflectionMatrix 1 * exceptionalMatrix =
    !![0,2,-2,0; 0,2,-2,2; 0,1,0,0; 1,0,0,0] := by decide

private theorem coxeter_cube :
    (reflectionMatrix 0 * reflectionMatrix 1 * reflectionMatrix 2 * reflectionMatrix 3)^3 =
      !![1,0,0,-2; 2,1,-2,-2; 1,1,-1,-2; 1,0,0,-1] := by decide

private theorem opposition_matrix :
    (reflectionMatrix 0 * reflectionMatrix 1 * reflectionMatrix 2 * reflectionMatrix 3)^6 = -1 := by
  rw [show (6:ℕ) = 3*2 by decide, pow_mul, coxeter_cube]
  decide


private abbrev diag (i : typeF4RootPairing_base.support) (u : kˣ) :=
  integralChevalleyTorusElement (P := typeF4RootPairing)
    (integralChevalleySimpleCorootParameter i u)

omit [IsAlgClosed k] in
private theorem basisUnit_simple (q : typeF4RootPairing_base.support)
    (u : kˣ) (a : BasisIndex) :
    chevalleyBasisTorusUnit (P := typeF4RootPairing)
      (integralChevalleySimpleCorootParameter q u) a =
      u ^ (-chevalleyBasisWeight (P := typeF4RootPairing) a q) := by
  unfold chevalleyBasisTorusUnit integralChevalleySimpleCorootParameter
  rw [Finset.prod_eq_single q]
  · simp
  · intro j _ hj; simp [hj]
  · simp

omit [IsAlgClosed k] in
private theorem weight_reflection (a : BasisIndex)
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

omit [IsAlgClosed k] in
private theorem tits_simple_diag (i q : typeF4RootPairing_base.support)
    (u : kˣ) :
    titsUnit (S := k) [i] * diag q u =
      (diag q u * diag i (u ^ (-typeF4RootPairing.pairingIn ℤ i q))) *
        titsUnit (S := k) [i] := by
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

private theorem literalMatrix_diagonal (u : Fin 4 → kˣ) :
    literalMatrix (diagonal u) = torusElement u := by
  apply matrixAmbientEquiv.injective
  rw [literalMatrix_ambient]
  change (ambientClosedCarrier (k := k)).inclusion.onPoints
    (splitTorusMorphism.onPoints ((dPointEquiv 4).symm u)) = _
  rw [splitTorusMorphism_inclusion_apply, torusAmbientMorphism_apply]
  change matrixToAmbient (torusElement (dPointEquiv 4 ((dPointEquiv 4).symm u))) = _
  rw [Equiv.apply_symm_apply]
  rfl

omit [IsAlgClosed k] in
private theorem torusParameter_single (q : Fin 4) (t : kˣ) :
    torusParameter (Pi.mulSingle q t) =
      integralChevalleySimpleCorootParameter (typeF4RootPairing_baseEquiv q) t := by
  funext j
  simp only [torusParameter, Pi.mulSingle_apply, integralChevalleySimpleCorootParameter]
  simp only [Equiv.symm_apply_eq]

private theorem literalMatrix_diagonal_single (q : Fin 4) (t : kˣ) :
    literalMatrix (diagonal (Pi.mulSingle q t)) = diag (typeF4RootPairing_baseEquiv q) t := by
  rw [literalMatrix_diagonal]
  change integralChevalleyTorusElement _ = _
  rw [torusParameter_single]

private theorem simpleWeyl_eq (i : Fin 4) :
    simpleWeyl (F := k) i = algebraicNElement (typeF4SimpleRootIndex i) 1 := by
  simp only [simpleWeyl, algebraicNElement, Units.val_one, inv_one]
  rfl

private theorem simpleWeyl_diagonal_single (i q : Fin 4) (t : kˣ) :
    simpleWeyl i * diagonal (Pi.mulSingle q t) * (simpleWeyl i)⁻¹ =
      diagonal (latticeAction (reflectionMatrix i) (Pi.mulSingle q t)) := by
  apply literalMatrix_injective
  rw [reflectionMatrix_single, map_mul diagonal]
  simp only [map_mul, map_inv, simpleWeyl_eq, literalMatrix_simpleN,
    literalMatrix_diagonal_single]
  rw [tits_simple_diag, mul_assoc, mul_inv_cancel, mul_one]
  congr 3
  exact congrArg Neg.neg (typeF4RootPairing_base_cartan_apply i q)

/-- The rank-one root word acts on the literal split torus by its coroot reflection. -/
private theorem simpleWeyl_diagonal (i : Fin 4) (u : Fin 4 → kˣ) :
    simpleWeyl i * diagonal u * (simpleWeyl i)⁻¹ =
      diagonal (latticeAction (reflectionMatrix i) u) := by
  let L := (MulAut.conj (simpleWeyl (F := k) i)).toMonoidHom.comp diagonal
  let R := (diagonal (F := k)).comp (latticeAction (reflectionMatrix i))
  have hs (q : Fin 4) (t : kˣ) : L (Pi.mulSingle q t) = R (Pi.mulSingle q t) :=
    simpleWeyl_diagonal_single i q t
  have hu : u = (List.ofFn fun q => Pi.mulSingle q (u q)).prod := by
    rw [List.prod_ofFn]
    ext j
    simp [Finset.prod_apply]
  change L u = R u
  rw [hu, map_list_prod, map_list_prod]
  congr 1
  simp only [List.map_ofFn, Function.comp_def, hs]

/-- Comparison with the positive-coroot root word, retaining its inverse parameter. -/
private theorem diagonal_single_eq_coroot (q : Fin 4) (t : kˣ) :
    diagonal (Pi.mulSingle q t) = algebraicCorootElement (typeF4SimpleRootIndex q) t⁻¹ := by
  apply (ambientClosedCarrier (k := k)).inclusion_injective
  rw [← literalMatrix_ambient, literalMatrix_diagonal_single,
    algebraicCorootElement_ambient, matrixH_simple, inv_inv]
  rfl


variable [CharP k 2]

omit [IsAlgClosed k] [CharP k 2] in
private theorem exceptionalMatrix_single (q : Fin 4) (t : kˣ) :
    latticeAction exceptionalMatrix (Pi.mulSingle q t) =
      Pi.mulSingle (Fin.revPerm q) (exceptionalParameter (typeF4SimpleRootIndex q) t) := by
  rw [latticeAction_single]
  have he : exceptionalParameter (typeF4SimpleRootIndex q) t =
      if q.val < 2 then t else t^2 := by
    by_cases h : q.val < 2
    · rw [if_pos h, exceptionalParameter_of_long]
      exact (typeF4SimpleRootIndex_mem_pair_iff q).mpr h
    · rw [if_neg h, exceptionalParameter_of_short]
      exact fun hh => h ((typeF4SimpleRootIndex_mem_pair_iff q).mp hh)
  rw [he]
  ext j
  fin_cases q <;> fin_cases j <;> simp [exceptionalMatrix]

omit [IsAlgClosed k] [CharP k 2] in
private theorem exceptionalParameter_inv (q : Fin 4) (t : kˣ) :
    exceptionalParameter (typeF4SimpleRootIndex q) t⁻¹ =
      (exceptionalParameter (typeF4SimpleRootIndex q) t)⁻¹ := by
  by_cases h : IsLongRoot (typeF4SimpleRootIndex q)
  · simp only [exceptionalParameter_of_long h]
  · simp only [exceptionalParameter_of_short h, inv_pow]

private theorem exceptional_diagonal_single (q : Fin 4) (t : kˣ) :
    exceptionalPointEnd (diagonal (Pi.mulSingle q t)) =
      diagonal (latticeAction exceptionalMatrix (Pi.mulSingle q t)) := by
  rw [exceptionalMatrix_single, diagonal_single_eq_coroot, diagonal_single_eq_coroot]
  have h : HasExceptionalRootFormula (exceptionalPointEnd (F := k)) :=
    ExceptionalMorphism.morphism_rootFormula
  rw [exceptional_simple_coroot exceptionalPointEnd h, exceptionalParameter_inv]

/-- The exceptional morphism on the actual split torus, in its four coroot coordinates. -/
private theorem exceptional_diagonal (u : Fin 4 → kˣ) :
    exceptionalPointEnd (diagonal u) = diagonal (latticeAction exceptionalMatrix u) := by
  let L := exceptionalPointEnd.comp (diagonal (F := k))
  let R := (diagonal (F := k)).comp (latticeAction exceptionalMatrix)
  have hs (q : Fin 4) (t : kˣ) : L (Pi.mulSingle q t) = R (Pi.mulSingle q t) :=
    exceptional_diagonal_single q t
  have hu : u = (List.ofFn fun q => Pi.mulSingle q (u q)).prod := by
    rw [List.prod_ofFn]
    ext j
    simp [Finset.prod_apply]
  change L u = R u
  rw [hu, map_list_prod, map_list_prod]
  congr 1
  simp only [List.map_ofFn, Function.comp_def, hs]

private theorem exceptional_power_diagonal (n : ℕ) (u : Fin 4 → kˣ) :
    (exceptionalPointEnd ^ n) (diagonal u) =
      diagonal (latticeAction (exceptionalMatrix ^ n) u) := by
  induction n generalizing u with
  | zero => simp only [pow_zero, latticeAction_one]; rfl
  | succ n ih =>
    rw [pow_succ', pow_succ', latticeAction_mul]
    change exceptionalPointEnd ((exceptionalPointEnd ^ n) (diagonal u)) = _
    rw [ih, exceptional_diagonal]

private theorem exceptional_matrix_odd (m : ℕ) :
    exceptionalMatrix ^ (2*m+1) = ((2:ℤ)^m) • exceptionalMatrix := by
  have hsq : exceptionalMatrix ^ 2 = (2:ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by decide
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2*(m+1)+1 = (2*m+1)+2 by omega, pow_add, ih, hsq,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, pow_succ]

omit [IsAlgClosed k] [CharP k 2] in
private theorem twistedAction_matrix (a : ℤ) (u : Fin 4 → kˣ) :
    latticeAction (a • (reflectionMatrix 0 * reflectionMatrix 1 * exceptionalMatrix)) u =
      twistedAction a u := by
  rw [minus_matrix]
  ext i
  fin_cases i <;> simp [latticeAction, twistedAction, Fin.prod_univ_four, mul_comm a]

omit [CharP k 2] in
private theorem conjugation_mul {n p : AlgebraicPoints k}
    {A B : Matrix (Fin 4) (Fin 4) ℤ}
    (hn : ∀ u, n * diagonal u * n⁻¹ = diagonal (latticeAction A u))
    (hp : ∀ u, p * diagonal u * p⁻¹ = diagonal (latticeAction B u))
    (u : Fin 4 → kˣ) :
    (n*p) * diagonal u * (n*p)⁻¹ = diagonal (latticeAction (A*B) u) := by
  rw [latticeAction_mul, ← hn, ← hp]
  group

omit [CharP k 2] in
private theorem conjugation_pow {n : AlgebraicPoints k}
    {A : Matrix (Fin 4) (Fin 4) ℤ}
    (hn : ∀ u, n * diagonal u * n⁻¹ = diagonal (latticeAction A u))
    (s : ℕ) (u : Fin 4 → kˣ) :
    n^s * diagonal u * (n^s)⁻¹ = diagonal (latticeAction (A^s) u) := by
  induction s generalizing u with
  | zero => simp [latticeAction_one]
  | succ s ih =>
    simpa only [pow_succ] using conjugation_mul ih hn u

omit [CharP k 2] in
private theorem weylMinus_diagonal (u : Fin 4 → kˣ) :
    weylMinus * diagonal u * weylMinus⁻¹ =
      diagonal (latticeAction (reflectionMatrix 0 * reflectionMatrix 1) u) :=
  conjugation_mul (simpleWeyl_diagonal 0) (simpleWeyl_diagonal 1) u

/-- The first literal cyclotomic Weyl/twist action. -/
theorem weylMinus_algebraicReeTwist (m : ℕ) (u : Fin 4 → kˣ) :
    weylMinus * (algebraicReeTwist m).onPoints (diagonal u) * weylMinus⁻¹ =
      diagonal (twistedAction ((2:ℤ)^m) u) := by
  have ht : (algebraicReeTwist m).onPoints (diagonal u) =
      diagonal (latticeAction (exceptionalMatrix ^ (2*m+1)) u) :=
    (DFunLike.congr_fun (algebraicReeTwist_onPoints m) (diagonal u)).trans
      (exceptional_power_diagonal (2*m+1) u)
  rw [ht, weylMinus_diagonal,
    ← latticeAction_mul, exceptional_matrix_odd, Matrix.mul_smul, twistedAction_matrix]

omit [CharP k 2] in
private theorem opposition_diagonal (u : Fin 4 → kˣ) :
    (simpleWeyl 0 * simpleWeyl 1 * simpleWeyl 2 * simpleWeyl 3)^6 * diagonal u *
      ((simpleWeyl 0 * simpleWeyl 1 * simpleWeyl 2 * simpleWeyl 3)^6)⁻¹ =
      diagonal u⁻¹ := by
  have hc := conjugation_mul
    (conjugation_mul (conjugation_mul (simpleWeyl_diagonal (k := k) 0)
      (simpleWeyl_diagonal 1)) (simpleWeyl_diagonal 2)) (simpleWeyl_diagonal 3)
  rw [conjugation_pow hc, opposition_matrix, latticeAction_neg, latticeAction_one]

/-- The opposition word gives the second literal cyclotomic Weyl/twist action. -/
theorem weylPlus_algebraicReeTwist (m : ℕ) (u : Fin 4 → kˣ) :
    weylPlus * (algebraicReeTwist m).onPoints (diagonal u) * weylPlus⁻¹ =
      diagonal (twistedAction (-((2:ℤ)^m)) u) := by
  let c : AlgebraicPoints k := (simpleWeyl 0 * simpleWeyl 1 * simpleWeyl 2 * simpleWeyl 3)^6
  change (c * weylMinus) * _ * (c * weylMinus)⁻¹ = _
  rw [show (c * weylMinus) * (algebraicReeTwist m).onPoints (diagonal u) *
      (c * weylMinus)⁻¹ = c * (weylMinus * (algebraicReeTwist m).onPoints (diagonal u) *
        weylMinus⁻¹) * c⁻¹ by group, weylMinus_algebraicReeTwist]
  rw [show c * diagonal (twistedAction ((2:ℤ)^m) u) * c⁻¹ =
      diagonal (twistedAction ((2:ℤ)^m) u)⁻¹ from opposition_diagonal _]
  congr 1
  ext i
  fin_cases i <;> simp [twistedAction, mul_comm, mul_assoc]

end ReeF4.CentralCovers.OddPrimary.Cyclotomic
