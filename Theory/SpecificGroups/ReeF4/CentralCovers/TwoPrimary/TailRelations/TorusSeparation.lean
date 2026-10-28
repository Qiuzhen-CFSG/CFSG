module

public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.TailRelations.Geometry
public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.NormalizedBlocks.Torus
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FixedTorus
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.TorusCharacters
public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Tactic.LinearCombination

/-!
# Separating fixed coroot actors for the eight Ree blocks

For two distinct positive relative roots, an element of the literal fixed
coroot torus centralizes the entire first block and has a surjective
commutator map on the entire second block. Both parameters of the nonabelian
B₂ blocks are retained, and the result includes the field of order eight.

The long-root expansions give eight character pairs in the two simple torus
parameters. In the exponent ring of the cyclic field-unit group, put z = 2^m;
then 2*z² = 1. Every pairwise character determinant is a unit, as are the
central-character factor 1+2*z and the factors 2, 2*z and z+1. Taking the
perpendicular exponent pair makes the first character trivial and both
characters of the second nontrivial. The compatible inverse diagonal matrix
is an actual fixed coroot element. Uniqueness of block coordinates makes its
action fixed-point-free on the second block, and the inverse of Mathlib's
commutator map gives the required convention t*z*t⁻¹*z⁻¹.

This discharges exactly the torus premise of
`BlockSections.normalizesTails_of_base_and_torus`; the independent angular
commutator calculation remains with that theorem's assembly owner.

Source: GLS3, Table 2.4 (types V and VI) and Theorem 2.4.7(f),
`refs/KGroup/GLS3/chapter2.tex`. The central-cover application is GLS3 §6.1
and Aschbacher–Smith I.1.1–4, printed pp.407–408 of `refs/quasithin.pdf`.
-/

public section
noncomputable section
namespace ReeF4.CentralCovers.TwoPrimary.TailRelations
namespace TorusSeparation
open Subgroup
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open Parabolics
open LocalBlockInput.PairRigidity.BlockParameters
open LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open MatrixRelations
open NormalizedRootCentralizers.CenterExponent
open ElementaryTwoBound ElementaryTwoBound.RootCalculations
open Parabolics.RadicalCoordinates.FixedCoordinates

variable {m : ℕ}

/-- Main-character exponents in the two simple fixed-torus parameters. -/
private def weightA {R : Type*} [CommRing R] (z : R) : Fin 8 → R :=
  ![0, 1, 1, 1 + 2*z, 2*z, 1 + 2*z, 1, 1]
private def weightB {R : Type*} [CommRing R] (z : R) : Fin 8 → R :=
  ![1, 2 + 2*z, 1 + 2*z, 2 + 4*z, 1 + 2*z, 2 + 2*z, 1, 0]

private theorem basic_units {R : Type*} [CommRing R] (z : R) (hz : 2*z^2 = 1) :
    IsUnit (2:R) ∧ IsUnit (2*z) ∧ IsUnit (2*z+1) ∧ IsUnit (z+1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact isUnit_iff_exists_inv.mpr ⟨z^2, hz⟩
  · apply isUnit_iff_exists_inv.mpr
    refine ⟨z, ?_⟩
    linear_combination hz
  · apply isUnit_iff_exists_inv.mpr
    refine ⟨2*z-1, ?_⟩
    linear_combination 2*hz
  · apply isUnit_iff_exists_inv.mpr
    refine ⟨2-2*z, ?_⟩
    linear_combination -hz

/-- Every two distinct main characters form a basis modulo the field-unit order. -/
private theorem determinant_isUnit {R : Type*} [CommRing R] (z : R) (hz : 2*z^2 = 1)
    (i j : Fin 8) (hij : i ≠ j) :
    IsUnit (weightA z j * weightB z i - weightB z j * weightA z i) := by
  have forward (i j : Fin 8) (hij : i < j) :
      IsUnit (weightA z j * weightB z i - weightB z j * weightA z i) := by
    obtain ⟨h2,ht,hu,hv⟩ := basic_units z hz
    have h4 : z^2*4 = 2 := by linear_combination 2*hz
    have hone : IsUnit (1:R) := isUnit_one
    fin_cases i <;> fin_cases j <;> norm_num at hij
    all_goals simp only [weightA, weightB, Matrix.cons_val_zero', Matrix.cons_val_succ']
    all_goals ring_nf
    all_goals try rw [h4]
    all_goals first
      | solve | convert hone using 1 <;> ring
      | solve | convert ht using 1; ring
      | solve | convert hu using 1; ring
      | solve | convert h2.mul hv using 1; ring
      | solve | convert h2.mul hu using 1; ring
  rcases lt_or_gt_of_ne hij with h | h
  · exact forward i j h
  · have hh := (forward j i h).neg
    convert hh using 1; ring

private abbrev UnitExponents (m : ℕ) := ZMod (Nat.card (CoefficientField m)ˣ)

private theorem unit_order (m : ℕ) : Nat.card (CoefficientField m)ˣ = 2 * (2^m)^2 - 1 := by
  rw [Nat.card_units, field_card, pow_two, ← pow_add, show m+m=2*m by omega, pow_succ]
  omega

private theorem exponent_relation (m : ℕ) :
    2 * ((2^m : ℕ) : UnitExponents m)^2 = 1 := by
  have hp : 0 < 2*(2^m)^2 := by positivity
  have he : Nat.card (CoefficientField m)ˣ + 1 = 2*(2^m)^2 := by rw [unit_order]; omega
  have hc := congrArg (fun n : ℕ => (n : UnitExponents m)) he
  simpa only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self, zero_add,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using hc.symm

private theorem exponent_nontrivial (m : ℕ) (hm : 1 ≤ m) :
    1 < Nat.card (CoefficientField m)ˣ := by
  have hp : 2 ≤ 2^m := by simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hm
  rw [unit_order]
  have hq : 4 ≤ (2^m)^2 := by nlinarith
  omega

/-- A cyclic coordinate for the multiplicative group of the actual coefficient field. -/
private def unitCoordinate (m : ℕ) : Multiplicative (UnitExponents m) ≃* (CoefficientField m)ˣ :=
  zmodCyclicMulEquiv inferInstance

/-- The determinant construction separates any two distinct displayed weights,
including the central Suzuki weight of the second. -/
private theorem exponent_separation (m : ℕ) (hm : 1 ≤ m) (i j : Fin 8) (hij : i ≠ j) :
    ∃ b c : UnitExponents m,
      weightA ((2^m : ℕ) : UnitExponents m) i * b +
        weightB ((2^m : ℕ) : UnitExponents m) i * c = 0 ∧
      weightA ((2^m : ℕ) : UnitExponents m) j * b +
        weightB ((2^m : ℕ) : UnitExponents m) j * c ≠ 0 ∧
      (1+2*((2^m : ℕ) : UnitExponents m)) *
        (weightA ((2^m : ℕ) : UnitExponents m) j * b +
          weightB ((2^m : ℕ) : UnitExponents m) j * c) ≠ 0 := by
  let z : UnitExponents m := (2^m : ℕ)
  have : Fact (1 < Nat.card (CoefficientField m)ˣ) := ⟨exponent_nontrivial m hm⟩
  have : NeZero (Nat.card (CoefficientField m)ˣ) := ⟨by have := exponent_nontrivial m hm; omega⟩
  have hd := determinant_isUnit z (exponent_relation m) i j hij
  have hc : IsUnit (1+2*z) := by
    simpa only [add_comm] using (basic_units z (exponent_relation m)).2.2.1
  refine ⟨weightB z i, -weightA z i, ?_, ?_, ?_⟩
  · ring
  · convert hd.ne_zero using 1
    ring
  · convert (hc.mul hd).ne_zero using 1
    ring

private theorem realize (u : TorusParameters m) (hu : TwistCompatible u) :
    ∃ t : Model m, t ∈ fixedTorus m ∧
      matrixRepresentation m t = (torusMatrix u)⁻¹ := by
  let h : SplitGroup m := ⟨torusMatrix u, torusMatrix_mem_splitGroup u⟩
  have hf : reeTwist m h = h := by
    simpa only [LocalBlockInput.twist_eq_reeAutomorphism, reeAutomorphism_apply] using
      twist_torusMatrix (canonicalLocalBlockInput m) u hu h rfl
  let t : Model m := ⟨h⁻¹, (ReeF4.mem_fixedSubgroup m h⁻¹).mpr (by rw [map_inv, hf])⟩
  refine ⟨t, ?_, ?_⟩
  · change toSplitGroup m t ∈ splitTorus m
    rw [toSplitGroup_apply]
    change h⁻¹ ∈ splitTorus m
    apply (splitTorus m).inv_mem
    rw [splitTorus_eq_diagonalTorus]
    exact ⟨u, rfl⟩
  · rw [matrixRepresentation_apply]
    rfl

private theorem scale_add (u : TorusParameters m) (r s v : F4Chevalley.Root)
    (hv : v.val = r.val + s.val) :
    rootScale u v = rootScale u r * rootScale u s := by
  have hp (q : F4Chevalley.Root) : typeF4RootPairing.pairingIn ℤ v q =
      typeF4RootPairing.pairingIn ℤ r q + typeF4RootPairing.pairingIn ℤ s q :=
    typeF4RootPairing.pairingIn_eq_add_of_root_eq_add hv
  simp only [rootScale, integralChevalleyRootScale, hp, zpow_add,
    Finset.prod_mul_distrib]

private theorem scale_short (u : TorusParameters m) (hu : TwistCompatible u) (i : Fin 8) :
    (rootScale u (shortRoot i) : CoefficientField m) =
      theta m (rootScale u (longRoot i) : CoefficientField m) := by
  symm
  simpa only [exceptionalParameter_of_long (longRoot_isLong i), theta_apply, shortRoot]
    using hu (longRoot i)

private theorem scale_mixed (u : TorusParameters m) (i : Fin 8) (hi : i.val % 2 = 0) :
    rootScale u (mixedRoot i) = rootScale u (longRoot i) * rootScale u (shortRoot i) :=
  scale_add u _ _ _ (mixedRoot_eq_add i hi)

private theorem scale_high (u : TorusParameters m) (i : Fin 8) (hi : i.val % 2 = 0) :
    rootScale u (highRoot i) = rootScale u (longRoot i) * rootScale u (shortRoot i) ^ 2 := by
  have hv : (highRoot i).val = (mixedRoot i).val + (shortRoot i).val := by
    rw [highRoot_eq_add_two i hi, mixedRoot_eq_add i hi, two_smul, add_assoc]
  rw [scale_add u _ _ _ hv, scale_mixed u i hi, pow_two, mul_assoc]

private theorem theta_twice_sq (a : CoefficientField m) : theta m (theta m a) ^ 2 = a := by
  simp only [theta_apply, ← pow_mul, ← pow_add]
  rw [show 2 ^ (m + m) * 2 = 2 ^ (2 * m + 1) by rw [pow_succ]; congr 2; omega]
  exact field_pow m a

private theorem conj_main (u : TorusParameters m) (hu : TwistCompatible u)
    (t : Model m) (ht : matrixRepresentation m t = (torusMatrix u)⁻¹)
    (i : Fin 8) (a : CoefficientField m) :
    t * mainElement m i a * t⁻¹ =
      mainElement m i ((rootScale u (longRoot i) : CoefficientField m) * a) := by
  apply matrixRepresentation_injective m
  simp only [map_mul, map_inv, ht, matrixRepresentation_apply]
  change matrixTorusConj u (rootWord m i a).val =
    (rootWord m i ((rootScale u (longRoot i) : CoefficientField m) * a)).val
  have hf : rootFieldEnd m (longRoot i) = theta m := by
    ext v; exact rootFieldEnd_longRoot m i v
  simp only [rootWord, Subgroup.coe_mul, map_mul, matrixTorusConj_root,
    rootGeneratorInGroup_coe, hf, map_mul]
  rw [scale_short u hu i]
  split_ifs with hi
  · simp only [rootGeneratorInGroup_coe, matrixTorusConj_root, scale_mixed u i hi,
      Units.val_mul, scale_short u hu i]
    congr 2
    ring
  · simp only [Subgroup.coe_one, map_one]

private theorem conj_central (u : TorusParameters m) (hu : TwistCompatible u)
    (t : Model m) (ht : matrixRepresentation m t = (torusMatrix u)⁻¹)
    (i : Fin 8) (hi : i.val % 2 = 0) (a : CoefficientField m) :
    t * centralElement m i a * t⁻¹ =
      centralElement m i ((centralScale (rootScale u (longRoot i)) : CoefficientField m) * a) := by
  apply matrixRepresentation_injective m
  simp only [map_mul, map_inv, ht, matrixRepresentation_apply]
  change matrixTorusConj u (centralWord m i a).val =
    (centralWord m i ((centralScale (rootScale u (longRoot i)) : CoefficientField m) * a)).val
  have hf : rootFieldEnd m (longRoot i) = theta m := by
    ext v; exact rootFieldEnd_longRoot m i v
  simp only [centralWord, Subgroup.coe_mul, map_mul, matrixTorusConj_root,
    rootGeneratorInGroup_coe, hf, scale_high u i hi,
    scale_mixed u i hi, Units.val_mul, Units.val_pow_eq_pow_val, scale_short u hu i,
    centralScale, Units.coe_map, MonoidHom.coe_coe, map_pow, theta_twice_sq]
  congr 2
  ring

private theorem pair_injective (m : ℕ) (j : Fin 4) :
    Function.Injective (mainElement m (positiveRootWordLayout.pairIndex j)) := by
  classical
  let pack (a : CoefficientField m) : PositiveParameters m :=
    ⟨Function.update (fun _ => 0) j a, fun _ => 0, fun _ => 0⟩
  have hw (a : CoefficientField m) : wordElement m (pack a) =
      mainElement m (positiveRootWordLayout.pairIndex j) a := by
    fin_cases j <;> simp [wordElement, pack, pairCount, quartetCount, List.ofFn_succ]
  intro a b h
  have hp := wordElement_injective m ((hw a).trans (h.trans (hw b).symm))
  simpa [pack] using congrArg (fun p => p.pair j) hp

private theorem block_injective (m : ℕ) (j : Fin 4) (a b c d : CoefficientField m)
    (h : blockPoint m (positiveRootWordLayout.quartetIndex j) a b =
      blockPoint m (positiveRootWordLayout.quartetIndex j) c d) : a = c ∧ b = d := by
  classical
  let pack (a b : CoefficientField m) : PositiveParameters m :=
    ⟨fun _ => 0, Function.update (fun _ => 0) j a, Function.update (fun _ => 0) j b⟩
  have hw (a b : CoefficientField m) : wordElement m (pack a b) =
      blockPoint m (positiveRootWordLayout.quartetIndex j) a b := by
    fin_cases j <;> simp [wordElement, pack, blockPoint, pairCount, quartetCount, List.ofFn_succ]
  have hp := wordElement_injective m ((hw a b).trans (h.trans (hw c d).symm))
  constructor
  · simpa [pack] using congrArg (fun p => p.main j) hp
  · simpa [pack] using congrArg (fun p => p.central j) hp

private theorem scalar_fixed {c : (CoefficientField m)ˣ} (hc : c ≠ 1)
    {a : CoefficientField m} (ha : (c : CoefficientField m) * a = a) : a = 0 := by
  have hh : ((c : CoefficientField m) - 1) * a = 0 := by rw [sub_mul, one_mul, ha, sub_self]
  exact (mul_eq_zero.mp hh).resolve_left (fun h => hc (Units.ext (sub_eq_zero.mp h)))

/-- A trivial main character centralizes the full generated root block. -/
private theorem centralizes (u : TorusParameters m) (hu : TwistCompatible u)
    (t : Model m) (ht : matrixRepresentation m t = (torusMatrix u)⁻¹)
    (i : Fin 8) (hi : rootScale u (longRoot i) = 1) :
    ∀ x : X m i, Commute t x.val := by
  rintro ⟨x,hx⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a,rfl⟩ := hx
    apply mul_inv_eq_iff_eq_mul.mp
    simpa only [hi, Units.val_one, one_mul] using conj_main u hu t ht i a
  | one => exact Commute.one_right t
  | mul x y _ _ hx hy => exact hx.mul_right hy
  | inv x _ hx => exact hx.inv_right

private theorem conj_blockPoint (u : TorusParameters m) (hu : TwistCompatible u)
    (t : Model m) (ht : matrixRepresentation m t = (torusMatrix u)⁻¹)
    (i : Fin 8) (hi : i.val % 2 = 0) (a b : CoefficientField m) :
    t * blockPoint m i a b * t⁻¹ = blockPoint m i
      ((rootScale u (longRoot i) : CoefficientField m) * a)
      ((centralScale (rootScale u (longRoot i)) : CoefficientField m) * b) := by
  change (MulAut.conj t) (mainElement m i a * centralElement m i b) = _
  rw [map_mul]
  exact congrArg₂ (· * ·) (conj_main u hu t ht i a) (conj_central u hu t ht i hi b)

/-- Nontriviality of the main and central characters excludes every nonidentity
fixed point, including the second coordinate in a B₂ block. -/
private theorem fixed_point_free (u : TorusParameters m) (hu : TwistCompatible u)
    (t : Model m) (ht : matrixRepresentation m t = (torusMatrix u)⁻¹)
    (i : BlockIndex) (hi : rootScale u (longRoot (rootIndex i)) ≠ 1)
    (hc : centralScale (rootScale u (longRoot (rootIndex i))) ≠ 1)
    (x : X m (rootIndex i)) (hx : t * x.val * t⁻¹ = x.val) : x = 1 := by
  apply Subtype.ext
  cases i with
  | inl j =>
    obtain ⟨a,ha⟩ := (mem_X_iff m _ (positiveRootWordLayout.pair_odd j) x.val).mp x.property
    rw [← ha, conj_main u hu t ht] at hx
    have hz := scalar_fixed hi (pair_injective m j hx)
    rw [← ha, hz, mainElement_zero]
    rfl
  | inr j =>
    obtain ⟨a,b,hab⟩ := (mem_X_even m _ (positiveRootWordLayout.quartet_even j) x.val).mp x.property
    rw [← hab, conj_blockPoint u hu t ht _ (positiveRootWordLayout.quartet_even j)] at hx
    obtain ⟨h₁,h₂⟩ := block_injective m j _ _ _ _ hx
    rw [← hab, scalar_fixed hi h₁, scalar_fixed hc h₂]
    simp only [blockPoint, mainElement_zero, centralElement_zero, mul_one, Subgroup.coe_one]

/-- The inverse of Mathlib's commutator map has the convention used by the
central-cover consumer: every element is `t*z*t⁻¹*z⁻¹`. -/
private theorem commutator_surjective (u : TorusParameters m) (hu : TwistCompatible u)
    (t : Model m) (htT : t ∈ fixedTorus m)
    (ht : matrixRepresentation m t = (torusMatrix u)⁻¹)
    (i : BlockIndex) (hi : rootScale u (longRoot (rootIndex i)) ≠ 1)
    (hc : centralScale (rootScale u (longRoot (rootIndex i))) ≠ 1) :
    ∀ y : X m (rootIndex i), ∃ z : X m (rootIndex i),
      t * z.val * t⁻¹ * z.val⁻¹ = y.val := by
  let H := X m (rootIndex i)
  have hn := fixedTorus_normalizes_X m (rootIndex i) htT
  let f : H →* H := ((MulAut.conj t).toMonoidHom.comp H.subtype).codRestrict H
    (fun x => (mem_normalizer_iff.mp hn x.val).mp x.property)
  have hf : MonoidHom.FixedPointFree f := by
    intro x hx
    exact fixed_point_free u hu t ht i hi hc x (congrArg Subtype.val hx)
  intro y
  obtain ⟨z,hz⟩ := hf.commutatorMap_surjective y⁻¹
  refine ⟨z, ?_⟩
  have he := congrArg (fun a : H => a.val⁻¹) hz
  change (z.val * (t * z.val * t⁻¹)⁻¹)⁻¹ = (y.val⁻¹)⁻¹ at he
  simpa only [mul_inv_rev, inv_inv] using he

private theorem long_pairing (i : Fin 8) (q : F4Chevalley.Root) :
    typeF4RootPairing.pairingIn ℤ (longRoot i) q =
      ∑ j : Fin 4, (longRootCoefficients i j : ℤ) *
        typeF4RootPairing.pairingIn ℤ (typeF4SimpleRootIndex j) q := by
  apply FaithfulSMul.algebraMap_injective ℤ ℝ
  simp only [map_sum, map_mul, typeF4RootPairing.algebraMap_pairingIn,
    ← typeF4RootPairing.root_coroot'_eq_pairing]
  change typeF4RootPairing.coroot' q (longRoot i).val = _
  rw [longRoot_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_nsmul]
  simp only [nsmul_eq_mul, map_natCast,
    typeF4RootPairing_root, typeF4SimpleRootIndex_val]

/-- The eight long-root characters follow from the actual root lattice expansions. -/
private theorem long_scale (u : TorusParameters m) (i : Fin 8) :
    rootScale u (longRoot i) =
      ∏ j : Fin 4, rootScale u (typeF4SimpleRootIndex j) ^ longRootCoefficients i j := by
  simp only [rootScale, integralChevalleyRootScale, long_pairing, Fin.sum_univ_four,
    zpow_add, Finset.prod_mul_distrib, Fin.prod_univ_four,
    mul_comm (longRootCoefficients i _ : ℤ), zpow_mul, zpow_natCast, Finset.prod_pow]

private theorem theta_units (b : (CoefficientField m)ˣ) :
    Units.map (theta m) b = b ^ (2^m) := by
  apply Units.ext
  rfl

/-- The two simple parameters give the displayed main-character weight pairs. -/
private theorem blockTorus_long_scale (b c : (CoefficientField m)ˣ) (i : Fin 8) :
    rootScale (blockTorus b c) (longRoot i) =
      b ^ (weightA (2^m : ℤ) i) * c ^ (weightB (2^m : ℤ) i) := by
  rw [long_scale]
  simp only [blockTorus, rootScale_torusParametersOfSimpleScales, Fin.prod_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    theta_units]
  fin_cases i <;> norm_num [longRootCoefficients, weightA, weightB, Fin.ext_iff,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals
    simp only [← zpow_natCast]
    push_cast
    simp only [zpow_add, zpow_mul, zpow_one]
    simp only [← zpow_mul, mul_comm, mul_left_comm, mul_assoc]

private def expUnit (x : UnitExponents m) : (CoefficientField m)ˣ :=
  unitCoordinate m (Multiplicative.ofAdd x)

private theorem expUnit_zero : expUnit (0 : UnitExponents m) = 1 :=
  map_one (unitCoordinate m)

private theorem expUnit_eq_one (x : UnitExponents m) : expUnit x = 1 ↔ x = 0 := by
  exact (unitCoordinate m).map_eq_one_iff

private theorem expUnit_add (x y : UnitExponents m) :
    expUnit (x+y) = expUnit x * expUnit y := map_mul (unitCoordinate m) _ _

private theorem expUnit_zpow (n : ℤ) (x : UnitExponents m) :
    expUnit ((n : UnitExponents m)*x) = expUnit x ^ n := by
  change unitCoordinate m (Multiplicative.ofAdd ((n : UnitExponents m)*x)) = _
  rw [← zsmul_eq_mul, ofAdd_zsmul, map_zpow]
  rfl

private theorem expUnit_pow (n : ℕ) (x : UnitExponents m) :
    expUnit ((n : UnitExponents m)*x) = expUnit x ^ n := by
  simpa using expUnit_zpow (n : ℤ) x

private theorem cast_weightA (z : ℤ) (i : Fin 8) :
    ((weightA z i : ℤ) : UnitExponents m) = weightA (z : UnitExponents m) i := by
  fin_cases i <;> simp [weightA]

private theorem cast_weightB (z : ℤ) (i : Fin 8) :
    ((weightB z i : ℤ) : UnitExponents m) = weightB (z : UnitExponents m) i := by
  fin_cases i <;> simp [weightB]

private theorem expUnit_character (b c : UnitExponents m) (i : Fin 8) :
    rootScale (blockTorus (expUnit b) (expUnit c)) (longRoot i) =
      expUnit (weightA ((2^m : ℕ) : UnitExponents m) i * b +
        weightB ((2^m : ℕ) : UnitExponents m) i * c) := by
  rw [blockTorus_long_scale, ← expUnit_zpow, ← expUnit_zpow, ← expUnit_add,
    cast_weightA, cast_weightB]
  norm_cast

private theorem expUnit_central (x : UnitExponents m) :
    centralScale (expUnit x) = expUnit ((1+2*((2^m : ℕ) : UnitExponents m))*x) := by
  rw [centralScale, theta_units, ← expUnit_pow, ← expUnit_pow, ← expUnit_add]
  congr 1
  ring

/-- Actual torus characters separate the first block from both coordinates of the second. -/
private theorem separating_parameters (m : ℕ) (hm : 1 ≤ m) (i j : Fin 8) (hij : i ≠ j) :
    ∃ b c : (CoefficientField m)ˣ,
      rootScale (blockTorus b c) (longRoot i) = 1 ∧
      rootScale (blockTorus b c) (longRoot j) ≠ 1 ∧
      centralScale (rootScale (blockTorus b c) (longRoot j)) ≠ 1 := by
  obtain ⟨b,c,hi,hj,hc⟩ := exponent_separation m hm i j hij
  refine ⟨expUnit b, expUnit c, ?_, ?_, ?_⟩
  · rw [expUnit_character, hi, expUnit_zero]
  · rw [expUnit_character, ne_eq, expUnit_eq_one]
    exact hj
  · rw [expUnit_character, expUnit_central, ne_eq, expUnit_eq_one]
    exact hc

end TorusSeparation
open TorusSeparation
open LocalBlockInput.PairRigidity.BlockParameters
open LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery

/-- Fixed coroot actors separate every two distinct actual Ree blocks, for all
q = 2^(2m+1) with m ≥ 1. This supplies the torus premise of
`BlockSections.normalizesTails_of_base_and_torus`. -/
theorem torusBlockSeparation (m : ℕ) (hm : 1 ≤ m) : TorusBlockSeparation m := by
  intro i j hij
  obtain ⟨b,c,hi,hj,hc⟩ := separating_parameters m hm (rootIndex i) (rootIndex j)
    (fun h => hij (rootIndexEquiv.injective h))
  let u := blockTorus b c
  have hu : TwistCompatible u := blockTorus_twistCompatible b c
  obtain ⟨t,htT,ht⟩ := realize u hu
  exact ⟨t, htT, fun k => fixedTorus_normalizes_X m (rootIndex k) htT,
    centralizes u hu t ht (rootIndex i) hi, commutator_surjective u hu t htT ht j hj hc⟩

end ReeF4.CentralCovers.TwoPrimary.TailRelations
