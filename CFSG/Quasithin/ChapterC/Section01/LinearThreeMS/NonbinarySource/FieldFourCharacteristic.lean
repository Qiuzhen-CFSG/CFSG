module
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism.WordDescent
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism.ShortTransport
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.WeylOpposition.Matrix
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.MSPairs
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The field-four original F4 candidate satisfies MS3

Use the actual integral F4 root matrices over a finite characteristic-two
field, including F₄. The full positive subgroup is a two-group and has
trivial intersection with its opposite. Exceptional root substitution
preserves every matrix relation by the generic short-ideal transport theorem;
its square is coefficient Frobenius, so finiteness gives an automorphism.
This automorphism preserves the positive subgroup and reverses the four
simple nodes. A characteristic subgroup normal in the long-A₂ parabolic
is consequently normalized by every simple Weyl lift. Opposition puts it
in both positive and negative subgroups, proving that it is trivial.

The field-four application is exactly `MSNoCharacteristicNormal` for the
literal candidate K = A join [U,A] and radical candidate U. The join is
U join A, and the field has size 2². This supplies MS3 on the new carrier;
it does not identify its two-core, prove the full SL₃(4) quotient or SQTK,
or assert that it is a complete LinearThreeMSPair or a counterexample.
Those remaining hypotheses must be certified on these same subgroups.

The grading and opposition argument extends F4LongParabolic.Characteristic
and the Ree positive/negative separation proof to even field degree, using
ExceptionalMorphism.ShortTransport rather than a Ree coefficient field.
Sources: Aschbacher--Smith C.1.31--34, printed pp.135--137; MS93's F4
examples, p.831; Steinberg's exceptional F4 root substitution, GLS3
1.15.4(b), and positive/negative separation, GLS3 2.3.8(c).
-/

public noncomputable section
open Subgroup Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open ReeF4.WordRelations
open ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism
open scoped Classical Matrix
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.F4Original
variable {F : Type} [Field F] [Finite F] [CharP F 2]

abbrev Ambient (F : Type) [Field F] := matrixGroup F

@[expose] def root (r : F4Chevalley.Root) (t : F) : Ambient F :=
  ⟨F4Chevalley.rootCurve r t, subset_closure ⟨(r,t), rfl⟩⟩

@[expose] def positive (F : Type) [Field F] : Subgroup (Ambient F) :=
  closure {x | ∃ (r : F4Chevalley.Root) (t : F),
    typeF4RootPairing_base.IsPos r ∧ x = root r t}

@[expose] def negative (F : Type) [Field F] : Subgroup (Ambient F) :=
  closure {x | ∃ (r : F4Chevalley.Root) (t : F),
    ¬ typeF4RootPairing_base.IsPos r ∧ x = root r t}

private def wordEval : FreeGroup (F4Chevalley.Root × F) →* Ambient F :=
  (matrixWordEval (K := F)).codRestrict _ (fun w => matrixWordEval_range.le ⟨w,rfl⟩)

omit [Finite F] [CharP F 2] in
private theorem wordEval_surjective : Function.Surjective (wordEval (F := F)) := by
  intro x
  have hx : x.val ∈ (matrixWordEval (K := F)).range := (matrixWordEval_range (K := F)).symm ▸ x.property
  obtain ⟨w,hw⟩ := hx
  exact ⟨w, Subtype.ext hw⟩

omit [Finite F] [CharP F 2] in
private theorem wordEval_of (r : F4Chevalley.Root) (t : F) :
    wordEval (FreeGroup.of (r,t)) = root r t := by
  apply Subtype.ext
  exact matrixWordEval_of r t

private def twistedWordEval : FreeGroup (F4Chevalley.Root × F) →* Ambient F :=
  (matrixTwistedEval (K := F)).codRestrict _ matrixTwistedEval_mem

omit [Finite F] in
private theorem wordEval_ker_le :
    (wordEval (F := F)).ker ≤ (twistedWordEval (F := F)).ker := by
  intro w hw
  apply Subtype.ext
  exact matrixWordEval_ker_le hasShortAdjointTransport (congrArg Subtype.val hw)

/-- Exceptional root substitution on the actual matrix carrier. -/
def exceptional : Monoid.End (Ambient F) :=
  wordEval.liftOfSurjective wordEval_surjective ⟨twistedWordEval,wordEval_ker_le⟩

omit [Finite F] in
/-- The construction retains all parameters of the original field. -/
theorem exceptional_root (r : F4Chevalley.Root) (t : F) :
    exceptional (root r t) =
      root (ReeF4.exceptionalRootPermutation r) (ReeF4.exceptionalParameter r t) := by
  rw [← wordEval_of]
  change wordEval.liftOfSurjective wordEval_surjective
    ⟨twistedWordEval,wordEval_ker_le⟩ (wordEval (FreeGroup.of (r,t))) = _
  rw [MonoidHom.liftOfRightInverse_comp_apply]
  apply Subtype.ext
  exact matrixTwistedEval_of r t

private def coefficientFrobenius :
    (Matrix Coordinate Coordinate F)ˣ →* (Matrix Coordinate Coordinate F)ˣ :=
  Units.map (frobenius F 2).mapMatrix.toMonoidHom

omit [Finite F] in
private theorem coefficientFrobenius_root (r : F4Chevalley.Root) (t : F) :
    coefficientFrobenius (F4Chevalley.rootCurve r t) =
      F4Chevalley.rootCurve r (t ^ 2) := by
  apply Units.ext
  change (↑(F4Chevalley.rootCurve r t) : Matrix Coordinate Coordinate F).map (frobenius F 2) =
    (F4Chevalley.rootCurve r ((frobenius F 2) t)).val
  generalize (frobenius F 2) = f
  rw [F4Chevalley.rootCurve_matrix_formula, F4Chevalley.rootCurve_matrix_formula]
  ext i j
  simp [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    specializeMatrix, Matrix.one_apply, apply_ite f]

omit [Finite F] in
private theorem exceptional_twice_coe (g : Ambient F) :
    (exceptional (exceptional g)).val = coefficientFrobenius g.val := by
  have he : (Ambient F).subtype.comp (exceptional.comp exceptional) =
      coefficientFrobenius.comp (Ambient F).subtype := by
    apply MonoidHom.cancel_right wordEval_surjective |>.mp
    apply FreeGroup.ext_hom
    rintro ⟨r,t⟩
    simp only [MonoidHom.comp_apply,wordEval_of]
    change (exceptional (exceptional (root r t))).val = coefficientFrobenius (F4Chevalley.rootCurve r t)
    rw [exceptional_root,exceptional_root]
    rw [ReeF4.exceptionalRootPermutation_involutive,ReeF4.exceptionalParameter_twice]
    exact (coefficientFrobenius_root r t).symm
  exact DFunLike.congr_fun he g

omit [Finite F] in
private theorem exceptional_injective : Function.Injective (exceptional (F := F)) := by
  intro g h hh
  have he := congrArg (fun x => (exceptional x).val) hh
  rw [exceptional_twice_coe,exceptional_twice_coe] at he
  apply Subtype.ext
  apply Units.ext
  ext i j
  exact (frobenius F 2).injective (congrArg (fun x : (Matrix Coordinate Coordinate F)ˣ => x.val i j) he)

/-- The exceptional map is an automorphism also in even field degree. -/
def duality : MulAut (Ambient F) :=
  MulEquiv.ofBijective exceptional (Finite.injective_iff_bijective.mp exceptional_injective)

/-- The original positive subgroup is stable under exceptional duality. -/
theorem positive_duality : (positive F).map duality.toMonoidHom = positive F := by
  have hle : (positive F).map duality.toMonoidHom ≤ positive F := by
    rw [Subgroup.map_le_iff_le_comap]
    apply (closure_le _).mpr
    rintro _ ⟨r,t,hr,rfl⟩
    change exceptional (root r t) ∈ positive F
    rw [exceptional_root]
    have hp := ((typeF4RootPairing.isPositiveRootDuality_iff
      typeF4RootPairing_base ReeF4.exceptionalRootPermutation).mp
      ReeF4.exceptionalRootPermutation_spec).2.1 r
    exact subset_closure ⟨_,_,hp.mp hr,rfl⟩
  exact Subgroup.eq_of_le_of_card_ge hle (Nat.card_congr (duality.subgroupMap (positive F)).toEquiv).le

section GradedMatrices
variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

private def Raises (w : ι → ℤ) (A : Matrix ι ι K) : Prop :=
  ∀ i j, w i ≤ w j → A i j = 0

omit [Fintype ι] [DecidableEq ι] in
private theorem raises_add {w : ι → ℤ} {A B : Matrix ι ι K}
    (hA : Raises w A) (hB : Raises w B) : Raises w (A + B) := by
  intro i j hij
  simp only [Matrix.add_apply, hA i j hij, hB i j hij, add_zero]

omit [DecidableEq ι] in
private theorem raises_mul {w : ι → ℤ} {A B : Matrix ι ι K}
    (hA : Raises w A) (hB : Raises w B) : Raises w (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : w i ≤ w k
  · rw [hA i k hik, zero_mul]
  · rw [hB k j (by omega), mul_zero]

private theorem raises_pow_entry {w : ι → ℤ} {A : Matrix ι ι K}
    (hA : Raises w A) (n : ℕ) (i j : ι) (hij : w i < w j + n) :
    (A ^ n) i j = 0 := by
  induction n generalizing i j with
  | zero =>
    have hne : i ≠ j := by rintro rfl; omega
    simp [hne]
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : w i < w k + n
    · rw [ih i k hik, zero_mul]
    · rw [hA k j (by omega), mul_zero]

private theorem two_power_eq_one_of_raises [Nonempty ι] [CharP K 2]
    {w : ι → ℤ} {A : Matrix ι ι K} (hA : Raises w (A - 1)) :
    ∃ n : ℕ, A ^ (2 ^ n) = 1 := by
  obtain ⟨a, ha⟩ := Finite.bddAbove_range w
  obtain ⟨b, hb⟩ := Finite.bddBelow_range w
  let n := (a - b).toNat + 1
  have hn : (n : ℤ) < (2 ^ n : ℕ) := by exact_mod_cast (Nat.lt_two_pow_self (n := n))
  have hn' : a - b < (n : ℤ) := by dsimp [n]; omega
  have hzero : (A - 1) ^ (2 ^ n) = 0 := by
    ext i j
    apply raises_pow_entry hA
    have hi := ha (Set.mem_range_self i)
    have hj := hb (Set.mem_range_self j)
    omega
  refine ⟨n, ?_⟩
  let : CharP (Matrix ι ι K) 2 :=
    charP_of_injective_ringHom (algebraMap K (Matrix ι ι K)).injective 2
  have he := add_pow_char_pow_of_commute 2 n (Commute.one_right (A - 1))
  simpa only [sub_add_cancel, hzero, one_pow, zero_add] using he

private theorem raises_unit_mul {w : ι → ℤ} {A B : (Matrix ι ι K)ˣ}
    (hA : Raises w (A.val - 1)) (hB : Raises w (B.val - 1)) :
    Raises w ((A * B).val - 1) := by
  have he : (A * B).val - 1 = (A.val - 1) + (B.val - 1) +
      (A.val - 1) * (B.val - 1) := by simp only [Units.val_mul]; noncomm_ring
  rw [he]
  exact raises_add (raises_add hA hB) (raises_mul hA hB)

private theorem raises_unit_pow {w : ι → ℤ} {A : (Matrix ι ι K)ˣ}
    (hA : Raises w (A.val - 1)) (n : ℕ) : Raises w ((A ^ n).val - 1) := by
  induction n with
  | zero => intro i j _; simp
  | succ n ih => rw [pow_succ]; exact raises_unit_mul ih hA

end GradedMatrices

private noncomputable def rootDegree (r : F4Chevalley.Root) : ℤ :=
  11 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 0) +
  21 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 1) +
  15 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 2) +
  8 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 3)

private theorem rootDegree_simple (i : Fin 4) : rootDegree (typeF4SimpleRootIndex i) = 1 := by
  have hp (j : Fin 4) : typeF4RootPairing.pairingIn ℤ
      (typeF4SimpleRootIndex i) (typeF4SimpleRootIndex j) = typeF4CartanMatrix i j :=
    typeF4RootPairing_base_cartan_apply i j
  simp only [rootDegree, hp]
  fin_cases i <;> norm_num [typeF4CartanMatrix, Fin.ext_iff]

private theorem rootDegree_add {i j k : F4Chevalley.Root}
    (h : typeF4RootPairing.root k = typeF4RootPairing.root i + typeF4RootPairing.root j) :
    rootDegree k = rootDegree i + rootDegree j := by
  have hp (q : F4Chevalley.Root) : typeF4RootPairing.pairingIn ℤ k q =
      typeF4RootPairing.pairingIn ℤ i q + typeF4RootPairing.pairingIn ℤ j q := by
    simpa using typeF4RootPairing.pairingIn_eq_add_of_root_eq_smul_add_smul (S := ℤ)
      (j := q) (show typeF4RootPairing.root k =
        (1 : ℤ) • typeF4RootPairing.root i + (1 : ℤ) • typeF4RootPairing.root j by simpa using h)
  simp only [rootDegree, hp]
  ring

private theorem rootDegree_pos {r : F4Chevalley.Root}
    (hr : typeF4RootPairing_base.IsPos r) : 0 < rootDegree r := by
  apply hr.induction_on_add
  · intro i hi
    obtain ⟨j, hj⟩ := typeF4RootPairing_baseEquiv.surjective ⟨i, hi⟩
    have he : typeF4SimpleRootIndex j = i := congrArg Subtype.val hj
    rw [← he, rootDegree_simple]
    omega
  · intro i j k hk hi hj
    obtain ⟨l, hl⟩ := typeF4RootPairing_baseEquiv.surjective ⟨j, hj⟩
    have he : typeF4SimpleRootIndex l = j := congrArg Subtype.val hl
    rw [rootDegree_add hk, ← he, rootDegree_simple]
    omega

private noncomputable def basisDegree (a : F4Chevalley.BasisIndex) : ℤ :=
  11 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 0) +
  21 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 1) +
  15 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 2) +
  8 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 3)

private theorem dividedPower_degree (r : F4Chevalley.Root) (n : ℕ)
    (i j : F4Chevalley.BasisIndex)
    (hij : F4Chevalley.integralOperators.rootDividedPower r n i j ≠ 0) :
    basisDegree i - basisDegree j = (n : ℤ) * rootDegree r := by
  have h := rootDividedPower_isChevalleyHomogeneous (P := typeF4RootPairing)
    (b := typeF4RootPairing_base) r n i j hij
  have h0 := h (typeF4SimpleRootIndex 0)
  have h1 := h (typeF4SimpleRootIndex 1)
  have h2 := h (typeF4SimpleRootIndex 2)
  have h3 := h (typeF4SimpleRootIndex 3)
  dsimp only [basisDegree, rootDegree]
  linear_combination 11 * h0 + 21 * h1 + 15 * h2 + 8 * h3


noncomputable local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private theorem rootDegree_neg (r : F4Chevalley.Root) : rootDegree (-r) = -rootDegree r := by
  simp only [rootDegree, RootPairing.indexNeg_neg,
    RootPairing.pairingIn_reflectionPerm_self_left]
  ring

private theorem rootDegree_neg_of_not_pos {r : F4Chevalley.Root}
    (hr : ¬ typeF4RootPairing_base.IsPos r) : rootDegree r < 0 := by
  have h := rootDegree_pos ((RootPairing.Base.IsPos.neg_iff_not typeF4RootPairing_base r).mpr hr)
  rw [rootDegree_neg] at h
  omega

omit [Finite F] [CharP F 2] in
private theorem dividedPower_raises  (r : F4Chevalley.Root)
    (c : ℤ) (hc : 0 < c * rootDegree r) (n : ℕ) (hn : 0 < n) :
    Raises (fun i => c * basisDegree i) (specializeMatrix (S := F)
      (F4Chevalley.integralOperators.rootDividedPower r n)) := by
  intro i j hij
  by_contra hne
  have hint : F4Chevalley.integralOperators.rootDividedPower r n i j ≠ 0 := by
    intro he
    apply hne
    simp [specializeMatrix, he]
  have hd := congrArg (c * ·) (dividedPower_degree r n i j hint)
  have hp : 0 < (n : ℤ) * (c * rootDegree r) :=
    mul_pos (by exact_mod_cast hn) hc
  nlinarith

omit [Finite F] [CharP F 2] in
private theorem rootCurve_raises  (r : F4Chevalley.Root)
    (c : ℤ) (hc : 0 < c * rootDegree r) (t : F) :
    Raises (fun i => c * basisDegree i) ((F4Chevalley.rootCurve r t).val - 1) := by
  rw [F4Chevalley.rootCurve_matrix_formula]
  have hs (n : ℕ) (hn : 0 < n) (s : F) :
      Raises (fun i => c * basisDegree i) (s • specializeMatrix (S := F)
        (F4Chevalley.integralOperators.rootDividedPower r n)) := by
    intro i j hij
    simp only [Matrix.smul_apply, smul_eq_mul,
      dividedPower_raises r c hc n hn i j hij, mul_zero]
  have he : (1 + t • specializeMatrix (S := F)
        (F4Chevalley.integralOperators.rootDividedPower r 1) +
      t ^ 2 • specializeMatrix (S := F)
        (F4Chevalley.integralOperators.rootDividedPower r 2) +
      t ^ 3 • specializeMatrix (S := F)
        (F4Chevalley.integralOperators.rootDividedPower r 3)) - 1 =
      t • specializeMatrix (S := F)
        (F4Chevalley.integralOperators.rootDividedPower r 1) +
      t ^ 2 • specializeMatrix (S := F)
        (F4Chevalley.integralOperators.rootDividedPower r 2) +
      t ^ 3 • specializeMatrix (S := F)
        (F4Chevalley.integralOperators.rootDividedPower r 3) := by abel
  rw [he]
  exact raises_add (raises_add (hs 1 (by decide) t) (hs 2 (by decide) (t ^ 2)))
    (hs 3 (by decide) (t ^ 3))

omit [CharP F 2] in
private theorem closure_raises  (w : F4Chevalley.BasisIndex → ℤ)
    (S : Set (matrixGroup F)) (hS : ∀ x ∈ S, Raises w (x.val.val - 1))
    (x : Ambient F) (hx : x ∈ closure S) : Raises w (x.val.val - 1) := by
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => intro i j _; simp
  | mul x y _ _ hx hy => exact raises_unit_mul hx hy
  | inv x _ hx =>
    have he : x⁻¹ = x ^ (orderOf x - 1) := by
      apply mul_left_cancel (a := x)
      rw [mul_inv_cancel, ← pow_succ', Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
    rw [he]
    exact raises_unit_pow hx _


omit [CharP F 2] in
/-- Opposite positive root closures are disjoint over the actual coefficient field. -/
theorem positive_disjoint_negative : Disjoint (positive F) (negative F) := by
  apply Subgroup.disjoint_def.mpr
  intro x hx hy
  have hp : Raises basisDegree (x.val.val - 1) := by
    apply closure_raises _ _ ?_ x hx
    rintro y ⟨r, t, hr, rfl⟩
    simpa only [root, one_mul] using rootCurve_raises r 1 (by simpa using rootDegree_pos hr) t
  have hn : Raises (fun i => -basisDegree i) (x.val.val - 1) := by
    apply closure_raises _ _ ?_ x hy
    rintro y ⟨r, t, hr, rfl⟩
    simpa only [root, neg_one_mul] using
      rootCurve_raises r (-1) (by simpa using rootDegree_neg_of_not_pos hr) t
  apply Subtype.ext
  apply Units.ext
  apply sub_eq_zero.mp
  ext i j
  rcases le_total (basisDegree i) (basisDegree j) with hij | hji
  · exact hp i j hij
  · exact hn i j (neg_le_neg hji)

/-- The full positive root subgroup is a two-group, including over field four. -/
theorem positive_isPGroup : IsPGroup 2 (positive F) := by
  intro x
  have hp : Raises basisDegree (x.val.val.val - 1) := by
    apply closure_raises _ _ ?_ x.val x.property
    rintro y ⟨r,t,hr,rfl⟩
    simpa only [root,one_mul] using rootCurve_raises r 1 (by simpa using rootDegree_pos hr) t
  let : Nonempty F4Chevalley.BasisIndex := ⟨Sum.inr (typeF4SimpleRootIndex 0)⟩
  obtain ⟨n,hn⟩ := two_power_eq_one_of_raises hp
  exact ⟨n, Subtype.ext (Subtype.ext (Units.ext hn))⟩


open ReeF4.WordRelations.Faithfulness.Adjoint
open ReeF4.LocalBlockInput.PairNormalization.WeylOpposition

@[expose] def longLevi (F : Type) [Field F] : Subgroup (Ambient F) :=
  closure {x | ∃ (i : Fin 4) (t : F), i.val < 2 ∧
    (x = root (typeF4SimpleRootIndex i) t ∨ x = root (-typeF4SimpleRootIndex i) t)}

/-- The original candidate component includes its whole positive commutator. -/
@[expose] def componentCandidate (F : Type) [Field F] : Subgroup (Ambient F) :=
  longLevi F ⊔ ⁅positive F,longLevi F⁆

/-- The literal long-A₂ parabolic, with all field parameters in its positive roots. -/
@[expose] def parabolic (F : Type) [Field F] : Subgroup (Ambient F) :=
  positive F ⊔ longLevi F

omit [Finite F] [CharP F 2] in
theorem component_join_positive : componentCandidate F ⊔ positive F = parabolic F := by
  apply le_antisymm
  · exact sup_le (sup_le le_sup_right (Subgroup.commutator_le_sup _ _)) le_sup_left
  · exact sup_le le_sup_right (le_sup_left.trans le_sup_left)

private def simpleLift (i : Fin 4) : Ambient F :=
  root (typeF4SimpleRootIndex i) 1 * root (-typeF4SimpleRootIndex i) 1 *
    root (typeF4SimpleRootIndex i) 1

private def opposition : Ambient F :=
  (simpleLift 0 * simpleLift 1 * simpleLift 2 * simpleLift 3) ^ 6

omit [Finite F] in
private theorem simpleLift_coe (i : Fin 4) :
    (simpleLift (F := F) i).val = Faithfulness.Adjoint.titsUnit (K := F) (typeF4RootPairing_baseEquiv i) := by
  change F4Chevalley.rootCurve _ _ * F4Chevalley.rootCurve _ _ *
    F4Chevalley.rootCurve _ _ = _
  simp only [←typeF4RootPairing_baseEquiv_val i,rootCurve_simple,
    rootCurve_neg_simple,Faithfulness.Adjoint.titsUnit,CharTwo.neg_eq]

omit [Finite F] in
private theorem opposition_coe : (opposition (F := F)).val = omegaUnit := by
  change (simpleLift 0 * simpleLift 1 * simpleLift 2 * simpleLift 3).val ^ 6 = _
  simp only [Subgroup.coe_mul,simpleLift_coe]
  rw [show Faithfulness.Adjoint.titsUnit (typeF4RootPairing_baseEquiv 0) * Faithfulness.Adjoint.titsUnit (typeF4RootPairing_baseEquiv 1) *
    Faithfulness.Adjoint.titsUnit (typeF4RootPairing_baseEquiv 2) * Faithfulness.Adjoint.titsUnit (typeF4RootPairing_baseEquiv 3) =
    titsWordUnit (K := F) coxeterWord by
      simp only [coxeterWord,titsWordUnit,mul_one,mul_assoc]]
  exact coxeterWord_pow_six_eq_omega

omit [Finite F] in
private theorem opposition_conj_root (r : F4Chevalley.Root) (t : F) :
    opposition * root r t * opposition⁻¹ = root (-r) t := by
  apply Subtype.ext
  change opposition.val * F4Chevalley.rootCurve r t * opposition.val⁻¹ = _
  rw [opposition_coe]
  exact omega_conj_rootCurve r t

omit [Finite F] in
private theorem opposition_positive :
    (positive F).map (MulAut.conj opposition).toMonoidHom = negative F := by
  rw [positive,negative,MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y,⟨r,t,hr,rfl⟩,rfl⟩
    refine ⟨-r,t,?_,?_⟩
    · simpa only [RootPairing.Base.IsPos.neg_iff_not,not_not] using hr
    · exact opposition_conj_root r t
  · rintro ⟨r,t,hr,rfl⟩
    refine ⟨root (-r) t,⟨-r,t,?_,rfl⟩,?_⟩
    · exact (RootPairing.Base.IsPos.neg_iff_not typeF4RootPairing_base r).mpr hr
    · change opposition * root (-r) t * opposition⁻¹ = root r t
      simpa only [neg_neg] using opposition_conj_root (-r) t

private theorem characteristic_map_stable {B : Type*} [Group B]
    (S : Subgroup B) (C : Subgroup S) [C.Characteristic]
    (a : MulAut B) (ha : S.map a.toMonoidHom = S) :
    (C.map S.subtype).map a.toMonoidHom = C.map S.subtype := by
  let b : MulAut S := (a.subgroupMap S).trans (MulEquiv.subgroupCongr ha)
  have hb := characteristic_iff_map_eq.mp (inferInstance : C.Characteristic) b
  have hm := congrArg (map S.subtype) hb
  have he : S.subtype.comp b.toMonoidHom = a.toMonoidHom.comp S.subtype := by
    ext x
    exact (MulEquiv.subgroupCongr_apply ha _).trans (MulEquiv.coe_subgroupMap_apply a S x)
  simpa only [map_map,he] using hm

/-- Every characteristic subgroup of the full positive subgroup that is normal
in the original long-A₂ parabolic is trivial, also over a field of even degree. -/
theorem characteristic_normal_eq_bot (C : Subgroup (positive F)) [C.Characteristic]
    (hn : ((C.map (positive F).subtype).subgroupOf (parabolic F)).Normal) : C = ⊥ := by
  let S := positive F
  let X := C.map S.subtype
  have hXS : X ≤ S := map_subtype_le C
  have hXP : X ≤ parabolic F := hXS.trans le_sup_left
  have hPN : parabolic F ≤ normalizer (X : Set (Ambient F)) :=
    (normal_subgroupOf_iff_le_normalizer hXP).mp hn
  have hSN : S ≤ normalizer (X : Set (Ambient F)) := le_sup_left.trans hPN
  have hXmap : X.map duality.toMonoidHom = X :=
    characteristic_map_stable S C (duality (F := F)) (positive_duality (F := F))
  have hNstable {x : Ambient F} (hx : x ∈ normalizer (X : Set (Ambient F))) :
      duality x ∈ normalizer (X : Set (Ambient F)) := by
    have hh : (normalizer (X : Set (Ambient F))).map duality.toMonoidHom ≤
        normalizer (X.map duality.toMonoidHom : Set (Ambient F)) :=
      le_normalizer_map duality.toMonoidHom
    rw [hXmap] at hh
    exact hh ⟨x,hx,rfl⟩
  have hp (i : Fin 4) : root (typeF4SimpleRootIndex i) (1 : F) ∈
      normalizer (X : Set (Ambient F)) :=
    hSN (subset_closure ⟨_,1,typeF4RootPairing_base.isPos_of_mem_support
      (typeF4RootPairing_baseEquiv i).property,rfl⟩)
  have hnfirst (i : Fin 4) (hi : i.val < 2) :
      root (-typeF4SimpleRootIndex i) (1 : F) ∈ normalizer (X : Set (Ambient F)) :=
    hPN (mem_sup_right (subset_closure ⟨i,1,hi,Or.inr rfl⟩))
  have ht (i : Fin 4) :
      duality (root (-typeF4SimpleRootIndex i) (1 : F)) =
        root (-typeF4SimpleRootIndex (Fin.revPerm i)) 1 := by
    change exceptional _ = _
    rw [exceptional_root,ReeF4.exceptionalRootPermutation_neg_simple]
    congr 1
    by_cases hr : ReeF4.IsLongRoot (-typeF4SimpleRootIndex i)
    · exact ReeF4.exceptionalParameter_of_long hr 1
    · simpa only [one_pow] using ReeF4.exceptionalParameter_of_short hr (1 : F)
  have hnall (i : Fin 4) : root (-typeF4SimpleRootIndex i) (1 : F) ∈
      normalizer (X : Set (Ambient F)) := by
    fin_cases i
    · exact hnfirst 0 (by decide)
    · exact hnfirst 1 (by decide)
    · have he := hNstable (hnfirst 1 (by decide))
      rw [ht] at he
      exact he
    · have he := hNstable (hnfirst 0 (by decide))
      rw [ht] at he
      exact he
  have hl (i : Fin 4) : simpleLift (F := F) i ∈ normalizer (X : Set (Ambient F)) :=
    mul_mem (mul_mem (hp i) (hnall i)) (hp i)
  have hw : opposition (F := F) ∈ normalizer (X : Set (Ambient F)) :=
    pow_mem (mul_mem (mul_mem (mul_mem (hl 0) (hl 1)) (hl 2)) (hl 3)) 6
  have hXneg : X ≤ negative F := by
    rw [←opposition_positive]
    have he : X.map (MulAut.conj opposition).toMonoidHom = X :=
      mem_normalizer_iff_map_conj_eq.mp hw
    exact he ▸ map_mono hXS
  have hzero : X = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    exact (disjoint_def.mp positive_disjoint_negative) (hXS hx) (hXneg hx)
  exact (map_eq_bot_iff_of_injective C S.subtype_injective).mp hzero

/-- The actual C.1.31 MS3 convention on the component candidate and full
positive subgroup. No quotient, component or classification hypothesis is used. -/
theorem candidate_ms3 :
    Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.MSNoCharacteristicNormal
      (componentCandidate F) (positive F) := by
  intro C hc hn
  let := hc
  rw [component_join_positive] at hn
  exact characteristic_normal_eq_bot C hn

abbrev FourField := GaloisField 2 2

theorem fourField_card : Nat.card FourField = 4 := GaloisField.card 2 2 (by decide)

/-- The field-four candidate has the exact MS3 field, with n=2, and its
radical candidate is the literal positive two-group in the same matrix carrier. -/
theorem field_four_characteristic_input :
    Nat.card FourField = 2 ^ 2 ∧ IsPGroup 2 (positive FourField) ∧
    Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.MSNoCharacteristicNormal
      (componentCandidate FourField) (positive FourField) :=
  ⟨fourField_card,positive_isPGroup,candidate_ms3⟩

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.F4Original
