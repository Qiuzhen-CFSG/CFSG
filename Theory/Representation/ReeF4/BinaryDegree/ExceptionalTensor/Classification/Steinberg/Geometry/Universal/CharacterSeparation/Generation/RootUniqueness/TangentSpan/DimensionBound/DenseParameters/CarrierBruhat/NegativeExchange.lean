module
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness.TangentSpan.DimensionBound.DenseParameters.CarrierBruhat.Generation
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.RankOneTransport.SimpleConjugation

/-!
# Negative-simple exchange in the literal algebraic F4 carrier

Positive-root partition isolates the reflecting simple-root factor. The
parameter-one simple representative preserves the remaining positive factors.
If the isolated root transports to a positive root, move it through the middle
normalizer word. In the other sign branch, a nonzero parameter gives an actual
opposite-root rank-one word, which stays in the middle and retains its torus
contribution. Two simple-representative exchanges give negative-simple exchange.

The sign step uses the faithful carrier matrices. Positive root matrices raise
an integral height grading, and negative root matrices lower it. Products of
lowering unipotent matrices have two-power order in characteristic two, over
any coefficient field. The nontrivial order-three simple-root pair therefore
cannot transport into two negative root groups. No negation preservation of
`RootTransport.perm`, finite-field hypothesis, or global coverage is used.

The collection strategy follows GLS3 §§1.11–1.12, especially the rank-one word
and reflection relations in 1.12.1, in `refs/KGroup/GLS3/Chapter1.tex`. The
matrix grading argument adapts the integral calculation in
`Theory/SpecificGroups/ReeF4/LargeLocalSeeds/FixedGeometry/PositiveTwoGroup.lean`;
the cell argument adapts `FixedBruhatCover/SplitCoverage/NegativeSimple.lean`.
Those finite-group modules are templates only and are not imported here.
-/

public section
noncomputable section
namespace Theory.AlgebraicGroup.F4Chevalley.DenseParameters.CarrierBruhat
open StandardRootSystem Subgroup
open RootPairing.IntegralGeckConstruction ReeF4.WordRelations
open scoped Matrix
universe u
variable {k : Type u} [Field k]
local instance : InvolutiveNeg Root := typeF4RootPairing.indexNeg

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


noncomputable local instance : Nonempty F4Chevalley.BasisIndex :=
  ⟨Sum.inl (typeF4RootPairing_baseEquiv 0)⟩

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

private theorem dividedPower_raises (r : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) (n : ℕ) (hn : 0 < n) :
    Raises basisDegree (specializeMatrix (S := k)
      (F4Chevalley.integralOperators.rootDividedPower r n)) := by
  intro i j hij
  by_contra hne
  have hint : F4Chevalley.integralOperators.rootDividedPower r n i j ≠ 0 := by
    intro he
    apply hne
    simp [specializeMatrix, he]
  have hd := dividedPower_degree r n i j hint
  have hp : 0 < (n : ℤ) * rootDegree r :=
    mul_pos (by exact_mod_cast hn) (rootDegree_pos hr)
  omega

private theorem rootCurve_raises (r : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) (t : k) :
    Raises basisDegree ((F4Chevalley.rootCurve r t).val - 1) := by
  rw [F4Chevalley.rootCurve_matrix_formula]
  have hs (n : ℕ) (hn : 0 < n) (s : k) :
      Raises basisDegree (s • specializeMatrix (S := k)
        (F4Chevalley.integralOperators.rootDividedPower r n)) := by
    intro i j hij
    simp only [Matrix.smul_apply, smul_eq_mul, dividedPower_raises r hr n hn i j hij,
      mul_zero]
  have he : (1 + t • specializeMatrix (S := k) (F4Chevalley.integralOperators.rootDividedPower r 1) +
      t ^ 2 • specializeMatrix (S := k) (F4Chevalley.integralOperators.rootDividedPower r 2) +
      t ^ 3 • specializeMatrix (S := k) (F4Chevalley.integralOperators.rootDividedPower r 3)) - 1 =
      t • specializeMatrix (S := k) (F4Chevalley.integralOperators.rootDividedPower r 1) +
      t ^ 2 • specializeMatrix (S := k) (F4Chevalley.integralOperators.rootDividedPower r 2) +
      t ^ 3 • specializeMatrix (S := k) (F4Chevalley.integralOperators.rootDividedPower r 3) := by abel
  rw [he]
  exact raises_add (raises_add (hs 1 (by decide) t) (hs 2 (by decide) (t ^ 2)))
    (hs 3 (by decide) (t ^ 3))

private theorem rootDegree_neg (r : Root) : rootDegree (-r) = -rootDegree r := by
  simp only [rootDegree, RootPairing.indexNeg_neg,
    RootPairing.pairingIn_reflectionPerm_self_left]
  ring

private theorem rootDegree_neg_of_not_pos {r : Root}
    (hr : ¬ typeF4RootPairing_base.IsPos r) : rootDegree r < 0 := by
  have h := rootDegree_pos ((RootPairing.Base.IsPos.neg_iff_not typeF4RootPairing_base r).mpr hr)
  rw [rootDegree_neg] at h
  omega

private theorem dividedPower_lowers (r : Root)
    (hr : ¬ typeF4RootPairing_base.IsPos r) (n : ℕ) (hn : 0 < n) :
    Raises (fun a => -basisDegree a) (specializeMatrix (S := k)
      (integralOperators.rootDividedPower r n)) := by
  intro i j hij
  by_contra hne
  have hint : integralOperators.rootDividedPower r n i j ≠ 0 := by
    intro he
    apply hne
    simp [specializeMatrix, he]
  have hd := dividedPower_degree r n i j hint
  have hp : (n : ℤ) * rootDegree r < 0 :=
    mul_neg_of_pos_of_neg (by exact_mod_cast hn) (rootDegree_neg_of_not_pos hr)
  dsimp only at hij
  omega

private theorem rootCurve_lowers (r : Root)
    (hr : ¬ typeF4RootPairing_base.IsPos r) (t : k) :
    Raises (fun a => -basisDegree a) ((rootCurve r t).val - 1) := by
  rw [rootCurve_matrix_formula]
  have hs (n : ℕ) (hn : 0 < n) (s : k) :
      Raises (fun a => -basisDegree a) (s • specializeMatrix (S := k)
        (integralOperators.rootDividedPower r n)) := by
    intro i j hij
    simp only [Matrix.smul_apply, smul_eq_mul, dividedPower_lowers r hr n hn i j hij,
      mul_zero]
  have he : (1 + t • specializeMatrix (S := k) (integralOperators.rootDividedPower r 1) +
      t ^ 2 • specializeMatrix (S := k) (integralOperators.rootDividedPower r 2) +
      t ^ 3 • specializeMatrix (S := k) (integralOperators.rootDividedPower r 3)) - 1 =
      t • specializeMatrix (S := k) (integralOperators.rootDividedPower r 1) +
      t ^ 2 • specializeMatrix (S := k) (integralOperators.rootDividedPower r 2) +
      t ^ 3 • specializeMatrix (S := k) (integralOperators.rootDividedPower r 3) := by abel
  rw [he]
  exact raises_add (raises_add (hs 1 (by decide) t) (hs 2 (by decide) (t ^ 2)))
    (hs 3 (by decide) (t ^ 3))

variable [IsAlgClosed k] [CharP k 2]

private theorem root_self (r : Root) (t : k) :
    rootElement r t * rootElement r t = 1 := by
  rw [← rootElement_add, CharTwo.add_self_eq_zero, rootElement_zero]

private theorem root_inv (r : Root) (t : k) :
    (rootElement r t)⁻¹ = rootElement r t := by
  rw [rootElement_inv, CharTwo.neg_eq]

omit [CharP k 2] in
private theorem positive_simple (i : Fin 4) (t : k) :
    rootElement (typeF4SimpleRootIndex i) t ∈ positiveUnipotent (k := k) :=
  rootElement_mem_positiveUnipotent _ (typeF4RootPairing_base.isPos_of_mem_support
    (typeF4RootPairing_baseEquiv i).property) t

private abbrev simpleRep (i : Fin 4) : Variety.Point (Carrier (k := k)) :=
  rankOne (typeF4SimpleRootIndex i) 1

private theorem simpleRep_def (i : Fin 4) :
    simpleRep (k := k) i = rootElement (typeF4SimpleRootIndex i) 1 *
      rootElement (-typeF4SimpleRootIndex i) 1 *
      rootElement (typeF4SimpleRootIndex i) 1 := by
  simp [simpleRep, rankOne, CharTwo.neg_eq]

private theorem simpleRep_inv (i : Fin 4) :
    (simpleRep (k := k) i)⁻¹ = simpleRep i := by
  simp only [simpleRep_def, mul_inv_rev, root_inv, mul_assoc]

private theorem simpleRep_conj_root (i : Fin 4) (r : Root) (t : k) :
    simpleRep i * rootElement r t * (simpleRep i)⁻¹ =
      rootElement (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r) t := by
  apply carrierMatrix_injective
  have hw : carrierMatrix (simpleRep (k := k) i) =
      titsUnit [typeF4RootPairing_baseEquiv i] := by
    simp [simpleRep, rankOne, map_mul, carrierMatrix_root,
      titsUnit_cons, titsUnit_nil, typeF4RootPairing_baseEquiv_val]
  simp only [map_mul, map_inv, carrierMatrix_root, hw]
  exact ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.RankOneTransport.simple_conj
    (typeF4RootPairing_baseEquiv i) r t

private theorem simpleRep_conj_positive (i : Fin 4) (t : k) :
    simpleRep i * rootElement (typeF4SimpleRootIndex i) t * (simpleRep i)⁻¹ =
      rootElement (-typeF4SimpleRootIndex i) t :=
  simpleRep_conj_root i (typeF4SimpleRootIndex i) t

private theorem simpleRep_conj_negative (i : Fin 4) (t : k) :
    simpleRep i * rootElement (-typeF4SimpleRootIndex i) t * (simpleRep i)⁻¹ =
      rootElement (typeF4SimpleRootIndex i) t := by
  calc
    _ = (simpleRep i)⁻¹ * rootElement (-typeF4SimpleRootIndex i) t * simpleRep i := by
      rw [simpleRep_inv]
    _ = _ := by rw [← simpleRep_conj_positive i t]; group

private theorem simple_pair_cube (i : Fin 4) :
    (rootElement (k := k) (typeF4SimpleRootIndex i) 1 *
      rootElement (k := k) (-typeF4SimpleRootIndex i) 1) ^ 3 = 1 := by
  let x := rootElement (k := k) (typeF4SimpleRootIndex i) 1
  let y := rootElement (k := k) (-typeF4SimpleRootIndex i) 1
  have hxx : x * x = 1 := root_self _ _
  have hyy : y * y = 1 := root_self _ _
  have h : simpleRep (k := k) i * x = y * simpleRep (k := k) i := by
    have hc := simpleRep_conj_positive (k := k) i 1
    exact (mul_inv_eq_iff_eq_mul).mp hc
  rw [simpleRep_def] at h
  have hb : x * y * x = y * x * y := by
    have he := congrArg (fun z => z * x) h
    change (x * y * x * x) * x = (y * (x * y * x)) * x at he
    simpa only [mul_assoc, hxx, mul_one] using he
  change (x * y) ^ 3 = 1
  calc
    (x * y) ^ 3 = (x * y * x) * (y * x * y) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = (y * x * y) * (y * x * y) := by rw [hb]
    _ = (y * x) * (y * y) * (x * y) := by group
    _ = y * (x * x) * y := by rw [hyy]; group
    _ = 1 := by rw [hxx, mul_one, hyy]

omit [CharP k 2] in
private theorem root_one_ne_one (r : Root) : rootElement (k := k) r 1 ≠ 1 := by
  intro h
  have he : rootCurve r (1 : k) = rootCurve r (0 : k) := by
    have hc := congrArg carrierMatrix (h.trans (rootElement_zero r).symm)
    simpa only [carrierMatrix_root] using hc
  apply one_ne_zero (α := k)
  apply RootPairing.IntegralGeckConstruction.rootElement_injective
    (P := typeF4RootPairing) (b := typeF4RootPairing_base) (k := k) r
  simp only [RootPairing.IntegralGeckConstruction.rootElement,
    rootMorphismFamily, rootMorphism_apply]
  congr 1
  change Matrix.GeneralLinearGroup.toLin (rootCurve r (1 : k)) =
    Matrix.GeneralLinearGroup.toLin (rootCurve r (0 : k))
  exact congrArg Matrix.GeneralLinearGroup.toLin he

private theorem simple_pair_ne_one (i : Fin 4) :
    rootElement (typeF4SimpleRootIndex i) (1 : k) *
      rootElement (-typeF4SimpleRootIndex i) 1 ≠ 1 := by
  intro h
  have he : rootElement (-typeF4SimpleRootIndex i) (1 : k) =
      rootElement (typeF4SimpleRootIndex i) 1 := by
    rw [← root_inv]
    exact ((mul_eq_one_iff_eq_inv).mp h).symm
  have hp := typeF4RootPairing_base.isPos_of_mem_support
    (typeF4RootPairing_baseEquiv i).property
  have hn : ¬ typeF4RootPairing_base.IsPos (-typeF4SimpleRootIndex i) := by
    intro hn
    exact ((RootPairing.Base.IsPos.neg_iff_not typeF4RootPairing_base _).mp hn) hp
  have hmat : rootCurve (-typeF4SimpleRootIndex i) (1 : k) =
      rootCurve (typeF4SimpleRootIndex i) 1 := by
    simpa only [carrierMatrix_root] using congrArg carrierMatrix he
  have hl := rootCurve_lowers (-typeF4SimpleRootIndex i) hn (1 : k)
  rw [hmat] at hl
  have hu := rootCurve_raises (typeF4SimpleRootIndex i) hp (1 : k)
  have hz : (rootCurve (typeF4SimpleRootIndex i) (1 : k)).val - 1 = 0 := by
    ext a b
    rcases le_total (basisDegree a) (basisDegree b) with hab | hab
    · exact hu a b hab
    · exact hl a b (neg_le_neg hab)
  apply root_one_ne_one (k := k) (typeF4SimpleRootIndex i)
  apply carrierMatrix_injective
  rw [carrierMatrix_root, map_one]
  exact Units.ext (sub_eq_zero.mp hz)

/-- The exact transported rank-one pair cannot consist of two negative roots.
The proof uses grading and characteristic two, with no finite-field hypothesis. -/
private theorem transported_simple_sign {n : Variety.Point (Carrier (k := k))}
    (a : RootTransport n) (i : Fin 4) :
    typeF4RootPairing_base.IsPos (a.perm (typeF4SimpleRootIndex i)) ∨
      typeF4RootPairing_base.IsPos (a.perm (-typeF4SimpleRootIndex i)) := by
  by_contra h
  obtain ⟨hp, hn⟩ := not_or.mp h
  let z := (MulAut.conj n) (rootElement (typeF4SimpleRootIndex i) 1 *
    rootElement (-typeF4SimpleRootIndex i) 1)
  have hz : Raises (fun b => -basisDegree b) ((carrierMatrix z).val - 1) := by
    dsimp only [z]
    rw [map_mul]
    change Raises _ ((carrierMatrix
      ((n * rootElement (typeF4SimpleRootIndex i) 1 * n⁻¹) *
        (n * rootElement (-typeF4SimpleRootIndex i) 1 * n⁻¹))).val - 1)
    rw [a.conj_root, a.conj_root, map_mul, carrierMatrix_root, carrierMatrix_root]
    exact raises_unit_mul (rootCurve_lowers _ hp _) (rootCurve_lowers _ hn _)
  obtain ⟨e, he⟩ := two_power_eq_one_of_raises hz
  have h2 : z ^ (2 ^ e) = 1 := by
    apply carrierMatrix_injective
    rw [map_pow, map_one]
    exact Units.ext he
  have h3 : z ^ 3 = 1 := by
    dsimp only [z]
    rw [← map_pow, simple_pair_cube, map_one]
  have hz1 : z = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.dvd_one.mp
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
    have hcop : Nat.Coprime (2 ^ e) 3 := (by decide : Nat.Coprime 2 3).pow_left e
    rwa [hcop.gcd_eq_one] at hd
  exact simple_pair_ne_one (k := k) i
    ((MulAut.conj n).injective (hz1.trans (map_one _).symm))

private def rootSubgroup (r : Root) : Subgroup (Variety.Point (Carrier (k := k))) where
  carrier := Set.range (rootElement (k := k) r)
  one_mem' := ⟨0, rootElement_zero r⟩
  mul_mem' := by
    rintro a b ⟨t, rfl⟩ ⟨v, rfl⟩
    exact ⟨t + v, rootElement_add r t v⟩
  inv_mem' := by
    rintro a ⟨t, rfl⟩
    exact ⟨t, (root_inv r t).symm⟩

private theorem simple_positive_factorization (hpartition : PositiveRootPartition (k := k))
    (i : Fin 4) {u : Variety.Point (Carrier (k := k))} (hu : u ∈ positiveUnipotent (k := k)) :
    ∃ a ∈ positiveUnipotent (k := k),
      simpleRep i * a * (simpleRep i)⁻¹ ∈ positiveUnipotent (k := k) ∧
      ∃ t : k, u = a * rootElement (k := k) (typeF4SimpleRootIndex i) t := by
  let A := positiveUnipotent (k := k) ⊓
    (positiveUnipotent (k := k)).comap (MulAut.conj (simpleRep i)).toMonoidHom
  have hsplit (r : PositiveRoot) :
      (∀ t, rootElement (k := k) r.val t ∈ A) ∨
      (∀ t, rootElement (k := k) r.val t ∈ rootSubgroup (typeF4SimpleRootIndex i)) := by
    by_cases hr : r.val = typeF4SimpleRootIndex i
    · exact Or.inr (fun t => ⟨t, by rw [hr]⟩)
    · refine Or.inl (fun t => ⟨rootElement_mem_positiveUnipotent r.val r.property t, ?_⟩)
      change simpleRep i * rootElement (k := k) r.val t * (simpleRep i)⁻¹ ∈ positiveUnipotent (k := k)
      rw [simpleRep_conj_root]
      exact subset_closure ⟨_, t,
        r.property.reflectionPerm (typeF4RootPairing_baseEquiv i).property hr, rfl⟩
  obtain ⟨a, ha, b, hb, he⟩ := hpartition
    A (rootSubgroup (typeF4SimpleRootIndex i)) hsplit u hu
  obtain ⟨t, rfl⟩ := hb
  exact ⟨a, ha.1, ha.2, t, he⟩

/-- One simple representative multiplies a normalizer cell into another such cell.
The nonzero branch keeps its additional rank-one representative in the middle. -/
theorem simpleRepresentative_cell_exchange (hpartition : PositiveRootPartition (k := k))
    (htransport : ∀ n ∈ normalizerWords (k := k), Nonempty (RootTransport n))
    (i : Fin 4) {u : Variety.Point (Carrier (k := k))} (hu : u ∈ positiveUnipotent (k := k))
    {n : Variety.Point (Carrier (k := k))} (hn : n ∈ normalizerWords (k := k)) :
    ∃ a ∈ positiveUnipotent (k := k), ∃ n' ∈ normalizerWords (k := k), ∃ c ∈ positiveUnipotent (k := k),
      rankOne (typeF4SimpleRootIndex i) 1 * u * n = a * n' * c := by
  obtain ⟨a, ha, hsa, t, rfl⟩ := simple_positive_factorization hpartition i hu
  obtain ⟨rt⟩ := htransport n⁻¹ ((normalizerWords (k := k)).inv_mem hn)
  have hs : simpleRep i ∈ normalizerWords (k := k) := rankOne_mem _ _
  have hconj (r : Root) (v : k) :
      n⁻¹ * rootElement (k := k) r v * n =
        rootElement (k := k) (rt.perm r) ((rt.scale r : k) * v) := by
    simpa only [MulAut.conj_apply, inv_inv] using rt.conj_root r v
  by_cases hp : typeF4RootPairing_base.IsPos (rt.perm (typeF4SimpleRootIndex i))
  · refine ⟨simpleRep i * a * (simpleRep i)⁻¹, hsa,
      simpleRep i * n, (normalizerWords (k := k)).mul_mem hs hn,
      rootElement (k := k) (rt.perm (typeF4SimpleRootIndex i))
        ((rt.scale (typeF4SimpleRootIndex i) : k) * t),
      subset_closure ⟨_, _, hp, rfl⟩, ?_⟩
    calc
      _ = (simpleRep i * a * (simpleRep i)⁻¹) * (simpleRep i * n) *
        (n⁻¹ * rootElement (k := k) (typeF4SimpleRootIndex i) t * n) := by group
      _ = _ := by rw [hconj]
  · by_cases ht : t = 0
    · refine ⟨simpleRep i * a * (simpleRep i)⁻¹, hsa,
        simpleRep i * n, (normalizerWords (k := k)).mul_mem hs hn,
        1, (positiveUnipotent (k := k)).one_mem, ?_⟩
      rw [ht, rootElement_zero]
      group
    · have hneg := (transported_simple_sign rt i).resolve_left hp
      let v : kˣ := (Units.mk0 t ht)⁻¹
      let b := rootElement (k := k) (-typeF4SimpleRootIndex i) (v : k)
      let w := rankOne (-typeF4SimpleRootIndex i) v
      have hsplit : rootElement (k := k) (typeF4SimpleRootIndex i) t = b * w * b := by
        have hw : w = b * rootElement (k := k) (typeF4SimpleRootIndex i) t * b := by
          simp only [w, b, rankOne, neg_neg, v, inv_inv,
            Units.val_mk0, CharTwo.neg_eq]
        rw [hw]
        calc
          _ = (b * b) * rootElement (k := k) (typeF4SimpleRootIndex i) t *
            (b * b) := by rw [show b * b = 1 from root_self _ _]; simp
          _ = b * (b * rootElement (k := k) (typeF4SimpleRootIndex i) t * b) * b := by group
      have hsb : simpleRep i * b =
          rootElement (k := k) (typeF4SimpleRootIndex i) (v : k) *
            simpleRep i :=
        (mul_inv_eq_iff_eq_mul).mp (simpleRep_conj_negative i (v : k))
      refine ⟨(simpleRep i * a * (simpleRep i)⁻¹) *
          rootElement (k := k) (typeF4SimpleRootIndex i) (v : k),
        (positiveUnipotent (k := k)).mul_mem hsa (positive_simple i _),
        (simpleRep i * w) * n,
        (normalizerWords (k := k)).mul_mem
          ((normalizerWords (k := k)).mul_mem hs (rankOne_mem _ _)) hn,
        rootElement (k := k) (rt.perm (-typeF4SimpleRootIndex i))
          ((rt.scale (-typeF4SimpleRootIndex i) : k) * (v : k)),
        subset_closure ⟨_, _, hneg, rfl⟩, ?_⟩
      calc
        _ = (simpleRep i * a * (simpleRep i)⁻¹) *
            (simpleRep i * b) * w * b * n := by rw [hsplit]; group
        _ = ((simpleRep i * a * (simpleRep i)⁻¹) *
              rootElement (k := k) (typeF4SimpleRootIndex i) (v : k)) *
            ((simpleRep i * w) * n) * (n⁻¹ * b * n) := by rw [hsb]; group
        _ = _ := by rw [hconj]

/-- Positive collection and exact normalizer root transport imply negative-simple
cell multiplication, including all nonzero field parameters and torus factors. -/
theorem negativeSimpleExchange_of_partition
    (hpartition : PositiveRootPartition (k := k))
    (htransport : ∀ n ∈ normalizerWords (k := k), Nonempty (RootTransport n)) :
    NegativeSimpleExchange (k := k) := by
  intro i t u hu n hn
  obtain ⟨a, ha, n', hn', c, hc, he⟩ :=
    simpleRepresentative_cell_exchange hpartition htransport i hu hn
  obtain ⟨b, hb, n'', hn'', d, hd, he'⟩ :=
    simpleRepresentative_cell_exchange hpartition htransport i
      ((positiveUnipotent (k := k)).mul_mem (positive_simple i t) ha) hn'
  have hnegative : rootElement (k := k) (-typeF4SimpleRootIndex i) t =
      simpleRep i * rootElement (k := k) (typeF4SimpleRootIndex i) t * simpleRep i := by
    simpa only [simpleRep_inv] using (simpleRep_conj_positive i t).symm
  refine ⟨b, hb, n'', hn'', d * c, (positiveUnipotent (k := k)).mul_mem hd hc, ?_⟩
  calc
    _ = simpleRep i * rootElement (k := k) (typeF4SimpleRootIndex i) t *
      (simpleRep i * u * n) := by rw [hnegative]; group
    _ = (simpleRep i * (rootElement (k := k) (typeF4SimpleRootIndex i) t * a) * n') * c := by
      rw [he]
      group
    _ = b * n'' * (d * c) := by rw [he']; group

end Theory.AlgebraicGroup.F4Chevalley.DenseParameters.CarrierBruhat
