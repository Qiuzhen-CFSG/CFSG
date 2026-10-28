module
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.Basic
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.Words
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.LinearProjection.Generation
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.RootCurve
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.WeylOpposition

/-!
# Complete coordinates on the signed type VI Ree blocks

Only the two end simple roots belong to the positive linear support. Their
root curves commute, so the split block has two independent additive
coordinates, recovered from explicit matrix entries. The supplied twist
forces the second coordinate to be the inverse Tits power of the first.
This proves coverage of the entire fixed intersection. Conjugation by the
checked fixed opposition element transports the result to the negative block.

Restricting a block-preserving automorphism and conjugating by these charts
constructs its additive parameter equivalences. No field multiplicativity
or compatibility between the two signs is assumed or asserted here.

Source: GLS3, Table 2.4 type VI and §§2.3–2.5,
`refs/KGroup/GLS3/chapter2.tex`. Adapted from the retained field-recovery
attempt's `Scratch/ReeFieldRecovery/Probe.lean`.
-/

@[expose] public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open scoped Matrix
open LargeLocalSeeds Subgroup Parabolics
open Parabolics.OuterLocal.SuzukiCommutators
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
local notation "b" => typeF4RootPairing_base
local notation "s" => typeF4RootPairing_baseEquiv
variable {m : ℕ}

private theorem positive_column (i j : typeF4RootPairing_base.support) (t : CoefficientField m) :
    positiveMatrix i t *ᵥ Pi.single (Sum.inl j) 1 =
      Pi.single (Sum.inl j : F4Chevalley.BasisIndex) 1 +
        (t * (|typeF4RootPairing_base.cartanMatrix i j| : ℤ)) •
          Pi.single (Sum.inr (i : F4Chevalley.Root) : F4Chevalley.BasisIndex) 1 := by
  classical
  ext (k | k) <;>
    simp [Matrix.mulVec_single, positiveMatrix_formula, eDividedPower, eMatrix,
      Matrix.one_apply, Pi.single_apply]

private theorem end_commute (t u : CoefficientField m) :
    Commute (rootGeneratorInGroup m (typeF4SimpleRootIndex 0) t)
      (rootGeneratorInGroup m (typeF4SimpleRootIndex 3) u) := by
  have h := commute_positive_positive_of_cartan_eq_zero
    (s 0) (s 3)
    (by intro h; have := typeF4RootPairing_baseEquiv.injective h; contradiction)
    (by rw [typeF4RootPairing_base_cartan_apply]; norm_num [typeF4CartanMatrix, Fin.ext_iff]) t u
  apply Subtype.ext
  change F4Chevalley.rootCurve _ t * F4Chevalley.rootCurve _ u =
    F4Chevalley.rootCurve _ u * F4Chevalley.rootCurve _ t
  simpa only [F4Chevalley.rootCurve, F4Chevalley.integralOperators,
    ← typeF4RootPairing_baseEquiv_val, rootCurveUnit_simple] using
    show positiveUnit (s 0) t * positiveUnit (s 3) u =
      positiveUnit (s 3) u * positiveUnit (s 0) t from congrArg Subtype.val h.eq

def linearSplitWord (m : ℕ) (t u : CoefficientField m) : SplitGroup m :=
  rootGeneratorInGroup m (typeF4SimpleRootIndex 0) t *
    rootGeneratorInGroup m (typeF4SimpleRootIndex 3) u

private theorem linearSplitWord_matrix (t u : CoefficientField m) :
    (linearSplitWord m t u).val.val = positiveMatrix (s 0) t * positiveMatrix (s 3) u := by
  change (F4Chevalley.rootCurve _ t).val * (F4Chevalley.rootCurve _ u).val = _
  simp only [F4Chevalley.rootCurve, F4Chevalley.integralOperators,
    ← typeF4RootPairing_baseEquiv_val, rootCurveUnit_simple, positiveUnit_val]

private theorem linearSplitWord_first (t u : CoefficientField m) :
    (linearSplitWord m t u).val.val (Sum.inr (typeF4SimpleRootIndex 0)) (Sum.inl (s 1)) = t := by
  have h : (linearSplitWord m t u).val.val *ᵥ Pi.single (Sum.inl (s 1)) 1 =
      Pi.single (Sum.inl (s 1) : F4Chevalley.BasisIndex) 1 +
        t • Pi.single (Sum.inr (typeF4SimpleRootIndex 0) : F4Chevalley.BasisIndex) 1 := by
    rw [linearSplitWord_matrix, ← Matrix.mulVec_mulVec, positive_column]
    norm_num [typeF4RootPairing_base_cartan_apply, typeF4CartanMatrix, Fin.ext_iff]
    simpa [Matrix.mulVec_single, typeF4RootPairing_base_cartan_apply, typeF4CartanMatrix, Fin.ext_iff,
      typeF4RootPairing_baseEquiv_val] using positive_column (s 0) (s 1) t
  have hx := congrFun h (Sum.inr (typeF4SimpleRootIndex 0))
  simpa [Matrix.mulVec_single] using hx

private theorem linearSplitWord_second (t u : CoefficientField m) :
    (linearSplitWord m t u).val.val (Sum.inr (typeF4SimpleRootIndex 3)) (Sum.inl (s 2)) = u := by
  have hc : (linearSplitWord m t u).val.val = positiveMatrix (s 3) u * positiveMatrix (s 0) t := by
    rw [linearSplitWord_matrix]
    have he := congrArg (fun x : SplitGroup m => x.val.val) (end_commute t u).eq
    simpa only [Subgroup.coe_mul, Units.val_mul, rootGeneratorInGroup, rootGenerator,
      F4Chevalley.rootCurve, F4Chevalley.integralOperators,
      ← typeF4RootPairing_baseEquiv_val, rootCurveUnit_simple, positiveUnit_val] using he
  have h : (linearSplitWord m t u).val.val *ᵥ Pi.single (Sum.inl (s 2)) 1 =
      Pi.single (Sum.inl (s 2) : F4Chevalley.BasisIndex) 1 +
        u • Pi.single (Sum.inr (typeF4SimpleRootIndex 3) : F4Chevalley.BasisIndex) 1 := by
    rw [hc, ← Matrix.mulVec_mulVec, positive_column]
    norm_num [typeF4RootPairing_base_cartan_apply, typeF4CartanMatrix, Fin.ext_iff]
    simpa [Matrix.mulVec_single, typeF4RootPairing_base_cartan_apply, typeF4CartanMatrix, Fin.ext_iff,
      typeF4RootPairing_baseEquiv_val] using positive_column (s 3) (s 2) u
  have hx := congrFun h (Sum.inr (typeF4SimpleRootIndex 3))
  simpa [Matrix.mulVec_single] using hx

theorem linearSplitWord_injective {t u v w : CoefficientField m}
    (h : linearSplitWord m t u = linearSplitWord m v w) : t = v ∧ u = w := by
  constructor
  · simpa only [linearSplitWord_first] using congrArg
      (fun x : SplitGroup m => x.val.val (Sum.inr (typeF4SimpleRootIndex 0)) (Sum.inl (s 1))) h
  · simpa only [linearSplitWord_second] using congrArg
      (fun x : SplitGroup m => x.val.val (Sum.inr (typeF4SimpleRootIndex 3)) (Sum.inl (s 2))) h

private theorem linear_positive_roots (r : F4Chevalley.Root) :
    IsSimpleBlockRoot .linear true r ↔
      r = typeF4SimpleRootIndex 0 ∨ r = typeF4SimpleRootIndex 3 := by
  constructor
  · rintro ⟨hs, hp⟩
    obtain ⟨i, hi, hr | hr⟩ := Parabolics.BinaryLinear.isLeviRoot_of_middle_coefficients_zero r
      (hs 1 (by simp [leviNodes])) (hs 2 (by simp [leviNodes]))
    · have hi' : i = 0 ∨ i = 3 := by simpa [leviNodes] using hi
      rcases hi' with rfl | rfl
      · exact Or.inl hr
      · exact Or.inr hr
    · have hpos := typeF4RootPairing_base.isPos_of_mem_support (s i).property
      rw [hr, RootPairing.Base.IsPos.neg_iff_not] at hp
      exact (hp hpos).elim
  · rintro (rfl | rfl)
    all_goals
      constructor
      · intro i hi
        fin_cases i <;> simp_all [leviNodes, typeF4SimpleCoefficient,
          typeF4SimpleRoot, Fin.ext_iff] <;> norm_num
      · exact typeF4RootPairing_base.isPos_of_mem_support (s _).property

private theorem root_add (r : F4Chevalley.Root) (t u : CoefficientField m) :
    rootGeneratorInGroup m r (t + u) =
      rootGeneratorInGroup m r t * rootGeneratorInGroup m r u :=
  Subtype.ext (F4Chevalley.rootCurve_add r t u)

private theorem root_zero (r : F4Chevalley.Root) : rootGeneratorInGroup m r 0 = 1 :=
  Subtype.ext (F4Chevalley.rootCurve_zero r)

theorem linearSplitWord_add (t u v w : CoefficientField m) :
    linearSplitWord m (t + v) (u + w) = linearSplitWord m t u * linearSplitWord m v w := by
  simp only [linearSplitWord, root_add]
  rw [mul_assoc, ← mul_assoc (rootGeneratorInGroup m (typeF4SimpleRootIndex 0) v),
    (end_commute v u).eq, mul_assoc, ← mul_assoc]

def linearSplitHom (m : ℕ) : Multiplicative (CoefficientField m × CoefficientField m) →* SplitGroup m where
  toFun p := linearSplitWord m p.toAdd.1 p.toAdd.2
  map_one' := by
    change linearSplitWord m 0 0 = 1
    simp only [linearSplitWord, root_zero, mul_one]
  map_mul' p q := linearSplitWord_add _ _ _ _

theorem linearSplitWord_mem (t u : CoefficientField m) :
    linearSplitWord m t u ∈ splitSimpleBlock m .linear true := by
  exact mul_mem
    (subset_closure ⟨_, _, (linear_positive_roots _).mpr (Or.inl rfl), rfl⟩)
    (subset_closure ⟨_, _, (linear_positive_roots _).mpr (Or.inr rfl), rfl⟩)

/-- Every element of the generated end-root block has two split coordinates. -/
theorem linearSplitWord_surjective {x : SplitGroup m}
    (hx : x ∈ splitSimpleBlock m .linear true) :
    ∃ t u, linearSplitWord m t u = x := by
  have hle : splitSimpleBlock m .linear true ≤ (linearSplitHom m).range := by
    apply (closure_le _).mpr
    rintro x ⟨r, t, hr, rfl⟩
    rcases (linear_positive_roots r).mp hr with rfl | rfl
    · refine ⟨Multiplicative.ofAdd (t, 0), ?_⟩
      change linearSplitWord m t 0 = _
      simp only [linearSplitWord, root_zero, mul_one]
    · refine ⟨Multiplicative.ofAdd (0, t), ?_⟩
      change linearSplitWord m 0 t = _
      simp only [linearSplitWord, root_zero, one_mul]
  obtain ⟨p, hp⟩ := hle hx
  exact ⟨p.toAdd.1, p.toAdd.2, hp⟩

/-- The fixed equation is imposed on all split block elements, with no coverage assumption. -/
theorem linearSplitWord_fixed_iff (d : LocalBlockInput m) (t u : CoefficientField m) :
    d.twist (linearSplitWord m t u) = linearSplitWord m t u ↔
      u = rootFieldEnd m (typeF4SimpleRootIndex 0) t := by
  have ht : d.twist (linearSplitWord m t u) =
      linearSplitWord m (rootFieldEnd m (typeF4SimpleRootIndex 3) u)
        (rootFieldEnd m (typeF4SimpleRootIndex 0) t) := by
    simp only [linearSplitWord, map_mul, d.twist_root, ← rootFieldEnd_apply,
      exceptionalRootPermutation_simple]
    exact (end_commute _ _).eq.symm
  rw [ht]
  constructor
  · intro h
    exact (linearSplitWord_injective h).2.symm
  · rintro rfl
    have h := Parabolics.RadicalCoordinates.rootFieldEnd_twice m (typeF4SimpleRootIndex 0) t
    rw [exceptionalRootPermutation_simple] at h
    change rootFieldEnd m (typeF4SimpleRootIndex 3)
      (rootFieldEnd m (typeF4SimpleRootIndex 0) t) = t at h
    rw [h]

def positiveLinearElement (d : LocalBlockInput m) (t : CoefficientField m) :
    simpleBlock d .linear true :=
  ⟨⟨linearSplitWord m t (rootFieldEnd m (typeF4SimpleRootIndex 0) t),
      (linearSplitWord_fixed_iff d t _).mpr rfl⟩, linearSplitWord_mem _ _⟩

theorem positiveLinearElement_bijective (d : LocalBlockInput m) :
    Function.Bijective (positiveLinearElement d) := by
  constructor
  · intro t u h
    exact (linearSplitWord_injective (congrArg (fun x : simpleBlock d .linear true => x.val.val) h)).1
  · intro x
    obtain ⟨t, u, h⟩ := linearSplitWord_surjective x.property
    have hf : d.twist (linearSplitWord m t u) = linearSplitWord m t u := by
      rw [h]
      exact x.val.property
    have hu := (linearSplitWord_fixed_iff d t u).mp hf
    refine ⟨t, Subtype.ext (Subtype.ext ?_)⟩
    change linearSplitWord m t (rootFieldEnd m (typeF4SimpleRootIndex 0) t) = x.val.val
    rw [← hu]
    exact h

/-- The type VI positive fixed block is exactly the additive coefficient group. -/
def positiveLinearEquiv (d : LocalBlockInput m) :
    Multiplicative (CoefficientField m) ≃* simpleBlock d .linear true :=
  MulEquiv.ofBijective
    ({
      toFun := fun t => positiveLinearElement d t.toAdd
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        change linearSplitWord m 0 (rootFieldEnd m _ 0) = 1
        simp only [map_zero, linearSplitWord, root_zero, mul_one]
      map_mul' := fun t u => by
        apply Subtype.ext
        apply Subtype.ext
        change linearSplitWord m (t.toAdd + u.toAdd) (rootFieldEnd m _ (t.toAdd + u.toAdd)) = _
        rw [map_add, linearSplitWord_add]
        rfl } : Multiplicative (CoefficientField m) →* simpleBlock d .linear true)
    (positiveLinearElement_bijective d)

private theorem coefficient_neg (r : F4Chevalley.Root) (i : Fin 4) :
    typeF4SimpleCoefficient (-r).val i = -typeF4SimpleCoefficient r.val i := by
  have hr : (-r).val = -r.val := by
    change typeF4RootPairing.root (-r) = -typeF4RootPairing.root r
    rw [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  rw [hr]
  fin_cases i <;> simp only [typeF4SimpleCoefficient, Pi.neg_apply] <;> ring

/-- Opposition preserves the Levi support and reverses its sign. -/
theorem simpleBlockRoot_neg_iff (side : Side) (r : F4Chevalley.Root) :
    IsSimpleBlockRoot side false (-r) ↔ IsSimpleBlockRoot side true r := by
  simp only [IsSimpleBlockRoot, coefficient_neg, neg_eq_zero,
    Bool.false_eq_true, ↓reduceIte, RootPairing.Base.IsPos.neg_iff_not, not_not]

theorem splitOpposition_map_simpleBlock (side : Side) :
    (splitSimpleBlock m side true).map
      (MulAut.conj (PairNormalization.splitOpposition m)).toMonoidHom =
        splitSimpleBlock m side false := by
  simp only [splitSimpleBlock, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨r, t, hr, rfl⟩, rfl⟩
    exact ⟨-r, t, (simpleBlockRoot_neg_iff side r).mpr hr,
      PairNormalization.splitOpposition_conj_root m r t⟩
  · rintro ⟨r, t, hr, rfl⟩
    refine ⟨rootGeneratorInGroup m (-r) t, ⟨-r, t, ?_, rfl⟩, ?_⟩
    · exact (simpleBlockRoot_neg_iff side (-r)).mp (by simpa only [neg_neg] using hr)
    · simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, neg_neg] using
        PairNormalization.splitOpposition_conj_root m (-r) t

/-- Opposition exchanges the actual fixed intersections, including the type V block. -/
theorem opposition_map_simpleBlock (d : LocalBlockInput m) (side : Side) :
    (simpleBlock d side true).map
      (MulAut.conj (PairNormalization.opposition d)).toMonoidHom =
        simpleBlock d side false := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    change PairNormalization.splitOpposition m * y.val *
      (PairNormalization.splitOpposition m)⁻¹ ∈ splitSimpleBlock m side false
    rw [← splitOpposition_map_simpleBlock side]
    exact ⟨y.val, hy, rfl⟩
  · intro x hx
    refine ⟨(PairNormalization.opposition d)⁻¹ * x * PairNormalization.opposition d, ?_, ?_⟩
    · have hx' : x.val ∈ splitSimpleBlock m side false := hx
      rw [← splitOpposition_map_simpleBlock side] at hx'
      obtain ⟨y, hy, he⟩ := hx'
      change (PairNormalization.splitOpposition m)⁻¹ * x.val *
        PairNormalization.splitOpposition m ∈ splitSimpleBlock m side true
      rw [← he]
      change (PairNormalization.splitOpposition m)⁻¹ *
        (PairNormalization.splitOpposition m * y * (PairNormalization.splitOpposition m)⁻¹) *
        PairNormalization.splitOpposition m ∈ splitSimpleBlock m side true
      have hc : (PairNormalization.splitOpposition m)⁻¹ *
          (PairNormalization.splitOpposition m * y * (PairNormalization.splitOpposition m)⁻¹) *
          PairNormalization.splitOpposition m = y := by group
      rw [hc]
      exact hy
    · simp [MulAut.conj_apply, mul_assoc]

def simpleBlockOppositionEquiv (d : LocalBlockInput m) (side : Side) :
    simpleBlock d side true ≃* simpleBlock d side false :=
  ((MulAut.conj (PairNormalization.opposition d)).subgroupMap (simpleBlock d side true)).trans
    (MulEquiv.subgroupCongr (opposition_map_simpleBlock d side))

/-- Additive coordinates on both signs of the type VI fixed block. -/
def linearEquiv (d : LocalBlockInput m) (positive : Bool) :
    Multiplicative (CoefficientField m) ≃* simpleBlock d .linear positive :=
  match positive with
  | true => positiveLinearEquiv d
  | false => (positiveLinearEquiv d).trans (simpleBlockOppositionEquiv d .linear)

def linearElement (d : LocalBlockInput m) (positive : Bool) (t : CoefficientField m) :
    d.fixedGroup := (linearEquiv d positive (Multiplicative.ofAdd t)).val

theorem linearElement_mem (d : LocalBlockInput m) (positive : Bool) (t : CoefficientField m) :
    linearElement d positive t ∈ simpleBlock d .linear positive :=
  (linearEquiv d positive (Multiplicative.ofAdd t)).property

/-- Every element of either signed fixed linear block is one of the parameterized elements. -/
theorem linearElement_surjective (d : LocalBlockInput m) (positive : Bool)
    {x : d.fixedGroup} (hx : x ∈ simpleBlock d .linear positive) :
    ∃ t, linearElement d positive t = x := by
  obtain ⟨t, ht⟩ := (linearEquiv d positive).surjective ⟨x, hx⟩
  exact ⟨t.toAdd, congrArg Subtype.val ht⟩

theorem linearElement_injective (d : LocalBlockInput m) (positive : Bool) :
    Function.Injective (linearElement d positive) := by
  intro t u h
  exact (linearEquiv d positive).injective (Subtype.ext h)

theorem linearElement_add (d : LocalBlockInput m) (positive : Bool) (t u : CoefficientField m) :
    linearElement d positive (t + u) = linearElement d positive t * linearElement d positive u :=
  congrArg Subtype.val ((linearEquiv d positive).map_mul (Multiplicative.ofAdd t) (Multiplicative.ofAdd u))

theorem linearElement_positive (d : LocalBlockInput m) (t : CoefficientField m) :
    (linearElement d true t).val = linearSplitWord m t (rootFieldEnd m (typeF4SimpleRootIndex 0) t) := rfl

theorem linearElement_negative (d : LocalBlockInput m) (t : CoefficientField m) :
    (linearElement d false t).val =
      rootGeneratorInGroup m (-typeF4SimpleRootIndex 0) t *
        rootGeneratorInGroup m (-typeF4SimpleRootIndex 3)
          (rootFieldEnd m (typeF4SimpleRootIndex 0) t) := by
  change PairNormalization.splitOpposition m *
    (rootGeneratorInGroup m (typeF4SimpleRootIndex 0) t *
      rootGeneratorInGroup m (typeF4SimpleRootIndex 3) _) *
        (PairNormalization.splitOpposition m)⁻¹ = _
  rw [show ∀ x y : SplitGroup m,
    PairNormalization.splitOpposition m * (x * y) * (PairNormalization.splitOpposition m)⁻¹ =
      (PairNormalization.splitOpposition m * x * (PairNormalization.splitOpposition m)⁻¹) *
      (PairNormalization.splitOpposition m * y * (PairNormalization.splitOpposition m)⁻¹) from
        fun x y => by group]
  rw [PairNormalization.splitOpposition_conj_root, PairNormalization.splitOpposition_conj_root]
  rfl

/-- Restriction to a preserved signed block. -/
def blockRestriction (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
    (hb : PreservesSimpleBlocks d a) (side : Side) (positive : Bool) :
    MulAut (simpleBlock d side positive) :=
  (a.subgroupMap (simpleBlock d side positive)).trans (MulEquiv.subgroupCongr (hb side positive))

/-- The additive parameter map is derived from the actual restricted group action. -/
def linearParameterAut (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
    (hb : PreservesSimpleBlocks d a) (positive : Bool) :
    CoefficientField m ≃+ CoefficientField m :=
  MulEquiv.toAdditive ((linearEquiv d positive).trans
    ((blockRestriction d a hb .linear positive).trans (linearEquiv d positive).symm))

theorem linearParameterAut_action (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
    (hb : PreservesSimpleBlocks d a) (positive : Bool) (t : CoefficientField m) :
    a (linearElement d positive t) =
      linearElement d positive (linearParameterAut d a hb positive t) := by
  change _ = ((linearEquiv d positive)
    ((linearEquiv d positive).symm
      (blockRestriction d a hb .linear positive (linearEquiv d positive (Multiplicative.ofAdd t))))).val
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem rootFieldEnd_simple_zero_eq_theta (t : CoefficientField m) :
    rootFieldEnd m (typeF4SimpleRootIndex 0) t = theta m t := by
  have h0 : IsLongRoot (typeF4SimpleRootIndex 0) :=
    (typeF4SimpleRootIndex_mem_pair_iff 0).mpr (by decide)
  rw [rootFieldEnd_apply, exceptionalParameter_of_long h0]
  rfl

/-- The constructed chart is the literal type VI word for either sign. -/
theorem linearElement_word (d : LocalBlockInput m) (positive : Bool)
    (t : CoefficientField m) : (linearElement d positive t).val = linearWord m positive t := by
  cases positive
  · rw [linearElement_negative, rootFieldEnd_simple_zero_eq_theta]
    rfl
  · rw [linearElement_positive]
    rw [rootFieldEnd_simple_zero_eq_theta]
    rfl

end ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
