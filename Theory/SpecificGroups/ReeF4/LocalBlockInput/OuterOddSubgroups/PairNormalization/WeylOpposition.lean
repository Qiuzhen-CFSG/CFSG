module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.RootPair
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.WeylOpposition.Matrix

/-!
# A fixed Weyl opposition representative for a supplied Ree group

Write `c = n₀ n₁ n₂ n₃` using the parameter-one simple root words in the
actual split matrix group. The matrix calculation in `WeylOpposition.Matrix`
identifies `c⁶` with the opposition involution. The supplied twist reverses
the four simple nodes, hence sends `c` to its inverse and fixes `c⁶`.

The same matrix calculation conjugates every positive root curve to its
negative. Mapping the generated closures and intersecting with the supplied
fixed group gives the exact two subgroups defined in `RootPair`. This works
for every supplied `LocalBlockInput`, without constructing an exceptional
endomorphism or comparing its fixed group with another model.

Source: GLS3, 2.3.4–2.3.8 and 2.4.8,
`refs/KGroup/GLS3/chapter2.tex`. The subsequent normalization assembly belongs
to `PairNormalization`.
-/

@[expose] public section
namespace ReeF4.LocalBlockInput.PairNormalization
open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction
open ReeF4.WordRelations.Faithfulness.Adjoint WeylOpposition
noncomputable section
-- This public section exports even local instances. An explicit name avoids
-- colliding with the anonymous root-negation helper in `PairNormalization.Disjoint`.
local instance oppositionRootNeg : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
local notation "s" => typeF4RootPairing_baseEquiv

open ReeF4
variable {m : ℕ}

/-- A simple Weyl representative, written in the actual split root generators. -/
def simpleLift (m : ℕ) (i : Fin 4) : SplitGroup m :=
  rootGeneratorInGroup m (typeF4SimpleRootIndex i) 1 *
    rootGeneratorInGroup m (-typeF4SimpleRootIndex i) 1 *
    rootGeneratorInGroup m (typeF4SimpleRootIndex i) 1

/-- The product of the four numbered simple Weyl representatives. -/
def coxeterElement (m : ℕ) : SplitGroup m :=
  simpleLift m 0 * simpleLift m 1 * simpleLift m 2 * simpleLift m 3

private lemma simpleLift_coe (m : ℕ) (i : Fin 4) :
    (simpleLift m i : MatrixUnits m) = titsUnit (K := CoefficientField m) (s i) := by
  change F4Chevalley.rootCurve _ _ * F4Chevalley.rootCurve _ _ *
    F4Chevalley.rootCurve _ _ = _
  simp only [← typeF4RootPairing_baseEquiv_val i, rootCurve_simple,
    rootCurve_neg_simple, titsUnit, CharTwo.neg_eq]

private lemma coxeterElement_coe (m : ℕ) :
    (coxeterElement m : MatrixUnits m) = titsWordUnit coxeterWord := by
  simp only [coxeterElement, Subgroup.coe_mul, simpleLift_coe, coxeterWord, titsWordUnit,
    mul_one, mul_assoc]

private lemma simpleLift_inv (m : ℕ) (i : Fin 4) : (simpleLift m i)⁻¹ = simpleLift m i := by
  have h (r : F4Chevalley.Root) : (rootGeneratorInGroup m r 1)⁻¹ =
      rootGeneratorInGroup m r 1 := by
    apply Subtype.ext
    change (F4Chevalley.rootCurve r (1 : CoefficientField m))⁻¹ = F4Chevalley.rootCurve r 1
    rw [F4Chevalley.rootCurve_inv]
    rw [CharTwo.neg_eq]
  simp only [simpleLift, mul_inv_rev, h, mul_assoc]

private lemma twist_simpleLift (d : LocalBlockInput m) (i : Fin 4) :
    d.twist (simpleLift m i) = simpleLift m (Fin.revPerm i) := by
  have hp (r : F4Chevalley.Root) : exceptionalParameter r (1 : CoefficientField m) = 1 := by
    by_cases hr : IsLongRoot r
    · exact exceptionalParameter_of_long hr 1
    · simpa only [one_pow] using exceptionalParameter_of_short hr (1 : CoefficientField m)
  simp only [simpleLift, map_mul, d.twist_root, exceptionalRootPermutation_simple,
    exceptionalRootPermutation_neg_simple, one_pow, hp]

private lemma twist_coxeterElement (d : LocalBlockInput m) :
    d.twist (coxeterElement m) = (coxeterElement m)⁻¹ := by
  simp only [coxeterElement, map_mul, twist_simpleLift, mul_inv_rev, simpleLift_inv, mul_assoc]
  rfl

/-- The split opposition representative: the sixth power of the Coxeter element. -/
def splitOpposition (m : ℕ) : SplitGroup m := coxeterElement m ^ 6

/-- The representative has precisely the matrix exchanging opposite root coordinates. -/
theorem splitOpposition_coe (m : ℕ) :
    (splitOpposition m : MatrixUnits m) = omegaUnit := by
  rw [splitOpposition, Subgroup.coe_pow, coxeterElement_coe, coxeterWord_pow_six_eq_omega]

/-- The split opposition representative is self-inverse. -/
theorem splitOpposition_inv (m : ℕ) : (splitOpposition m)⁻¹ = splitOpposition m := by
  apply Subtype.ext
  simp only [Subgroup.coe_inv, splitOpposition_coe]
  exact Units.ext rfl

/-- The supplied exceptional twist fixes the explicit opposition representative. -/
theorem twist_splitOpposition (d : LocalBlockInput m) :
    d.twist (splitOpposition m) = splitOpposition m := by
  rw [splitOpposition, map_pow, twist_coxeterElement, inv_pow]
  exact splitOpposition_inv m

/-- Conjugation exchanges opposite root generators with the same parameter. -/
theorem splitOpposition_conj_root (m : ℕ) (r : F4Chevalley.Root) (t : CoefficientField m) :
    splitOpposition m * rootGeneratorInGroup m r t * (splitOpposition m)⁻¹ =
      rootGeneratorInGroup m (-r) t := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, splitOpposition_coe]
  exact omega_conj_rootCurve r t

/-- The explicit Weyl representative exchanges the two split root closures. -/
theorem splitOpposition_map_unipotent (m : ℕ) :
    (LargeLocalSeeds.splitUnipotent m).map (MulAut.conj (splitOpposition m)).toMonoidHom =
      LocalBlockInput.splitNegativeUnipotent m := by
  have h (P : F4Chevalley.Root → Prop) :
      (Subgroup.closure {x | ∃ (r : F4Chevalley.Root) (t : CoefficientField m),
        P r ∧ x = rootGeneratorInGroup m r t}).map
          (MulAut.conj (splitOpposition m)).toMonoidHom =
      Subgroup.closure {x | ∃ (r : F4Chevalley.Root) (t : CoefficientField m),
        P (-r) ∧ x = rootGeneratorInGroup m r t} := by
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨r, t, hr, rfl⟩, rfl⟩
      refine ⟨-r, t, ?_, ?_⟩
      · simpa only [neg_neg] using hr
      · exact splitOpposition_conj_root m r t
    · rintro ⟨r, t, hr, rfl⟩
      refine ⟨rootGeneratorInGroup m (-r) t, ⟨-r, t, hr, rfl⟩, ?_⟩
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, neg_neg] using
        splitOpposition_conj_root m (-r) t
  simpa only [LargeLocalSeeds.splitUnipotent, LocalBlockInput.splitNegativeUnipotent,
    RootPairing.Base.IsPos.neg_iff_not] using h typeF4RootPairing_base.IsPos

/-- The opposition representative in the supplied twist-fixed group. -/
def opposition (d : LocalBlockInput m) : d.fixedGroup :=
  ⟨splitOpposition m, (d.mem_fixedGroup _).mpr (twist_splitOpposition d)⟩

/-- Conjugation by the fixed representative sends the standard subgroup to its opposite. -/
theorem opposition_map_unipotent (d : LocalBlockInput m) :
    (LargeLocalSeeds.standardUnipotent d).map (MulAut.conj (opposition d)).toMonoidHom =
      LocalBlockInput.oppositeUnipotent d := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    change splitOpposition m * y.val * (splitOpposition m)⁻¹ ∈
      LocalBlockInput.splitNegativeUnipotent m
    rw [← splitOpposition_map_unipotent m]
    exact ⟨y.val, hy, rfl⟩
  · intro x hx
    refine ⟨(opposition d)⁻¹ * x * opposition d, ?_, ?_⟩
    · have hx' : x.val ∈ LocalBlockInput.splitNegativeUnipotent m := hx
      rw [← splitOpposition_map_unipotent m] at hx'
      obtain ⟨y, hy, he⟩ := hx'
      change (splitOpposition m)⁻¹ * x.val * splitOpposition m ∈
        LargeLocalSeeds.splitUnipotent m
      rw [← he]
      change (splitOpposition m)⁻¹ * (splitOpposition m * y * (splitOpposition m)⁻¹) *
        splitOpposition m ∈ LargeLocalSeeds.splitUnipotent m
      have hc : (splitOpposition m)⁻¹ * (splitOpposition m * y * (splitOpposition m)⁻¹) *
          splitOpposition m = y := by group
      rw [hc]
      exact hy
    · simp [MulAut.conj_apply, mul_assoc]

/-- The standard positive and negative fixed root subgroups are conjugate.
No simplicity, perfectness, index, or lower bound on the field exponent is needed. -/
theorem exists_opposition (d : LocalBlockInput m) :
    ∃ w : d.fixedGroup,
      (LargeLocalSeeds.standardUnipotent d).map (MulAut.conj w).toMonoidHom =
        LocalBlockInput.oppositeUnipotent d :=
  ⟨opposition d, opposition_map_unipotent d⟩

end
end ReeF4.LocalBlockInput.PairNormalization
end
