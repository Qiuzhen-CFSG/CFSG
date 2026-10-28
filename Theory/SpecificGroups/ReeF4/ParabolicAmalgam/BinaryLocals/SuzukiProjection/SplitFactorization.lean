module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.Levi
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.SplitFactorization.RootGeneration
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.SplitFactorization.RootNormalization
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.SplitFactorization.Separation
public import Mathlib.GroupTheory.Complement

/-!
# Binary Suzuki-side split factorization from root calculations

Matrix grading proves that the actual middle-node Levi and the specified
positive-root radical have trivial intersection. The subsystem root calculation
puts every positive subsystem root curve in the signed-simple Levi, and the
matrix conjugation calculation shows that every seed root curve normalizes the
radical. Closure induction gives seed generation and relative normality; the
subgroup product then gives a unique Levi–radical factorization.

The conditional assembly lemmas are retained, and the two proved root
calculations discharge their premises in the unconditional theorems below.
This concerns the genuine split F₄ carrier at `m = 0`, before taking fixed
points. Source: the parabolic Levi construction underlying Aschbacher–Smith,
F.1.12(I)(5), printed pp.263–264 (PDF pp.274–275) of `refs/quasithin.pdf`.
-/

public section
noncomputable section

namespace ReeF4.Parabolics.BinarySuzuki

open Theory.AlgebraicGroup StandardRootSystem LargeLocalSeeds Subgroup

local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private theorem rootGenerator_inv (r : F4Chevalley.Root) (t : CoefficientField 0) :
    (rootGeneratorInGroup 0 r t)⁻¹ = rootGeneratorInGroup 0 r (-t) := by
  apply Subtype.ext
  exact F4Chevalley.rootCurve_inv r t

/-- Checking conjugation of radical generators by seed generators suffices for
normality in the split seed, including conjugation by inverse root parameters. -/
theorem splitRadicalInSeed_normal_of_root_conjugation
    (hconj : ∀ (r s : F4Chevalley.Root) (a b : CoefficientField 0),
      IsSeedRoot .suzuki r → IsRadicalRoot .suzuki s →
      rootGeneratorInGroup 0 r a * rootGeneratorInGroup 0 s b *
        (rootGeneratorInGroup 0 r a)⁻¹ ∈ splitRadical 0 .suzuki) :
    splitRadicalInSeed.Normal := by
  apply (normal_subgroupOf_iff_le_normalizer
    ((splitRadical_le_unipotent 0 .suzuki).trans
      (splitUnipotent_le_splitSeed 0 .suzuki))).mpr
  apply (closure_le _).mpr
  rintro _ ⟨r, a, hr, rfl⟩
  have hc (t : CoefficientField 0) : splitRadical 0 .suzuki ≤
      (splitRadical 0 .suzuki).comap (MulAut.conj (rootGeneratorInGroup 0 r t)) := by
    apply (closure_le _).mpr
    rintro _ ⟨s, b, hs, rfl⟩
    exact hconj r s t b hr hs
  change rootGeneratorInGroup 0 r a ∈ normalizer (splitRadical 0 .suzuki)
  rw [mem_normalizer_iff]
  intro y
  constructor
  · exact fun hy => hc a hy
  · intro hy
    have he := hc (-a) hy
    change rootGeneratorInGroup 0 r (-a) *
      (rootGeneratorInGroup 0 r a * y * (rootGeneratorInGroup 0 r a)⁻¹) *
      (rootGeneratorInGroup 0 r (-a))⁻¹ ∈ splitRadical 0 .suzuki at he
    rw [← rootGenerator_inv] at he
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using he

/-- All non-radical positive root curves must be generated inside the signed
middle-node Levi; that precise subsystem calculation gives seed generation. -/
theorem splitSeed_eq_sup_of_subsystem_root_mem
    (hsub : ∀ (r : F4Chevalley.Root) (t : CoefficientField 0),
      typeF4RootPairing_base.IsPos r → ¬ IsRadicalRoot .suzuki r →
      rootGeneratorInGroup 0 r t ∈ splitLevi) :
    splitSeed 0 .suzuki = splitLevi ⊔ splitRadical 0 .suzuki := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro _ ⟨r, t, hr, rfl⟩
    rcases hr with hr | ⟨i, hi, rfl⟩
    · by_cases hR : IsRadicalRoot .suzuki r
      · exact mem_sup_right (subset_closure ⟨r, t, hR, rfl⟩)
      · exact mem_sup_left (hsub r t hr hR)
    · exact mem_sup_left (subset_closure ⟨_, t, ⟨i, hi, Or.inr rfl⟩, rfl⟩)
  · exact sup_le splitLevi_le_seed ((splitRadical_le_unipotent 0 .suzuki).trans
      (splitUnipotent_le_splitSeed 0 .suzuki))

/-- The two concrete root calculations supply existence of Levi–radical
factorization; matrix grading has already supplied its uniqueness. -/
theorem splitLeviInSeed_isComplement_of_root_calculations
    (hsub : ∀ (r : F4Chevalley.Root) (t : CoefficientField 0),
      typeF4RootPairing_base.IsPos r → ¬ IsRadicalRoot .suzuki r →
      rootGeneratorInGroup 0 r t ∈ splitLevi)
    (hconj : ∀ (r s : F4Chevalley.Root) (a b : CoefficientField 0),
      IsSeedRoot .suzuki r → IsRadicalRoot .suzuki s →
      rootGeneratorInGroup 0 r a * rootGeneratorInGroup 0 s b *
        (rootGeneratorInGroup 0 r a)⁻¹ ∈ splitRadical 0 .suzuki) :
    splitLeviInSeed.IsComplement' splitRadicalInSeed := by
  let := splitRadicalInSeed_normal_of_root_conjugation hconj
  have hsup : splitLeviInSeed ⊔ splitRadicalInSeed = ⊤ := by
    rw [splitLeviInSeed, splitRadicalInSeed, ← subgroupOf_sup splitLevi_le_seed
      ((splitRadical_le_unipotent 0 .suzuki).trans
        (splitUnipotent_le_splitSeed 0 .suzuki)),
      ← splitSeed_eq_sup_of_subsystem_root_mem hsub, subgroupOf_self]
  refine ⟨splitLeviRadical_mul_injective, ?_⟩
  intro x
  have hx : x ∈ splitLeviInSeed ⊔ splitRadicalInSeed := by rw [hsup]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_normal_right.mp hx
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩

/-- The positive-root radical is normal relative to the binary Suzuki split seed. -/
theorem splitRadicalInSeed_normal : splitRadicalInSeed.Normal :=
  splitRadicalInSeed_normal_of_root_conjugation rootGenerator_conj_radical

/-- The signed middle-node Levi and the positive-root radical generate the split seed. -/
theorem splitSeed_eq_sup : splitSeed 0 .suzuki = splitLevi ⊔ splitRadical 0 .suzuki :=
  splitSeed_eq_sup_of_subsystem_root_mem rootGenerator_mem_splitLevi_of_pos_not_radical

/-- Every element of the binary Suzuki split seed has a unique actual
Levi–radical product expression. -/
theorem splitLeviInSeed_isComplement :
    splitLeviInSeed.IsComplement' splitRadicalInSeed :=
  splitLeviInSeed_isComplement_of_root_calculations
    rootGenerator_mem_splitLevi_of_pos_not_radical rootGenerator_conj_radical

end ReeF4.Parabolics.BinarySuzuki
