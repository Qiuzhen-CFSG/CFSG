module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocal.ParabolicComparison
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.LinearRadical.LeviDetection.Grading

/-!+# Retraction of the full linear Ree parabolic onto its Levi

The two full-parabolic conventions agree as actual matrix subgroups. The
specified radical strictly raises the middle-node grading, whereas the full
Levi, including its complementary torus, preserves each graded summand. Their
intersection is therefore trivial. The proved fixed radical–Levi factorization
then identifies the quotient by the radical with this actual full Levi.

The resulting retraction has exactly the root radical as kernel, hence a
two-group kernel. Identifying the full Levi with an SL₂-times-torus subgroup
is a separate calculation; the smaller seed Levi is not used in its place.

Source: GLS3, Theorem 2.6.5(d,g), `refs/KGroup/GLS3/chapter2.tex`, and the
linear local factor in Aschbacher–Smith F.1.12(I)(5), printed p.263.
-/

public noncomputable section

namespace ReeF4.ConverseParabolics

open Subgroup LargeLocalSeeds
open MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry
open SectionGeometry.LinearRadical (fullLevi)

/-- The root radicals in the two full-parabolic conventions are identical. -/
theorem radical_eq_rootRadical (m : ℕ) (s : Side) :
    radical m s = Parabolics.radical m s := by
  ext x
  change x.val ∈ splitRadical m s ↔ toSplitGroup m x ∈ splitRadical m s
  rw [toSplitGroup_apply]

/-- Relative normality includes the complementary torus of the full parabolic. -/
theorem linear_parabolic_le_radical_normalizer (m : ℕ) :
    parabolic m .linear ≤ normalizer (radical m .linear : Set (Model m)) := by
  rw [parabolic_eq_rootParabolic, radical_eq_rootRadical]
  exact SectionGeometry.LinearRadical.parabolic_le_radical_normalizer m .linear

/-- The specified linear radical is normal inside its full parabolic. -/
theorem linear_intrinsicRadical_normal (m : ℕ) :
    (intrinsicRadical m .linear).Normal :=
  (normal_subgroupOf_iff_le_normalizer (radical_le_parabolic m .linear)).mpr
    (linear_parabolic_le_radical_normalizer m)

attribute [local instance] linear_intrinsicRadical_normal

/-- The full fixed end-node Levi belongs to the full linear parabolic. -/
theorem linear_fullLevi_le_parabolic (m : ℕ) : fullLevi m ≤ parabolic m .linear := by
  rw [parabolic_eq_rootParabolic]
  exact SectionGeometry.LinearRadical.fullLevi_le_parabolic m

/-- Strictly raising and degree-preserving matrices intersect only in identity. -/
theorem linear_radical_disjoint_fullLevi (m : ℕ) :
    Disjoint (radical m .linear) (fullLevi m) := by
  rw [radical_eq_rootRadical]
  apply Subgroup.disjoint_def.mpr
  intro x hx hl
  have hr := SectionGeometry.LinearRadical.LeviDetection.radical_raises x hx
  have hp := SectionGeometry.LinearRadical.LeviDetection.fullLevi_preservesDegree x hl
  apply toSplitGroup_injective m
  rw [map_one]
  apply Subtype.ext
  apply Units.ext
  change SectionGeometry.LinearRadical.LeviDetection.modelMatrix m x = 1
  apply sub_eq_zero.mp
  ext i j
  by_cases hij : SectionGeometry.LinearRadical.LeviDetection.basisDegree i ≤
      SectionGeometry.LinearRadical.LeviDetection.basisDegree j
  · exact hr i j hij
  · have hne : SectionGeometry.LinearRadical.LeviDetection.basisDegree i ≠
        SectionGeometry.LinearRadical.LeviDetection.basisDegree j := by omega
    have hij' : i ≠ j := fun he => hne (congrArg
      SectionGeometry.LinearRadical.LeviDetection.basisDegree he)
    simp only [Matrix.sub_apply, hp i j hne, Matrix.one_apply_ne hij', sub_self,
      Matrix.zero_apply]

/-- Inclusion of the full Levi, retaining its complementary torus. -/
def linearFullLeviInclusion (m : ℕ) : fullLevi m →* parabolic m .linear :=
  inclusion (linear_fullLevi_le_parabolic m)

private def fullLeviToQuotient (m : ℕ) :
    fullLevi m →* parabolic m .linear ⧸ intrinsicRadical m .linear :=
  (QuotientGroup.mk' (intrinsicRadical m .linear)).comp (linearFullLeviInclusion m)

private theorem fullLeviToQuotient_bijective (m : ℕ) :
    Function.Bijective (fullLeviToQuotient m) := by
  constructor
  · apply (injective_iff_map_eq_one (fullLeviToQuotient m)).mpr
    intro l hl
    have hr : l.val ∈ radical m .linear :=
      (QuotientGroup.eq_one_iff (linearFullLeviInclusion m l)).mp hl
    exact Subtype.ext (Subgroup.disjoint_def.mp
      (linear_radical_disjoint_fullLevi m) hr l.property)
  · intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (intrinsicRadical m .linear) q
    obtain ⟨r, hr, l, hl, he⟩ :=
      SectionGeometry.LinearRadical.exists_radical_fullLevi_factors m x.val
        (by simpa only [parabolic_eq_rootParabolic] using x.property)
    have hr' : r ∈ radical m .linear := by rwa [radical_eq_rootRadical]
    let rP : parabolic m .linear := ⟨r, radical_le_parabolic m .linear hr'⟩
    refine ⟨⟨l, hl⟩, ?_⟩
    have he' : rP * linearFullLeviInclusion m ⟨l, hl⟩ = x := Subtype.ext he
    change QuotientGroup.mk' (intrinsicRadical m .linear)
      (linearFullLeviInclusion m ⟨l, hl⟩) = _
    have hq : QuotientGroup.mk' (intrinsicRadical m .linear) rP = 1 :=
      (QuotientGroup.eq_one_iff rP).mpr (show rP ∈ intrinsicRadical m .linear from hr')
    rw [← he', map_mul, hq, one_mul]

/-- The radical quotient is the actual full fixed Levi. -/
def linearFullLeviQuotientEquiv (m : ℕ) :
    fullLevi m ≃* parabolic m .linear ⧸ intrinsicRadical m .linear :=
  MulEquiv.ofBijective (fullLeviToQuotient m) (fullLeviToQuotient_bijective m)

/-- Retraction onto the full Levi, constructed from the fixed matrix factorization. -/
def linearLeviRetraction (m : ℕ) : parabolic m .linear →* fullLevi m :=
  (linearFullLeviQuotientEquiv m).symm.toMonoidHom.comp
    (QuotientGroup.mk' (intrinsicRadical m .linear))

/-- The retraction fixes every element of the full Levi. -/
@[simp] theorem linearLeviRetraction_inclusion (m : ℕ) (l : fullLevi m) :
    linearLeviRetraction m (linearFullLeviInclusion m l) = l :=
  (linearFullLeviQuotientEquiv m).symm_apply_apply l

theorem linearLeviRetraction_surjective (m : ℕ) :
    Function.Surjective (linearLeviRetraction m) :=
  fun l => ⟨linearFullLeviInclusion m l, linearLeviRetraction_inclusion m l⟩

/-- Its kernel is precisely the specified root radical, not just a two-subgroup. -/
theorem linearLeviRetraction_ker (m : ℕ) :
    (linearLeviRetraction m).ker = intrinsicRadical m .linear := by
  unfold linearLeviRetraction
  rw [MonoidHom.ker_comp_of_injective _ _ (linearFullLeviQuotientEquiv m).symm.injective,
    QuotientGroup.ker_mk']

theorem linearLeviRetraction_ker_isPGroup (m : ℕ) :
    IsPGroup 2 (linearLeviRetraction m).ker := by
  rw [linearLeviRetraction_ker]
  exact intrinsicRadical_isPGroup m .linear

end ReeF4.ConverseParabolics
