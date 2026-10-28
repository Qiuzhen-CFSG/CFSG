module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocal.ParabolicComparison
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Suzuki.Grading

/-!
# Retraction of the full Suzuki Ree parabolic onto its Levi

The two full-parabolic conventions agree as actual matrix subgroups. The
specified radical strictly raises the end-node grading, whereas the full
Levi, including its complementary torus, preserves each graded summand. Their
intersection is therefore trivial. The proved fixed radical–Levi factorization
then identifies the quotient by the radical with this actual full Levi.

The resulting retraction has exactly the root radical as kernel, hence a
two-group kernel. Identifying the full Levi with a Suzuki-times-torus subgroup
is a separate calculation; the smaller seed Levi is not used in its place.

Source: GLS3, Theorem 2.6.5(d,g), `refs/KGroup/GLS3/chapter2.tex`, and the
Suzuki local factor in Aschbacher–Smith F.1.12(I)(5), printed p.263.
-/

public noncomputable section

namespace ReeF4.ConverseParabolics

open Subgroup LargeLocalSeeds
open MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry
open SuzukiLevi (fullLevi)

/-- The root radicals in the two full-parabolic conventions are identical. -/
theorem suzuki_radical_eq_rootRadical (m : ℕ) :
    radical m .suzuki = Parabolics.radical m .suzuki := by
  ext x
  change x.val ∈ splitRadical m .suzuki ↔ toSplitGroup m x ∈ splitRadical m .suzuki
  rw [toSplitGroup_apply]

/-- Relative normality includes the complementary torus of the full parabolic. -/
theorem suzuki_parabolic_le_radical_normalizer (m : ℕ) :
    parabolic m .suzuki ≤ normalizer (radical m .suzuki : Set (Model m)) := by
  rw [parabolic_eq_rootParabolic, suzuki_radical_eq_rootRadical]
  exact SectionGeometry.LinearRadical.parabolic_le_radical_normalizer m .suzuki

/-- The specified Suzuki radical is normal inside its full parabolic. -/
theorem suzuki_intrinsicRadical_normal (m : ℕ) :
    (intrinsicRadical m .suzuki).Normal :=
  (normal_subgroupOf_iff_le_normalizer (radical_le_parabolic m .suzuki)).mpr
    (suzuki_parabolic_le_radical_normalizer m)

attribute [local instance] suzuki_intrinsicRadical_normal

/-- The full fixed middle-node Levi belongs to the full Suzuki parabolic. -/
theorem suzuki_fullLevi_le_parabolic (m : ℕ) : fullLevi m ≤ parabolic m .suzuki := by
  rw [parabolic_eq_rootParabolic]
  exact SuzukiLevi.fullLevi_le_parabolic m

/-- Strictly raising and degree-preserving matrices intersect only in identity. -/
theorem suzuki_radical_disjoint_fullLevi (m : ℕ) :
    Disjoint (radical m .suzuki) (fullLevi m) := by
  rw [suzuki_radical_eq_rootRadical]
  apply Subgroup.disjoint_def.mpr
  intro x hx hl
  have hr := SuzukiLevi.Grading.radical_raises x hx
  have hp := SuzukiLevi.Grading.fullLevi_preservesDegree x hl
  apply toSplitGroup_injective m
  rw [map_one]
  apply Subtype.ext
  apply Units.ext
  change SuzukiLevi.Grading.modelMatrix m x = 1
  apply sub_eq_zero.mp
  ext i j
  by_cases hij : SuzukiLevi.Grading.basisDegree i ≤
      SuzukiLevi.Grading.basisDegree j
  · exact hr i j hij
  · have hne : SuzukiLevi.Grading.basisDegree i ≠
        SuzukiLevi.Grading.basisDegree j := by omega
    have hij' : i ≠ j := fun he => hne (congrArg
      SuzukiLevi.Grading.basisDegree he)
    simp only [Matrix.sub_apply, hp i j hne, Matrix.one_apply_ne hij', sub_self,
      Matrix.zero_apply]

/-- Inclusion of the full Levi, retaining its complementary torus. -/
def suzukiFullLeviInclusion (m : ℕ) : fullLevi m →* parabolic m .suzuki :=
  inclusion (suzuki_fullLevi_le_parabolic m)

private def fullLeviToQuotient (m : ℕ) :
    fullLevi m →* parabolic m .suzuki ⧸ intrinsicRadical m .suzuki :=
  (QuotientGroup.mk' (intrinsicRadical m .suzuki)).comp (suzukiFullLeviInclusion m)

private theorem fullLeviToQuotient_bijective (m : ℕ) :
    Function.Bijective (fullLeviToQuotient m) := by
  constructor
  · apply (injective_iff_map_eq_one (fullLeviToQuotient m)).mpr
    intro l hl
    have hr : l.val ∈ radical m .suzuki :=
      (QuotientGroup.eq_one_iff (suzukiFullLeviInclusion m l)).mp hl
    exact Subtype.ext (Subgroup.disjoint_def.mp
      (suzuki_radical_disjoint_fullLevi m) hr l.property)
  · intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (intrinsicRadical m .suzuki) q
    obtain ⟨r, hr, l, hl, he⟩ :=
      SuzukiLevi.exists_radical_fullLevi_factors m x.val
        (by simpa only [parabolic_eq_rootParabolic] using x.property)
    have hr' : r ∈ radical m .suzuki := by rwa [suzuki_radical_eq_rootRadical]
    let rP : parabolic m .suzuki := ⟨r, radical_le_parabolic m .suzuki hr'⟩
    refine ⟨⟨l, hl⟩, ?_⟩
    have he' : rP * suzukiFullLeviInclusion m ⟨l, hl⟩ = x := Subtype.ext he
    change QuotientGroup.mk' (intrinsicRadical m .suzuki)
      (suzukiFullLeviInclusion m ⟨l, hl⟩) = _
    have hq : QuotientGroup.mk' (intrinsicRadical m .suzuki) rP = 1 :=
      (QuotientGroup.eq_one_iff rP).mpr (show rP ∈ intrinsicRadical m .suzuki from hr')
    rw [← he', map_mul, hq, one_mul]

/-- The radical quotient is the actual full fixed Levi. -/
def suzukiFullLeviQuotientEquiv (m : ℕ) :
    fullLevi m ≃* parabolic m .suzuki ⧸ intrinsicRadical m .suzuki :=
  MulEquiv.ofBijective (fullLeviToQuotient m) (fullLeviToQuotient_bijective m)

/-- Retraction onto the full Levi, constructed from the fixed matrix factorization. -/
def suzukiLeviRetraction (m : ℕ) : parabolic m .suzuki →* fullLevi m :=
  (suzukiFullLeviQuotientEquiv m).symm.toMonoidHom.comp
    (QuotientGroup.mk' (intrinsicRadical m .suzuki))

/-- The retraction fixes every element of the full Levi. -/
@[simp] theorem suzukiLeviRetraction_inclusion (m : ℕ) (l : fullLevi m) :
    suzukiLeviRetraction m (suzukiFullLeviInclusion m l) = l :=
  (suzukiFullLeviQuotientEquiv m).symm_apply_apply l

theorem suzukiLeviRetraction_surjective (m : ℕ) :
    Function.Surjective (suzukiLeviRetraction m) :=
  fun l => ⟨suzukiFullLeviInclusion m l, suzukiLeviRetraction_inclusion m l⟩

/-- Its kernel is precisely the specified root radical, not just a two-subgroup. -/
theorem suzukiLeviRetraction_ker (m : ℕ) :
    (suzukiLeviRetraction m).ker = intrinsicRadical m .suzuki := by
  unfold suzukiLeviRetraction
  rw [MonoidHom.ker_comp_of_injective _ _ (suzukiFullLeviQuotientEquiv m).symm.injective,
    QuotientGroup.ker_mk']

theorem suzukiLeviRetraction_ker_isPGroup (m : ℕ) :
    IsPGroup 2 (suzukiLeviRetraction m).ker := by
  rw [suzukiLeviRetraction_ker]
  exact intrinsicRadical_isPGroup m .suzuki

end ReeF4.ConverseParabolics
