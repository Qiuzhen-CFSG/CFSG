module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.FieldActors

/-!
# The recognized natural branch of K.3.2.1

The hyperplane pointwise centralizer attains the quadratic ratio `1/(n-1)`.
Every outer elementary actor forces `n=3` and field degree `2s>0`. The
coefficient involution displaces `3s` dimensions; its literal centralizer has
two-rank `2s+1`, while a larger elementary actor displaces at least `4s`.
Consequently all offenders lie in L, and the inner displacement bound becomes
the global quadratic lower bound. The transported hyperplane offenders
generate L, giving the precise linearThree or binaryLinear Chapter B clause.

Only the earlier natural-module recognition and its semilinear scalar equation
remain inputs. They are owned by qt-k03-linear-recognition and discharged in
the full K.3.2 assembly by qt-k03-linear-modules. No actor estimate, ratio, or
offender-generation assertion is a premise of these theorems.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.3.2.1,
printed pp.454–455/PDF pp.465–466.
-/

public section

open Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped ENNReal

namespace CFSG.Quasithin.ChapterK.Linear.Natural

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G) (F : BinaryField) (n : ℕ)

/-- The outer-actor premise of the natural assembly is discharged in every
source parameter range, including even field degree. -/
theorem source_outer_actor_bound {K : GroupClass} (h : SourceInput ρ L F n K)
    (A : Subgroup G) (hA : IsElementaryTwo A) (hAL : ¬ A ≤ L) :
    rank A < fixedCodim ρ A := by
  obtain ⟨hn, s, hspos, hdegree⟩ := outside_elementary_parameters ρ L F n h hA hAL
  subst n
  exact FieldActors.outer_elementary_bound ρ L F h.natural h.faithful h.semilinear
    hA hAL s hspos hdegree

/-- Field involutions exclude every outer offender, hence in particular every
outer best offender. -/
theorem source_offender_le {K : GroupClass} (h : SourceInput ρ L F n K)
    {A : Subgroup G} (hA : IsOffender ρ A) : A ≤ L := by
  by_contra hAL
  exact Nat.not_lt_of_ge hA.2 (source_outer_actor_bound ρ L F n h A hA.1 hAL)

/-- K.3.2.1 for the actual recognized natural representation. The global
ratio, containment and generation are conclusions, and the final conjunct
instantiates B.4.2(3) or B.4.2(9) with that same intertwiner. -/
theorem source_natural {K : GroupClass} (h : SourceInput ρ L F n K) :
    quadraticRatio ρ = 1 / (n - 1 : ℕ) ∧
    (∀ A, IsBestOffender ρ A → A ≤ L) ∧ offenderSubgroup ρ = L ∧
    ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase
      ρ L (offenderSubgroup ρ) := by
  have hn : 2 ≤ n := by
    rcases h.dimensions with hn | ⟨hn | hn, _⟩ <;> omega
  obtain ⟨hq, hb, hg⟩ := conclusions_of_outer_actor_bound ρ L F n h.natural hn
    (source_outer_actor_bound ρ L F n h)
  refine ⟨hq, hb, hg, ?_⟩
  rcases h.dimensions with rfl | ⟨hd, hF⟩
  · exact .linearThree F hg h.natural (by simpa using hq)
  · exact .binaryLinear n hd hg (primeFieldActionEquiv ρ L F hF n h.natural) hq

/-- The sharp global lower bound, on every actual quadratic elementary actor
of G, without a containment or outer-actor hypothesis. -/
theorem source_quadratic_lower_bound {K : GroupClass} (h : SourceInput ρ L F n K)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hquad : IsQuadratic ρ A) :
    1 / (n - 1 : ℕ) ≤ actionRatio ρ A := by
  rw [← (source_natural ρ L F n h).1]
  exact iInf_le_of_le A (iInf_le_of_le ⟨hA, hquad⟩ le_rfl)

/-- The literal pointwise centralizer of the transported F-hyperplane is a
quadratic best offender attaining the global minimum. -/
theorem source_hyperplane_minimizer {K : GroupClass} (h : SourceInput ρ L F n K)
    (j : Fin n) :
    rank (markedCentralizer ρ L F n h.natural j) = F.degree * (n - 1) ∧
    fixedCodim ρ (markedCentralizer ρ L F n h.natural j) = F.degree ∧
    IsQuadratic ρ (markedCentralizer ρ L F n h.natural j) ∧
    IsBestOffender ρ (markedCentralizer ρ L F n h.natural j) ∧
    actionRatio ρ (markedCentralizer ρ L F n h.natural j) = quadraticRatio ρ := by
  have hn : 2 ≤ n := by
    rcases h.dimensions with hn | ⟨hn | hn, _⟩ <;> omega
  obtain ⟨hr, hc, hq, hb⟩ := markedCentralizer_calculation ρ L F n h.natural hn j
  refine ⟨hr, hc, hq, hb, ?_⟩
  rw [(source_natural ρ L F n h).1, actionRatio, hr, hc, Nat.cast_mul]
  have hf : (F.degree : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.ne_of_gt F.degree_pos
  simpa only [mul_one] using
    (ENNReal.mul_div_mul_left (1 : ℝ≥0∞) ((n - 1 : ℕ) : ℝ≥0∞) hf (by simp))

omit [FiniteDimensional (ZMod 2) V] in
/-- Every actual outer involution forces the even-degree SL₃ branch. Its
coefficient automorphism has order two, its fixed codimension is `3s`, and its
literal ambient centralizer has two-rank exactly `2s+1`. -/
theorem source_outer_involution_estimates {K : GroupClass} (h : SourceInput ρ L F n K)
    (a : G) (ha : orderOf a = 2) (haL : a ∉ L) :
    n = 3 ∧ ∃ s : ℕ, 0 < s ∧ F.degree = 2 * s ∧
      fixedCodim ρ (Subgroup.zpowers a) = 3 * s ∧
      primeRank 2 (Subgroup.centralizer ({a} : Set G)) = 2 * s + 1 ∧
      ∃ σ : F.Carrier ≃+* F.Carrier, orderOf σ = 2 ∧
        ∀ (c : F.Carrier) (v : V),
          h.natural.linearEquiv
              (ρ a (h.natural.linearEquiv.symm (c • h.natural.linearEquiv v))) =
            σ c • h.natural.linearEquiv (ρ a v) := by
  have hA : IsElementaryTwo (Subgroup.zpowers a) := by
    refine ⟨?_, IsElementaryAbelian.zpowers_of_pow_eq_one (ha ▸ pow_orderOf_eq_one a)⟩
    intro hb
    have he : a = 1 := by simpa only [hb, Subgroup.mem_bot] using Subgroup.mem_zpowers a
    exact haL (he ▸ L.one_mem)
  have hAL : ¬ Subgroup.zpowers a ≤ L := fun he => haL (he (Subgroup.mem_zpowers a))
  obtain ⟨hn, s, hspos, hdegree⟩ := outside_elementary_parameters ρ L F n h hA hAL
  subst n
  refine ⟨rfl, s, hspos, hdegree,
    FieldActors.source_outer_involution_fixedCodim ρ L F h a ha haL s hdegree,
    FieldActors.Centralizer.source_primeRank_centralizer_eq
      ρ L F h a ha haL s hspos hdegree,
    FieldActors.coefficientAction ρ L F h.natural h.semilinear a,
    FieldActors.outer_coefficient_orderOf ρ L F h.natural h.faithful h.semilinear a ha haL,
    ?_⟩
  intro c v
  simpa only [FieldActors.coordinateAction_apply, h.natural.linearEquiv.symm_apply_apply] using
    FieldActors.coefficientAction_smul ρ L F h.natural h.semilinear
      a c (h.natural.linearEquiv v)

/-- The source common-fixed-space and centralizer estimates apply to every
outer elementary actor of rank greater than one on the original module. -/
theorem source_outer_elementary_estimates {K : GroupClass} (h : SourceInput ρ L F n K)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hAL : ¬ A ≤ L) (hr : 1 < rank A) :
    n = 3 ∧ ∃ s : ℕ, 0 < s ∧ F.degree = 2 * s ∧ rank A ≤ 2 * s + 1 ∧
      Module.finrank (ZMod 2) (fixedSpace ρ A) ≤ 2 * s ∧
      4 * s ≤ fixedCodim ρ A ∧ rank A < fixedCodim ρ A := by
  obtain ⟨hn, s, hspos, hdegree⟩ := outside_elementary_parameters ρ L F n h hA hAL
  subst n
  obtain ⟨a, haA, haL⟩ := Set.not_subset.mp hAL
  have ha := FieldActors.outer_element_orderOf L hA.2 ⟨a, haA⟩ haL
  exact ⟨rfl, s, hspos, hdegree,
    FieldActors.Centralizer.elementary_rank_le ρ L F h.natural h.faithful h.semilinear
      a ha haL s hspos hdegree A hA.2 haA,
    FieldActors.outer_elementary_fixedSpace_finrank ρ L F h.natural h.faithful h.semilinear
      hA hr ⟨a, haA⟩ haL s hdegree,
    FieldActors.source_outer_elementary_fixedCodim ρ L F h hA hr ⟨a, haA⟩ haL s hdegree,
    source_outer_actor_bound ρ L F 3 h A hA hAL⟩

end CFSG.Quasithin.ChapterK.Linear.Natural
