module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.FieldActors.FixedSpaces
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.FieldActors.Centralizer
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.SmallFields

/-!
# Displacement estimates for outer natural SL₃ actors

The genuine coefficient action gives displacement 3s for an outer involution.
For a larger elementary subgroup, its nontrivial linear kernel and a moved
scalar bound the common fixed dimension by 2s, hence displacement below by 4s.
The literal centralizer has two-rank 2s+1, with an actual elementary subgroup
attaining the bound. Thus every outer elementary actor has displacement
strictly greater than its rank.

The source parameter reduction places every remaining outer actor in this
even-degree SL₃ branch. Applying the completed estimate to the natural-module
assembly gives quadratic ratio 1/2, containment of best offenders in L, and
generation of L by best offenders, including the literal B.4.2(3) conclusion.
Recognition remains an earlier input, and assembly across all natural cases
belongs to the natural-module source owner.

Source: Aschbacher–Smith, K.3.2.1, printed pp.454–455 (1 March 2004).
-/

public section

open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterK.Linear.Natural.FieldActors
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G) (F : BinaryField)

omit [Finite G] in
/-- An outer element of an elementary two-group is an involution. -/
lemma outer_element_orderOf {A : Subgroup G} (hA : IsElementaryAbelian 2 A)
    (a : A) (haL : (a : G) ∉ L) : orderOf (a : G) = 2 :=
  orderOf_eq_prime (elementary_square_one hA a) (fun he => haL (he ▸ L.one_mem))

/-- In rank one the elementary actor is precisely its outer involution's
cyclic subgroup, so its displacement is exactly 3s. -/
theorem outer_rank_one_fixedCodim
    (e : ActionEquiv (ρ.comp L.subtype) (linearNatural F 3))
    (hf : Function.Injective ρ) (hs : IsSemilinearExtension ρ L F 3 e)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hr : rank A = 1)
    (a : A) (haL : (a : G) ∉ L) (s : ℕ) (hdegree : F.degree = 2 * s) :
    fixedCodim ρ A = 3 * s := by
  have ha := outer_element_orderOf L hA.2 a haL
  have he : Subgroup.zpowers (a : G) = A := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr a.property)
    rw [Nat.card_zpowers, ha, hA.card_eq_two_pow_rank, hr, pow_one]
  rw [← he]
  exact outer_involution_fixedCodim ρ L F e hf hs a ha haL s hdegree

/-- Every rank-one outer elementary actor is excluded from the offender
inequality, without any centralizer-rank premise. -/
theorem outer_rank_one_bound
    (e : ActionEquiv (ρ.comp L.subtype) (linearNatural F 3))
    (hf : Function.Injective ρ) (hs : IsSemilinearExtension ρ L F 3 e)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hr : rank A = 1)
    (hAL : ¬ A ≤ L) (s : ℕ) (hspos : 0 < s) (hdegree : F.degree = 2 * s) :
    rank A < fixedCodim ρ A := by
  obtain ⟨a, haA, haL⟩ := Set.not_subset.mp hAL
  rw [outer_rank_one_fixedCodim ρ L F e hf hs hA hr ⟨a, haA⟩ haL s hdegree, hr]
  omega

/-- Source application of the parameter reduction and both fixed-space
calculations on the original representation. -/
theorem source_outer_displacement_cases [FiniteDimensional (ZMod 2) V]
    {K : GroupClass} (h : SourceInput ρ L F 3 K)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hAL : ¬ A ≤ L) :
    ∃ s : ℕ, 0 < s ∧ F.degree = 2 * s ∧
      ((rank A = 1 ∧ fixedCodim ρ A = 3 * s ∧ rank A < fixedCodim ρ A) ∨
       (1 < rank A ∧ Module.finrank (ZMod 2) (fixedSpace ρ A) ≤ 2 * s ∧
        4 * s ≤ fixedCodim ρ A)) := by
  obtain ⟨_, s, hspos, hdegree⟩ := outside_elementary_parameters ρ L F 3 h hA hAL
  obtain ⟨a, haA, haL⟩ := Set.not_subset.mp hAL
  refine ⟨s, hspos, hdegree, ?_⟩
  by_cases hr : rank A = 1
  · exact Or.inl ⟨hr,
      outer_rank_one_fixedCodim ρ L F h.natural h.faithful h.semilinear hA hr
        ⟨a, haA⟩ haL s hdegree,
      outer_rank_one_bound ρ L F h.natural h.faithful h.semilinear hA hr hAL s hspos hdegree⟩
  · have hr' : 1 < rank A := by have := hA.rank_pos; omega
    exact Or.inr ⟨hr',
      outer_elementary_fixedSpace_finrank ρ L F h.natural h.faithful h.semilinear hA hr'
        ⟨a, haA⟩ haL s hdegree,
      source_outer_elementary_fixedCodim ρ L F h hA hr' ⟨a, haA⟩ haL s hdegree⟩

/-- Every outer elementary actor has displacement strictly greater than rank.
In rank one the displacement is 3s. Otherwise the literal centralizer bounds
its rank by 2s+1, while its displacement is at least 4s. -/
theorem outer_elementary_bound [FiniteDimensional (ZMod 2) V]
    (e : ActionEquiv (ρ.comp L.subtype) (linearNatural F 3))
    (hf : Function.Injective ρ) (hs : IsSemilinearExtension ρ L F 3 e)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hAL : ¬ A ≤ L)
    (s : ℕ) (hspos : 0 < s) (hdegree : F.degree = 2 * s) :
    rank A < fixedCodim ρ A := by
  by_cases hr : rank A = 1
  · exact outer_rank_one_bound ρ L F e hf hs hA hr hAL s hspos hdegree
  · obtain ⟨a, haA, haL⟩ := Set.not_subset.mp hAL
    have hr' : 1 < rank A := by have := hA.rank_pos; omega
    have ha := outer_element_orderOf L hA.2 ⟨a, haA⟩ haL
    have hbound := Centralizer.elementary_rank_le ρ L F e hf hs
      a ha haL s hspos hdegree A hA.2 haA
    have hcodim := outer_elementary_fixedCodim ρ L F e hf hs
      hA hr' ⟨a, haA⟩ haL s hdegree
    omega

/-- The outer-actor premise of the natural source assembly, with the even
field degree derived from the source input and the actor's noncontainment. -/
theorem source_outer_actor_bound [FiniteDimensional (ZMod 2) V]
    {K : GroupClass} (h : SourceInput ρ L F 3 K)
    (A : Subgroup G) (hA : IsElementaryTwo A) (hAL : ¬ A ≤ L) :
    rank A < fixedCodim ρ A := by
  obtain ⟨_, s, hspos, hdegree⟩ := outside_elementary_parameters ρ L F 3 h hA hAL
  exact outer_elementary_bound ρ L F h.natural h.faithful h.semilinear
    hA hAL s hspos hdegree

/-- The even-degree natural SL₃ branch of K.3.2.1. The outer-actor premise
of `conclusions_of_outer_actor_bound` is discharged, giving the exact ratio,
best-offender containment and generation, and the literal B.4.2(3) clause. -/
theorem source_linearThree_of_even_degree [FiniteDimensional (ZMod 2) V]
    {K : GroupClass} (h : SourceInput ρ L F 3 K)
    (s : ℕ) (hspos : 0 < s) (hdegree : F.degree = 2 * s) :
    quadraticRatio ρ = 1 / 2 ∧ (∀ A, IsBestOffender ρ A → A ≤ L) ∧
      offenderSubgroup ρ = L ∧
      ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  have houter : ∀ A : Subgroup G, IsElementaryTwo A → ¬ A ≤ L →
      rank A < fixedCodim ρ A := by
    intro A hA hAL
    exact outer_elementary_bound ρ L F h.natural h.faithful h.semilinear
      hA hAL s hspos hdegree
  obtain ⟨hq, hb, hg⟩ := conclusions_of_outer_actor_bound ρ L F 3 h.natural (by decide) houter
  exact ⟨by simpa using hq, hb, hg,
    linearThree_of_outer_actor_bound ρ L F h.natural houter⟩

end CFSG.Quasithin.ChapterK.Linear.Natural.FieldActors
