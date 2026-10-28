module

public import Theory.GroupTheory.NoncentralChiefRefinement.ResidualRestriction
public import Theory.GroupAction.SubgroupQuotientIrreducible
public import Theory.GroupTheory.PResidual.FiniteImage
public import Mathlib.Algebra.Group.Subgroup.Actions

/-!
# Survival of binary chief sections in the two-residual

Let A < B be a noncentral binary chief interval of a finite group K. If R
is normal and K/R is a two-group, R acts nontrivially on B/A: otherwise the
full action factors through a two-group, whose nonidentity fixed points and
chief minimality make the whole section central. Since [R,B] lies in R ∩ B,
chief minimality then gives A(R ∩ B) = B. Thus the literal intersection map
is an isomorphism, and its conjugation equivariance preserves noncentrality.

Specializing to R = O²(K) supplies the section-survival premise of the chief
count comparison. Restricted sections need not be chief; the separate
refinement premise in the final application remains explicit.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
14.7.70, printed p.1074 (PDF p.1091), the comparison with the original L₁.
-/

public section

open Subgroup
namespace NoncentralChiefRefinement
variable {K : Type*} [Group K]

-- Chief minimality is irreducibility for the literal ambient conjugation action.
private theorem chief_section_irreducible (A B : NormalNode K) (hAB : A ⋖ B)
    (D : Subgroup (Section A B))
    (hD : ∀ k x, x ∈ D → sectionAction A B k x ∈ D) : D = ⊥ ∨ D = ⊤ := by
  apply quotient_conjugation_irreducible_of_maximal (⊤ : Subgroup K) B.val A.val
    hAB.le (by rw [normalizer_eq_top]) inferInstance ?_
    ((sectionAction A B).comp (⊤ : Subgroup K).subtype) (fun _ _ => rfl) D
    (fun k x hx => hD k x hx)
  intro L hAL hLB hnorm
  have hL : L.Normal := normalizer_eq_top_iff.mp (top_unique hnorm)
  obtain he | he := hAB.eq_or_eq (c := ⟨L, hL⟩) hAL hLB.le
  · exact congrArg Subtype.val he
  · exact (hLB.ne (congrArg Subtype.val he)).elim

-- A two-group action has a nonidentity fixed point on a nontrivial two-group.
private theorem chief_action_not_trivial [Finite K]
    (R : Subgroup K) [R.Normal] (hR : IsPGroup 2 (K ⧸ R))
    (A B : NormalNode K) (hAB : A ⋖ B) (h : IsNoncentralTwo A B) :
    ¬ (∀ r : R, ∀ x, sectionAction A B r x = x) := by
  intro hfix
  let f := sectionAction A B
  have hker : R ≤ f.rangeRestrict.ker := by
    intro r hr
    apply Subtype.ext
    apply MulEquiv.ext
    exact hfix ⟨r, hr⟩
  let q := QuotientGroup.lift R f.rangeRestrict hker
  have hp : IsPGroup 2 f.range := hR.of_surjective q
    (QuotientGroup.lift_surjective_of_surjective R f.rangeRestrict
      f.rangeRestrict_surjective hker)
  let : Nontrivial (Section A B) := not_subsingleton_iff_nontrivial.mp (by
    intro hs
    let := hs
    exact h.2 ((isCentral_iff_action A B).mpr (fun _ _ => Subsingleton.elim _ _)))
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdiv : 2 ∣ Nat.card (Section A B) := h.1.card_eq_or_dvd.resolve_left
    (Nat.ne_of_gt Finite.one_lt_card)
  obtain ⟨x, hx, hne⟩ := hp.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (α := Section A B) hdiv (a := 1) (by simp [MulAction.mem_fixedPoints])
  let D := FixedPoints.subgroup f.range (Section A B)
  have hinv : ∀ k y, y ∈ D → sectionAction A B k y ∈ D := by
    intro k y hy
    have he : sectionAction A B k y = y := hy (f.rangeRestrict k)
    rw [he]
    exact hy
  obtain hbot | htop := chief_section_irreducible A B hAB D hinv
  · have hxd : x ∈ D := hx
    rw [hbot, mem_bot] at hxd
    exact hne hxd.symm
  · apply h.2
    apply (isCentral_iff_action A B).mpr
    intro k y
    have hy : y ∈ D := by rw [htop]; exact mem_top _
    exact hy (f.rangeRestrict k)

open scoped commutatorElement

private theorem chief_sup_intersection [Finite K]
    (R : Subgroup K) [R.Normal] (hR : IsPGroup 2 (K ⧸ R))
    (A B : NormalNode K) (hAB : A ⋖ B) (h : IsNoncentralTwo A B) :
    A.val ⊔ (R ⊓ B.val) = B.val := by
  obtain hCA | hCB := ((covBy_iff_isChief A B).mp hAB).minimal
    (A.val ⊔ (R ⊓ B.val)) inferInstance le_sup_left (sup_le hAB.le inf_le_right)
  · exfalso
    apply chief_action_not_trivial R hR A B hAB h
    have hcomm : ⁅R, B.val⁆ ≤ A.val := by
      have hle : R ⊓ B.val ≤ A.val ⊔ (R ⊓ B.val) := le_sup_right
      rw [hCA] at hle
      exact (commutator_le_inf R B.val).trans hle
    intro r x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (A.val.subgroupOf B.val) x
    rw [sectionAction_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (r : K) * (b : K) * (r : K)⁻¹ / (b : K) ∈ A.val
    simpa only [commutatorElement_def, div_eq_mul_inv] using
      hcomm (commutator_mem_commutator r.property b.property)
  · exact hCB

/-- Every original chief-section class has a representative in the normal actor
when its quotient is a two-group and the section is noncentral binary. -/
theorem restrictionSectionMap_surjective_of_two_quotient [Finite K]
    (R : Subgroup K) [R.Normal] (hR : IsPGroup 2 (K ⧸ R))
    (A B : NormalNode K) (hAB : A ⋖ B) (h : IsNoncentralTwo A B) :
    Function.Surjective (restrictionSectionMap R A B) := by
  intro x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (A.val.subgroupOf B.val) x
  have hb : (b : K) ∈ A.val ⊔ (R ⊓ B.val) := by
    rw [chief_sup_intersection R hR A B hAB h]
    exact b.property
  obtain ⟨a, ha, c, hc, hac⟩ := mem_sup_of_normal_right.mp hb
  refine ⟨QuotientGroup.mk' _ ⟨⟨c, hc.1⟩, hc.2⟩, ?_⟩
  rw [restrictionSectionMap_mk]
  apply QuotientGroup.eq_iff_div_mem.mpr
  change c / (b : K) ∈ A.val
  rw [← hac]
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_inv_cancel_left] using A.val.inv_mem ha

/-- Restriction to a normal actor with two-group quotient preserves a
noncentral binary chief section, without asserting restricted chiefness. -/
theorem isNoncentralTwo_restrict_of_two_quotient [Finite K]
    (R : Subgroup K) [R.Normal] (hR : IsPGroup 2 (K ⧸ R))
    (A B : NormalNode K) (hAB : A ⋖ B) (h : IsNoncentralTwo A B) :
    IsNoncentralTwo (restrictNormalNode R A) (restrictNormalNode R B) := by
  refine ⟨restrictionSection_isPGroup R A B h.1, ?_⟩
  intro hc
  apply chief_action_not_trivial R hR A B hAB h
  intro r x
  obtain ⟨y, rfl⟩ := restrictionSectionMap_surjective_of_two_quotient R hR A B hAB h x
  rw [← restrictionSectionMap_equivariant,
    (isCentral_iff_action _ _).mp hc r y]

/-- The literal inclusion map of intersected sections is a genuine quotient
isomorphism. Its construction retains that map, including its equivariance. -/
noncomputable def restrictionSectionEquivOfTwoQuotient [Finite K]
    (R : Subgroup K) [R.Normal] (hR : IsPGroup 2 (K ⧸ R))
    (A B : NormalNode K) (hAB : A ⋖ B) (h : IsNoncentralTwo A B) :
    Section (restrictNormalNode R A) (restrictNormalNode R B) ≃* Section A B :=
  MulEquiv.ofBijective (restrictionSectionMap R A B)
    ⟨restrictionSectionMap_injective R A B,
      restrictionSectionMap_surjective_of_two_quotient R hR A B hAB h⟩

/-- The isomorphism is the existing restriction map on every quotient element. -/
@[simp] theorem restrictionSectionEquivOfTwoQuotient_apply [Finite K]
    (R : Subgroup K) [R.Normal] (hR : IsPGroup 2 (K ⧸ R))
    (A B : NormalNode K) (hAB : A ⋖ B) (h : IsNoncentralTwo A B)
    (x : Section (restrictNormalNode R A) (restrictNormalNode R B)) :
    restrictionSectionEquivOfTwoQuotient R hR A B hAB h x =
      restrictionSectionMap R A B x := by rfl

/-- Surjectivity for the actual two-residual, with its quotient hypothesis
supplied by the finite residual theorem. -/
theorem restrictionSectionMap_pResidual_surjective [Finite K]
    (A B : NormalNode K) (hAB : A ⋖ B) (h : IsNoncentralTwo A B) :
    Function.Surjective (restrictionSectionMap (pResidual 2 K) A B) :=
  restrictionSectionMap_surjective_of_two_quotient (pResidual 2 K)
    (isPGroup_quotient_pResidual 2) A B hAB h

/-- The exact local section-survival premise for restriction to the actual
two-residual. Only chiefness for the original actor is required. -/
theorem isNoncentralTwo_restrict_pResidual [Finite K]
    (A B : NormalNode K) (hAB : A ⋖ B) (h : IsNoncentralTwo A B) :
    IsNoncentralTwo (restrictNormalNode (pResidual 2 K) A)
      (restrictNormalNode (pResidual 2 K) B) :=
  isNoncentralTwo_restrict_of_two_quotient (pResidual 2 K)
    (isPGroup_quotient_pResidual 2) A B hAB h

/-- Application to the actual residual chief-count comparison: the local
section-survival premise is discharged. The independent noncentral-refinement
premise is retained for its producer and the final source assembly owner. -/
theorem ChiefSeries.exists_comparison_of_pResidual [Finite K]
    (s : ChiefSeries K) (h0 : s.head = ⊥) (h1 : s.last = ⊤)
    (hrefine : ∀ t : ChiefSeries (pResidual 2 K), IsNoncentralTwo t.head t.last →
      ∃ j : Fin t.length, IsNoncentralTwo (t j.castSucc) (t j.succ)) :
    ∃ (t : ChiefSeries (pResidual 2 K))
      (ι : Fin (s.length + 1) →o Fin (t.length + 1)),
      (∀ i, t (ι i) = restrictNormalNode (pResidual 2 K) (s i)) ∧
      ι 0 = 0 ∧ ι (Fin.last s.length) = Fin.last t.length ∧
      t.head = ⊥ ∧ t.last = ⊤ ∧ s.noncentralTwoCount ≤ t.noncentralTwoCount :=
  s.exists_comparison_of_restriction_survival (pResidual 2 K) h0 h1
    (fun i => isNoncentralTwo_restrict_pResidual _ _ (s.step i)) hrefine

end NoncentralChiefRefinement
