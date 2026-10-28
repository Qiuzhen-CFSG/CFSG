module
public import Theory.Representation.BinaryOffender.CubicSection
public import Theory.Representation.BinaryOffender.ActionImage
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.Representation.BinaryOffender.FaithfulInvariantSection

/-!
# Cubic budgets for two invariant sections

Fixed codimensions on an invariant submodule and its quotient add to at most
that of the whole module. Their cubic ratios therefore give an additive lower
bound for the whole ratio. In the faithful-image formulation, two sections
with no FF offender each use more than the rank of the same elementary actor.
The component-centralizer criterion supplies faithfulness on those sections.

Source: Aschbacher--Smith D.3.9(1), printed pp.199--200. These are numerical
and faithfulness lemmas; construction of a local chief filtration remains a
separate source argument.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- The two literal sections together use at least the sum of their cubic ratios. -/
theorem section_cubicRatio_add_le :
    ∀ U : Subrepresentation ρ,
    cubicRatio U.toRepresentation + cubicRatio U.quotientRepresentation ≤ cubicRatio ρ := by
  intro U
  apply le_iInf
  intro A
  apply le_iInf
  rintro ⟨hA, hc⟩
  have hs : cubicRatio U.toRepresentation ≤ actionRatio U.toRepresentation A :=
    iInf_le_of_le A (iInf_le_of_le ⟨hA, cubic_subrepresentation ρ U hc⟩ le_rfl)
  have hq : cubicRatio U.quotientRepresentation ≤ actionRatio U.quotientRepresentation A :=
    iInf_le_of_le A (iInf_le_of_le ⟨hA, cubic_quotient ρ U hc⟩ le_rfl)
  apply (add_le_add hs hq).trans
  have hb := fixedCodim_quotient_add_subrepresentation_le ρ U A
  unfold actionRatio
  rw [← ENNReal.add_div]
  apply ENNReal.div_le_div_right
  exact_mod_cast (by omega : fixedCodim U.toRepresentation A +
    fixedCodim U.quotientRepresentation A ≤ fixedCodim ρ A)

/-- Two sections both above the FF threshold cannot fit a cubic ratio at most two. -/
theorem not_cubicRatio_le_two_of_section_ratios
    (U : Subrepresentation ρ)
    (hU : 1 < cubicRatio U.toRepresentation)
    (hQ : 1 < cubicRatio U.quotientRepresentation) :
    ¬ cubicRatio ρ ≤ 2 := by
  intro h
  have hs := (section_cubicRatio_add_le ρ U).trans h
  have ht : (2 : ENNReal) < cubicRatio U.toRepresentation + cubicRatio U.quotientRepresentation := by
    calc
      (2 : ENNReal) = 1 + 1 := by norm_num
      _ < _ := ENNReal.add_lt_add hU hQ
  exact (not_lt_of_ge hs) ht

omit [FiniteDimensional (ZMod 2) V] in
/-- Passing to a faithful image preserves the rank of the specified actor,
so absence of FF offenders forces strict fixed-codimension growth. -/
theorem rank_lt_fixedCodim_of_nonFF_image
    {A : Subgroup G} (hA : IsElementaryTwo A)
    (hfaith : ∀ a ∈ A, (∀ v, ρ a v = v) → a = 1)
    (hno : ¬ IsFFModule (imageRepresentation ρ)) :
    rank A < fixedCodim ρ A := by
  apply lt_of_not_ge
  intro hc
  apply hno
  refine ⟨actionSubgroup ρ A, hA.actionSubgroup ρ hfaith, ?_⟩
  rw [fixedCodim_actionSubgroup, actionSubgroup_rank ρ A hfaith]
  exact hc

/-- Faithful non-FF images on both literal sections force a strict two-rank bound. -/
theorem twice_rank_lt_fixedCodim_of_nonFF_sections
    (U : Subrepresentation ρ) {A : Subgroup G} (hA : IsElementaryTwo A)
    (hU : ∀ a ∈ A, (∀ v, U.toRepresentation a v = v) → a = 1)
    (hQ : ∀ a ∈ A, (∀ v, U.quotientRepresentation a v = v) → a = 1)
    (hnU : ¬ IsFFModule (imageRepresentation U.toRepresentation))
    (hnQ : ¬ IsFFModule (imageRepresentation U.quotientRepresentation)) :
    2 * rank A < fixedCodim ρ A := by
  have hu := rank_lt_fixedCodim_of_nonFF_image U.toRepresentation hA hU hnU
  have hq := rank_lt_fixedCodim_of_nonFF_image U.quotientRepresentation hA hQ hnQ
  have hs := fixedCodim_quotient_add_subrepresentation_le ρ U A
  omega

/-- It suffices to find a second non-FF section inside the quotient;
the rest of that quotient may have a different action kernel. -/
theorem twice_rank_lt_fixedCodim_of_nonFF_submodule_sections
    (U : Subrepresentation ρ) (W : Subrepresentation U.quotientRepresentation)
    {A : Subgroup G} (hA : IsElementaryTwo A)
    (hU : ∀ a ∈ A, (∀ v, U.toRepresentation a v = v) → a = 1)
    (hW : ∀ a ∈ A, (∀ v, W.toRepresentation a v = v) → a = 1)
    (hnU : ¬ IsFFModule (imageRepresentation U.toRepresentation))
    (hnW : ¬ IsFFModule (imageRepresentation W.toRepresentation)) :
    2 * rank A < fixedCodim ρ A := by
  have hu := rank_lt_fixedCodim_of_nonFF_image U.toRepresentation hA hU hnU
  have hw := rank_lt_fixedCodim_of_nonFF_image W.toRepresentation hA hW hnW
  have hqw := fixedCodim_subrepresentation_le U.quotientRepresentation W A
  have hs := fixedCodim_quotient_add_subrepresentation_le ρ U A
  omega

/-- Faithfulness on a normal component group supplies section faithfulness
for every actor whose intersection with its centralizer is trivial. -/
theorem twice_rank_lt_fixedCodim_of_component_faithful_nonFF_sections
    (U : Subrepresentation ρ) (K A : Subgroup G) (hA : IsElementaryTwo A)
    (hAN : A ≤ normalizer (K : Set G))
    (hAC : A ⊓ centralizer (K : Set G) = ⊥)
    (hKU : ∀ k ∈ K, (∀ v, U.toRepresentation k v = v) → k = 1)
    (hKQ : ∀ k ∈ K, (∀ v, U.quotientRepresentation k v = v) → k = 1)
    (hnU : ¬ IsFFModule (imageRepresentation U.toRepresentation))
    (hnQ : ¬ IsFFModule (imageRepresentation U.quotientRepresentation)) :
    2 * rank A < fixedCodim ρ A := by
  have hu := actor_faithful_on_section U.toRepresentation K A ⊤
    (by intro k hk v; simp)
    (fun k hk h => hKU k hk (fun v => h v Submodule.mem_top)) hAN hAC
  have hq := actor_faithful_on_section U.quotientRepresentation K A ⊤
    (by intro k hk v; simp)
    (fun k hk h => hKQ k hk (fun v => h v Submodule.mem_top)) hAN hAC
  exact twice_rank_lt_fixedCodim_of_nonFF_sections ρ U hA
    (fun a ha h => hu a ha (fun v _ => h v))
    (fun a ha h => hq a ha (fun v _ => h v)) hnU hnQ

/-- The same obstruction holds in any intermediate actor containing the
specified elementary subgroup, with no lift of an elementary subgroup. -/
theorem twice_rank_lt_fixedCodim_of_restricted_nonFF_sections
    {A H : Subgroup G} (hA : IsElementaryTwo A) (hAH : A ≤ H)
    (U : Subrepresentation (ρ.comp H.subtype))
    (hU : ∀ a ∈ A.subgroupOf H, (∀ v, U.toRepresentation a v = v) → a = 1)
    (hQ : ∀ a ∈ A.subgroupOf H, (∀ v, U.quotientRepresentation a v = v) → a = 1)
    (hnU : ¬ IsFFModule (imageRepresentation U.toRepresentation))
    (hnQ : ¬ IsFFModule (imageRepresentation U.quotientRepresentation)) :
    2 * rank A < fixedCodim ρ A := by
  let : IsElementaryAbelian 2 A := hA.2
  have hB : IsElementaryTwo (A.subgroupOf H) := by
    refine ⟨?_, IsElementaryAbelian.subgroupOf hAH⟩
    intro hz
    apply hA.1
    rw [← map_subgroupOf_eq_of_le hAH, hz, Subgroup.map_bot]
  have hb := twice_rank_lt_fixedCodim_of_nonFF_sections (ρ.comp H.subtype) U
    hB hU hQ hnU hnQ
  rwa [rank_subgroupOf hAH, fixedCodim_subgroupOf ρ hAH] at hb

/-- The two-section obstruction remains valid for a selected chief section
inside the quotient and any intermediate actor preserving the local space. -/
theorem twice_rank_lt_fixedCodim_of_restricted_nonFF_submodule_sections
    {A H : Subgroup G} (hA : IsElementaryTwo A) (hAH : A ≤ H)
    (U : Subrepresentation (ρ.comp H.subtype))
    (W : Subrepresentation U.quotientRepresentation)
    (hU : ∀ a ∈ A.subgroupOf H, (∀ v, U.toRepresentation a v = v) → a = 1)
    (hW : ∀ a ∈ A.subgroupOf H, (∀ v, W.toRepresentation a v = v) → a = 1)
    (hnU : ¬ IsFFModule (imageRepresentation U.toRepresentation))
    (hnW : ¬ IsFFModule (imageRepresentation W.toRepresentation)) :
    2 * rank A < fixedCodim ρ A := by
  let : IsElementaryAbelian 2 A := hA.2
  have hB : IsElementaryTwo (A.subgroupOf H) := by
    refine ⟨?_, IsElementaryAbelian.subgroupOf hAH⟩
    intro hz
    apply hA.1
    rw [← map_subgroupOf_eq_of_le hAH, hz, Subgroup.map_bot]
  have hb := twice_rank_lt_fixedCodim_of_nonFF_submodule_sections (ρ.comp H.subtype) U W
    hB hU hW hnU hnW
  rwa [rank_subgroupOf hAH, fixedCodim_subgroupOf ρ hAH] at hb

/-- A cubic actor of ratio at most two cannot be faithful on two non-FF sections,
even after restriction to a subgroup that preserves the chosen local section. -/
theorem exists_cubic_actor_without_two_nonFF_sections [Finite G]
    (hbound : cubicRatio ρ ≤ 2) :
    ∃ A : Subgroup G, IsElementaryTwo A ∧ IsCubic ρ A ∧
      fixedCodim ρ A ≤ 2 * rank A ∧
      ∀ (H : Subgroup G), A ≤ H →
        ∀ U : Subrepresentation (ρ.comp H.subtype),
          (¬ IsFFModule (imageRepresentation U.toRepresentation)) →
          (¬ IsFFModule (imageRepresentation U.quotientRepresentation)) →
          ¬ ((∀ a ∈ A.subgroupOf H, (∀ v, U.toRepresentation a v = v) → a = 1) ∧
             (∀ a ∈ A.subgroupOf H, (∀ v, U.quotientRepresentation a v = v) → a = 1)) := by
  obtain ⟨A,hA,hc,hd⟩ := (cubicRatio_le_nat_iff ρ 2).mp hbound
  refine ⟨A,hA,hc,hd,?_⟩
  intro H hAH U hnU hnQ hfaith
  exact (not_lt_of_ge hd) (twice_rank_lt_fixedCodim_of_restricted_nonFF_sections ρ
    hA hAH U hfaith.1 hfaith.2 hnU hnQ)

/-- The original cubic bound also controls every chosen invariant section
inside the quotient by a local section. No faithful quotient action is presumed. -/
theorem exists_cubic_actor_without_two_nonFF_submodule_sections [Finite G]
    (hbound : cubicRatio ρ ≤ 2) :
    ∃ A : Subgroup G, IsElementaryTwo A ∧ IsCubic ρ A ∧
      fixedCodim ρ A ≤ 2 * rank A ∧
      ∀ (H : Subgroup G), A ≤ H →
        ∀ (U : Subrepresentation (ρ.comp H.subtype))
          (W : Subrepresentation U.quotientRepresentation),
          (¬ IsFFModule (imageRepresentation U.toRepresentation)) →
          (¬ IsFFModule (imageRepresentation W.toRepresentation)) →
          ¬ ((∀ a ∈ A.subgroupOf H, (∀ v, U.toRepresentation a v = v) → a = 1) ∧
             (∀ a ∈ A.subgroupOf H, (∀ v, W.toRepresentation a v = v) → a = 1)) := by
  obtain ⟨A,hA,hc,hd⟩ := (cubicRatio_le_nat_iff ρ 2).mp hbound
  refine ⟨A,hA,hc,hd,?_⟩
  intro H hAH U W hnU hnW hfaith
  exact (not_lt_of_ge hd) (twice_rank_lt_fixedCodim_of_restricted_nonFF_submodule_sections ρ
    hA hAH U W hfaith.1 hfaith.2 hnU hnW)

/-- An actual cubic actor whose fixed-codimension budget forbids two faithful
non-FF sections under every intermediate actor that preserves them. -/
@[expose] def HasCubicTwoSectionBudget : Prop :=
  ∃ A : Subgroup G, IsElementaryTwo A ∧ IsCubic ρ A ∧
    fixedCodim ρ A ≤ 2 * rank A ∧
    ∀ (H : Subgroup G), A ≤ H →
      ∀ (U : Subrepresentation (ρ.comp H.subtype))
        (W : Subrepresentation U.quotientRepresentation),
        (¬ IsFFModule (imageRepresentation U.toRepresentation)) →
        (¬ IsFFModule (imageRepresentation W.toRepresentation)) →
        ¬ ((∀ a ∈ A.subgroupOf H, (∀ v, U.toRepresentation a v = v) → a = 1) ∧
           (∀ a ∈ A.subgroupOf H, (∀ v, W.toRepresentation a v = v) → a = 1))

/-- The numerical bound constructs the actual two-section budget witness. -/
theorem hasCubicTwoSectionBudget_of_le_two [Finite G]
    (hbound : cubicRatio ρ ≤ 2) : HasCubicTwoSectionBudget ρ :=
  exists_cubic_actor_without_two_nonFF_submodule_sections ρ hbound

end Representation.BinaryOffender
