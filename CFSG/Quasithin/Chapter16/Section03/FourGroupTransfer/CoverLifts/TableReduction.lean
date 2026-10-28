module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.CoverLifts.Inputs
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.CoverLifts.TableReduction.SourceClauses
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.CoverLifts.TableReduction.Action
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.CoverLifts.TableReduction.Intrinsic
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.CoverLifts.TableReduction.MathieuJanko
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.CoverLifts.TableReduction.Rudvalis

/-!
# The exceptional-cover table reduction

The center bound follows from the explicit applicable 16.1.2 clause, after
identifying Z(I) with O₂(I) using E1. The inner-index argument uses the actual
C₂ × A₅ fixed subgroup in the outer M₁₂ row, rather than an assumed bound
on Out(I). The paired component and central-quotient models are transported
through explicit equivalences for the remaining table arguments.

The J₂ and Ru component deductions exclude outer actors in those cases.
The component and Sylow calculations in all three models exclude 2-central
quotient representatives of inner actors. `table_reduction_of_source`
assembles all four fields with only the literal earlier center and involution
clauses as source inputs; it discharges the intermediate outer-M₁₂ premise
of `inner_index_of_outer_m12`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 16.1.2,
16.1.5 and 16.3.6, printed pp.1170–1172 and 1179 / PDF pp.1187–1189 and 1196.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.CoverLifts.TableReduction
open Subgroup Theory.GroupTheory Theory.GroupTheory.DoubleCoverCentralizer ClassificationModels
variable {G : Type*} [Group G] [Finite G] {𝒦 : GroupClass}
variable {E L : Subgroup G} {i : G}

/-- E1 transports both members of each exceptional model pair to the exact
intrinsic component and central quotient used by the automorphism tables. -/
theorem enlargement_model_pairs (hG : Hypothesis1611 𝒦 G) (hi : orderOf i = 2)
    (h : ExceptionalEnlargement E L i) :
    (Nonempty (ComponentInside L i ≃* alternatingGroup (Fin 5)) ∧
      (Nonempty ((Enlargement L i ⧸ center (Enlargement L i)) ≃* SporadicName.m12.Carrier) ∨
       Nonempty ((Enlargement L i ⧸ center (Enlargement L i)) ≃* SporadicName.j2.Carrier))) ∨
    (Nonempty (ComponentInside L i ≃* SzEight) ∧
      Nonempty ((Enlargement L i ⧸ center (Enlargement L i)) ≃* SporadicName.ru.Carrier)) := by
  let q := QuotientGroup.quotientMulEquivOfEq
    (hG.evenType.component_center_eq_twoCore hi h.component)
  let j := subgroupOfEquivOfLe (ComponentTransfer.le_layerClosure (involutionCentralizer i) L)
  rcases h.models with ⟨⟨l⟩, hm | hj⟩ | ⟨⟨l⟩, ⟨hr⟩⟩
  · obtain ⟨m⟩ := hm
    exact Or.inl ⟨⟨j.trans l⟩, Or.inl ⟨q.trans m⟩⟩
  · obtain ⟨m⟩ := hj
    exact Or.inl ⟨⟨j.trans l⟩, Or.inr ⟨q.trans m⟩⟩
  · exact Or.inr ⟨⟨j.trans l⟩, ⟨q.trans hr⟩⟩

/-- Apply only the specialized earlier center clause to the actual component. -/
theorem center_bound_of_source (source : CenterClause (G := G) 𝒦)
    (hG : Hypothesis1611 𝒦 G) (hi : orderOf i = 2)
    (h : ExceptionalEnlargement E L i) : Nat.card (center (Enlargement L i)) ≤ 2 := by
  apply source hG i (Enlargement L i) hi h.component
  rcases enlargement_model_pairs hG hi h with ⟨_, hm | hj⟩ | ⟨_, hr⟩
  · exact Or.inl hm
  · exact Or.inr (Or.inl hj)
  · exact Or.inr (Or.inr hr)

/-- The M₁₂ fixed-subgroup row proves the inner-index bound once the separate
table sieve has restricted outer actors to that actual model. -/
theorem inner_index_of_outer_m12 (tables : InvolutionTables)
    (hG : Hypothesis1611 𝒦 G) (hi : orderOf i = 2)
    (h : ExceptionalEnlargement E L i) (hcard : Nat.card E = 4)
    (hc : CentralizesAsComponent E L)
    (ho : ∀ e : E, inducedAction E (Enlargement L i) h.normalizes e ∉
        (MulAut.conj : Enlargement L i →* MulAut (Enlargement L i)).range →
      Nonempty ((Enlargement L i ⧸ pCore 2 (Enlargement L i)) ≃* SporadicName.m12.Carrier)) :
    (innerActors (inducedAction E (Enlargement L i) h.normalizes)).index ≤ 2 := by
  classical
  let α := inducedAction E (Enlargement L i) h.normalizes
  by_cases hall : ∀ e : E, α e ∈ (MulAut.conj : Enlargement L i →* MulAut (Enlargement L i)).range
  · have ht : innerActors α = ⊤ := top_unique (fun e _ => hall e)
    change (innerActors α).index ≤ 2
    rw [ht, index_top]
    decide
  · push Not at hall
    obtain ⟨a, ha⟩ := hall
    have ha1 : a ≠ 1 := by intro hh; exact ha (hh ▸ (by simp))
    obtain ⟨e⟩ := ho a ha
    let q := (QuotientGroup.quotientMulEquivOfEq
      (hG.evenType.component_center_eq_twoCore hi h.component)).trans e
    let := h.component.quasisimple
    have hr : orderOf (MulAut.centralQuotientAction q (α a)) = 2 :=
      (orderOf_injective _ (MulAut.centralQuotientAction_injective q) _).trans
        (actor_order_two h a ha1)
    have hrout : ¬ ∃ g, MulAut.centralQuotientAction q (α a) = MulAut.conj g := by
      intro hh
      obtain ⟨f, hf⟩ := (MulAut.centralQuotientAction_inner_iff q (α a)).mp hh
      exact ha ⟨f, hf.symm⟩
    have hproduct : Nonempty ((MulAut.centralQuotientAction q (α a)).fixedSubgroup ≃*
        OtherPreliminaries.Mathieu.C2 × OtherPreliminaries.Mathieu.A5) := by
      rcases tables.m12 _ hr with ⟨hin, _⟩ | ⟨_, hp⟩
      · exact (hrout hin).elim
      · exact hp
    obtain ⟨f⟩ := hproduct
    let := componentInside_perfect (i := i) hcard hc
    apply innerActors_index_le_two_of_fixed_product (ComponentInside L i) α
      (h.image_eq.trans (by rw [component_action_range L i])) hcard q a
      (actor_fixes_component h hc a) f

private theorem outer_m12_of_source (tables : InvolutionTables)
    (hG : Hypothesis1611 𝒦 G) (hi : orderOf i = 2)
    (h : ExceptionalEnlargement E L i) (hc : CentralizesAsComponent E L) :
    ∀ e : E,
      inducedAction E (Enlargement L i) h.normalizes e ∉
        (MulAut.conj : Enlargement L i →* MulAut (Enlargement L i)).range →
      Nonempty ((Enlargement L i ⧸ pCore 2 (Enlargement L i)) ≃*
        SporadicName.m12.Carrier) := by
  let := h.component.quasisimple
  intro e he
  have he' : e ≠ 1 := by
    intro he1
    exact he (he1 ▸ (by simp))
  have hr := actor_order_two h e he'
  have hJ := actor_component h hc e he'
  rcases enlargement_model_pairs hG hi h with ⟨eJ, hm | hj⟩ | ⟨eJ, er⟩
  · obtain ⟨em⟩ := hm
    exact ⟨(QuotientGroup.quotientMulEquivOfEq
      (hG.evenType.component_center_eq_twoCore hi h.component)).symm.trans em⟩
  · obtain ⟨ej⟩ := hj
    obtain ⟨f, hf⟩ := j2_inner_of_component tables (ComponentInside L i)
      (inducedAction E (Enlargement L i) h.normalizes e) hr hJ eJ ej
    exact (he ⟨f, hf.symm⟩).elim
  · obtain ⟨f, hf⟩ := rudvalis_inner_of_source (ComponentInside L i)
      (inducedAction E (Enlargement L i) h.normalizes e) tables hr hJ eJ er
    exact (he ⟨f, hf.symm⟩).elim

private theorem non_two_central_mark_of_source (tables : InvolutionTables)
    (hG : Hypothesis1611 𝒦 G) (hi : orderOf i = 2)
    (h : ExceptionalEnlargement E L i) (hc : CentralizesAsComponent E L)
    (f : Enlargement L i)
    (hf2 : orderOf (QuotientGroup.mk' (center (Enlargement L i)) f) = 2)
    (hfrange : MulAut.conj f ∈ (inducedAction E (Enlargement L i) h.normalizes).range) :
    ¬ TwoCentral (QuotientGroup.mk' (center (Enlargement L i)) f) := by
  let := h.component.quasisimple
  obtain ⟨e, he⟩ := hfrange
  have he' : e ≠ 1 := by
    intro he1
    have hconj : MulAut.conj f = 1 := by
      simpa only [he1, map_one] using he.symm
    have hfZ : f ∈ center (Enlargement L i) := by
      rw [← conj_kernel]
      exact hconj
    have hqone : QuotientGroup.mk' (center (Enlargement L i)) f = 1 :=
      (QuotientGroup.eq_one_iff f).mpr hfZ
    rw [hqone, orderOf_one] at hf2
    norm_num at hf2
  have hr := actor_order_two h e he'
  have hJ := actor_component h hc e he'
  rcases enlargement_model_pairs hG hi h with ⟨eJ, hm | hj⟩ | ⟨eJ, er⟩
  · obtain ⟨em⟩ := hm
    exact m12_not_twoCentral_of_component tables (ComponentInside L i)
      (inducedAction E (Enlargement L i) h.normalizes e) hr hJ eJ em f he.symm hf2
  · obtain ⟨ej⟩ := hj
    exact j2_not_twoCentral_of_component (ComponentInside L i)
      (inducedAction E (Enlargement L i) h.normalizes e) hr hJ eJ ej f he.symm hf2
  · exact rudvalis_non_two_central_of_source (ComponentInside L i)
      (inducedAction E (Enlargement L i) h.normalizes e) tables hr hJ eJ er f he.symm hf2

/-- The literal 16.1.2 and 16.1.5 clauses imply the complete intermediate
contract used by the exceptional-cover lifting argument. The component
hypotheses discharge the outer-model restriction and non-2-central mark;
no lifting assertion from I.2.2 is needed for this deduction. -/
theorem table_reduction_of_source (source : CenterClause (G := G) 𝒦)
    (tables : InvolutionTables) (hG : Hypothesis1611 𝒦 G)
    (hi : orderOf i = 2) (h : ExceptionalEnlargement E L i)
    (hcard : Nat.card E = 4) (hc : CentralizesAsComponent E L) :
    TableReduction E L i h := by
  have houter := outer_m12_of_source tables hG hi h hc
  exact
    { center_bound := center_bound_of_source source hG hi h
      inner_index := inner_index_of_outer_m12 tables hG hi h hcard hc houter
      outer_m12 := houter
      non_two_central_mark := non_two_central_mark_of_source tables hG hi h hc }

end CFSG.Quasithin.Chapter16.FourGroupTransfer.CoverLifts.TableReduction
