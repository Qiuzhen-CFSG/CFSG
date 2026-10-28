module
public import CFSG.Quasithin.ChapterC.Section04.A5ConstrainedSelection
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedLinearTwo
public import CFSG.Quasithin.ChapterC.Section04.A5LinearThreeComplete
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedG2Normality

/-!
# Original component normality for an A₅ seed

Under the genuine C.2.8 hypotheses and strict local containment, an
A₅-marked seed component is normal in its local overgroup. The completed
contained-Fitting and ordinary branches reduce nonnormality to four
constrained star models. The actual radical action excludes the SL₂ and
A₅ rows; the original pair action and local normalizer bounds exclude
SL₃ and large G₂. Every marking is the literal quotient of the selected
component, and all additional branch premises are discharged here.

This is the specialized consequence of C.4.8 needed by the A₅ covering
argument. It does not assert the full general module classification.
Source: Aschbacher–Smith C.4.8, printed pp.153–154, applied in
4.2.12–13, pp.610–611, and the A₅ setup of 10.2, p.744.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

theorem normalizes_of_a5_quotient
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hstrict : M < H) (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5)) :
    M ≤ normalizer (L : Set G) := by
  by_contra hn
  obtain ⟨K,hK,hq,hout,hfK,hm⟩ := h.nonnormal_a5_constrained_remainder hstrict a hn
  rcases hm with hm | hm | hm | hm
  · obtain ⟨F,⟨e⟩⟩ := hm
    exact h.no_constrained_component_star_linear_two K hK hq hout hfK F e
  · obtain ⟨F,⟨e⟩⟩ := hm
    exact hn (h.normalizes_a5_of_constrained_star_linear_three a K hK hq hout hfK F e)
  · obtain ⟨F,hF,⟨e⟩⟩ := hm
    exact hn (h.normalizes_a5_of_constrained_star_g2 a K hK hq hout hfK F hF e)
  · obtain ⟨e⟩ := hm
    exact h.no_constrained_component_star_alternating_five K hK hq hout hfK e

theorem span_eq_of_a5_quotient
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hstrict : M < H) (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5)) :
    conjugateSpanBy L M = L :=
  le_antisymm (conjugateSpanBy_le le_rfl (h.normalizes_of_a5_quotient hstrict a))
    (le_conjugateSpanBy L M)

end CFSG.Quasithin.ChapterC.HypothesisC28
