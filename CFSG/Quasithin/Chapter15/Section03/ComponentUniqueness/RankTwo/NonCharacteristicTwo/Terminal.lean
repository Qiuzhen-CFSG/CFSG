module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.Definitions

/-!
# The centralizer contradiction after the local model calculation

An order-four moved subgroup forces the second case of Hypothesis 15.3.10,
since the first case moves the whole group V of order sixteen. The defining
two-residual in that second case centralizes V₁. A trivial fixer for the actual
Y₊ image in the component quotient then puts V₁ in C_I(L). Symmetry of
centralization and the earlier normalizer bound force L ≤ M.

The local model calculation must still prove the commutator order and fixer
condition through an actual equivalence I/C_I(L) ≃ Aut(J₂). These conditional
reductions do not replace that calculation or the preceding catalogue sieve.
Source: Aschbacher--Smith, combined manuscript, 15.3.42, printed p.1138.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo
variable {G : Type*} [Group G]

/-- The first choice in Hypothesis 15.3.10 moves all sixteen elements of V,
so a commutator of order four forces the second choice. -/
theorem caseTwo_of_moved_card_four
    {M Y S V V₁ Yplus : Subgroup G}
    (hcases : Hypothesis15310 M Y S V₁ Yplus)
    (hV : ⁅V, Y⁆ = V) (hcardV : Nat.card V = 16)
    (hcardMoved : Nat.card (⁅V, Yplus⁆ : Subgroup G) = 4) : CaseTwo M Y S V₁ Yplus := by
  rcases hcases with h | h
  · rw [h, hV, hcardV] at hcardMoved
    contradiction
  · exact h

/-- The residual in the actual second choice centralizes the first plane. -/
theorem caseTwo_le_centralizer
    {M Y S V₁ Yplus : Subgroup G} (h : CaseTwo M Y S V₁ Yplus) :
    V₁ ≤ centralizer (Yplus : Set G) := by
  apply le_centralizer_iff.mpr
  rw [h.2]
  exact (map_subtype_le _).trans inf_le_right

/-- A trivial centralizer of the actual quotient image gives the source
containment C_I(Y₊) ≤ C_I(L). Only normality inside I is needed. -/
theorem relative_centralizer_le_of_image_centralizer_eq_bot
    {I L Yplus : Subgroup G} [(L.subgroupOf I).Normal] (hLI : L ≤ I)
    (hc : centralizer (componentImage I L Yplus : Set (ComponentQuotient I L)) = ⊥) :
    (centralizer (Yplus : Set G)).subgroupOf I ≤
      (centralizer (L : Set G)).subgroupOf I := by
  intro x hx
  rw [← component_kernel_eq I L hLI]
  change centralizerQuotientMap (L.subgroupOf I) x = 1
  have hx' : centralizerQuotientMap (L.subgroupOf I) x ∈
      centralizer (componentImage I L Yplus : Set (ComponentQuotient I L)) := by
    rintro y ⟨y, hy, rfl⟩
    have hxy : y * x = x * y := Subtype.ext (hx y hy)
    simpa only [map_mul] using congrArg (centralizerQuotientMap (L.subgroupOf I)) hxy
  simpa only [hc, mem_bot] using hx'

/-- The terminal centralizer chain on p.1138: V₁ centralizes L, and
C_G(V₁) ≤ N_G(V₁) ≤ M by the genuine earlier normalizer control. -/
theorem component_le_of_caseTwo_centralizer
    {I L M Y S V₁ Yplus : Subgroup G}
    (hcase : CaseTwo M Y S V₁ Yplus) (hVI : V₁ ≤ I)
    (hc : (centralizer (Yplus : Set G)).subgroupOf I ≤
      (centralizer (L : Set G)).subgroupOf I)
    (hcontrol : normalizer (V₁ : Set G) ≤ M) : L ≤ M := by
  apply (le_centralizer_iff.mp ?_).trans ((Subgroup.centralizer_le_normalizer _).trans hcontrol)
  intro v hv
  exact hc (show (⟨v, hVI hv⟩ : I) ∈
    (centralizer (Yplus : Set G)).subgroupOf I from caseTwo_le_centralizer hcase hv)



/-- Transport the fixer calculation through the specified model equivalence.
The subgroup in the model is the actual image under that same equivalence. -/
theorem centralizer_eq_bot_of_model
    {H K : Type*} [Group H] [Group K] (U : Subgroup H) (e : H ≃* K)
    (hc : centralizer (U.map e.toMonoidHom : Set K) = ⊥) :
    centralizer (U : Set H) = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  change x = 1
  apply e.injective
  rw [map_one]
  have he : e x ∈ centralizer (U.map e.toMonoidHom : Set K) := by
    rintro _ ⟨y, hy, rfl⟩
    change e y * e x = e x * e y
    simpa only [map_mul] using congrArg e (hx y hy)
  simpa only [hc, mem_bot] using he

/-- The exact terminal source argument, using the relative centralizer
containment rather than requiring a trivial centralizer in the quotient. -/
theorem no_component_of_local_action
    {I L M Y S V V₁ V₂ Yplus : Subgroup G} [(L.subgroupOf I).Normal]
    (d : ComponentSetup I L M Yplus S) (a : ActionSetup M Y S V V₁ V₂ Yplus)
    (hcard : Nat.card (⁅V, Yplus⁆ : Subgroup G) = 4)
    (hcentral : (centralizer (Yplus : Set G)).subgroupOf I ≤
      (centralizer (L : Set G)).subgroupOf I) : False := by
  have hc := caseTwo_of_moved_card_four a.hypothesis a.moved a.card hcard
  have hSI : S ≤ I := d.join_eq ▸ le_sup_right
  exact d.outside (component_le_of_caseTwo_centralizer hc
    (a.first_le.trans (a.le_sylow.trans hSI)) hcentral (a.normalizer_control hc))

/-- The final contradiction, conditional on the two local model calculations.
The order-four commutator and trivial model fixer are explicit premises; this
does not assert that they hold for Aut(J₂), or prove the full 15.3.42. -/
theorem no_component_of_model_action
    {I L M Y S V V₁ V₂ Yplus : Subgroup G} [(L.subgroupOf I).Normal]
    (d : ComponentSetup I L M Yplus S) (a : ActionSetup M Y S V V₁ V₂ Yplus)
    {H : Type*} [Group H] (e : ComponentQuotient I L ≃* H)
    (hcard : Nat.card (⁅V, Yplus⁆ : Subgroup G) = 4)
    (hfix : centralizer ((componentImage I L Yplus).map e.toMonoidHom : Set H) = ⊥) :
    False := by
  exact no_component_of_local_action d a hcard
    (relative_centralizer_le_of_image_centralizer_eq_bot d.component_le
      (centralizer_eq_bot_of_model _ e hfix))

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo
