module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Configuration
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.Radical
public import CFSG.Quasithin.Chapter4.Section01.RadicalBounds
public import Theory.GroupTheory.GeneralizedFitting.SemisimpleCenter

/-!
# The fixed radical at the start of original 4.3.6

The ordinary component centralizes O₂(H), which is nontrivial and lies in
R = O₂(I). Thus R₀ = C_R(L) is nontrivial. The exact identity
R = (T ∩ H) ∩ O₂(LT) makes the Sylow intersection and its crossing element
normalize R. They also normalize L, so they preserve R₀. Uniqueness over
LS⟨t⟩ controls N_G(R₀), and the escaping component cannot centralize R₀.

These are the source inputs to the remaining C.3.1/automorphism inspection;
no ordinary model or module marking is asserted here.
Source: Aschbacher--Smith 4.3.6, printed p.614.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The source R₀, with R = O₂(I), inside the original ambient group. -/
abbrev SourceConfiguration.ordinaryFixedRadical (c : SourceConfiguration T L) : Subgroup G :=
  c.I.pCoreIn 2 ⊓ centralizer (L : Set G)

omit [Finite G] in
/-- Both the full Sylow intersection and the crossing element normalize R. -/
theorem SourceConfiguration.crossing_radical_normalizes (c : SourceConfiguration T L) :
    ((T : Subgroup G) ⊓ c.H ⊔ zpowers c.t) ≤ normalizer (c.I.pCoreIn 2 : Set G) := by
  have hQ : (T : Subgroup G) ≤
      normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
    le_sup_right.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  rw [c.core_sylow]
  apply (le_inf ?_ ?_).trans inf_normalizer_le_normalizer_inf
  · exact sup_le ((T : Subgroup G) ⊓ c.H).le_normalizer
      (zpowers_le.mpr c.crossing_normalizes)
  · exact (sup_le inf_le_left (zpowers_le.mpr c.crossing_mem)).trans hQ

/-- The ordinary component centralizes the actual two-core of H. -/
theorem SourceConfiguration.ordinary_component_centralizes_core
    (c : SourceConfiguration T L) (ho : IsComponent c.H c.K) :
    c.K.map c.H.subtype ≤ centralizer (c.H.pCoreIn 2 : Set G) := by
  let : Group.IsNilpotent (pCore 2 c.H) := pCore_isPGroup.isNilpotent
  have hc := ho.le_centralizer_of_solvable_normal (pCore 2 c.H)
  rintro _ ⟨k,hk,rfl⟩ _ ⟨q,hq,rfl⟩
  exact congrArg Subtype.val (hc hk q hq)

/-- The nontrivial two-core of H lies in C_R(L). -/
theorem SourceConfiguration.ordinary_core_le_fixedRadical
    (c : SourceConfiguration T L) (ho : IsComponent c.H c.K) :
    c.H.pCoreIn 2 ≤ c.ordinaryFixedRadical :=
  le_inf (core_le_of_relative_radical c.c28.isRadical)
    (le_centralizer_iff.mp (c.le_component.trans (c.ordinary_component_centralizes_core ho)))

/-- The source fixed radical is nontrivial, before any model classification. -/
theorem SourceConfiguration.ordinaryFixedRadical_ne_bot
    (c : SourceConfiguration T L) (ho : IsComponent c.H c.K) :
    c.ordinaryFixedRadical ≠ ⊥ := by
  intro he
  exact c.c28.core_nontrivial (bot_unique (he ▸ c.ordinary_core_le_fixedRadical ho))

/-- The source L S⟨t⟩ preserves the fixed radical. -/
theorem SourceConfiguration.ordinaryFixedRadical_normalized
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V) :
    L ⊔ ((T : Subgroup G) ⊓ c.H ⊔ zpowers c.t) ≤
      normalizer (c.ordinaryFixedRadical : Set G) := by
  apply (le_inf ?_ ?_).trans inf_normalizer_le_normalizer_inf
  · exact sup_le ((le_conjugateSpanBy L _).trans c.c28.span_normalizes_radical)
      c.crossing_radical_normalizes
  · exact (sup_le L.le_normalizer
      ((sup_le inf_le_left (zpowers_le.mpr c.crossing_mem)).trans
        D.sylow_normalizes_component)).trans (normalizer_le_normalizer_centralizer L)

/-- Original 4.3.5 controls the full ambient normalizer of R₀. -/
theorem SourceConfiguration.ordinaryFixedRadical_normalizer_le
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (ho : IsComponent c.H c.K) :
    normalizer (c.ordinaryFixedRadical : Set G) ≤ normalizer (L : Set G) :=
  c.crossing_normalizer_control
    ((isPGroup_pCoreIn 2 c.I).to_le inf_le_left)
    (c.ordinaryFixedRadical_ne_bot ho) (c.ordinaryFixedRadical_normalized D)

/-- The nontrivial image of R₀ in the component action is forced by escape. -/
theorem SourceConfiguration.ordinaryFixedRadical_not_centralizes_component
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (ho : IsComponent c.H c.K) :
    ¬ c.ordinaryFixedRadical ≤ centralizer (c.K.map c.H.subtype : Set G) := by
  intro hc
  exact c.component_outside ((le_centralizer_iff.mp hc).trans
    ((Subgroup.centralizer_le_normalizer _).trans (c.ordinaryFixedRadical_normalizer_le D ho)))

/-- The literal source commutator [K,R₀] is nonidentity. -/
theorem SourceConfiguration.ordinaryFixedRadical_commutator_ne_bot
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (ho : IsComponent c.H c.K) :
    ⁅c.K.map c.H.subtype,c.ordinaryFixedRadical⁆ ≠ ⊥ := by
  intro he
  exact c.ordinaryFixedRadical_not_centralizes_component D ho
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he))

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
