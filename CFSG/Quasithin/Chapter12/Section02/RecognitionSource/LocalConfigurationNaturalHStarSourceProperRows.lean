module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceProperLinear
public import Theory.GroupTheory.SolvableSylowOvergroupLifts
public import Theory.GroupTheory.SylowLocalCore
public import Theory.SpecificGroups.PSL3Two.SolvableSylowOvergroups
public import Theory.SpecificGroups.G2Even.BinaryDerivedSolvableOvergroups
public import Theory.SpecificGroups.AlternatingSix.ProperSylowOvergroups
public import Theory.SpecificGroups.Alternating.FiveProperSubgroups

/-!
# Proper overcomponents of the original H-star residual

In a perfect group whose proper Sylow overgroups are solvable, a nonsolvable
Sylow-normalized subgroup is the whole group. Applied to the literal H-star
component, this rules out the SL₃(2), A₅, A₆, G₂(2)′ and triple-six rows for a
proper overcomponent. The full binary natural rows are excluded by the flag
argument, leaving the exterior-five and alternating-seven/eight rows.

The model calculations and two-core transports are shared with the terminal
application in Section03/SourceAlternatingSeven/TerminalComponentResidualProper;
this application retains the original NoEscape/H-star setting. Source:
Aschbacher–Smith, 12.2.7, printed pp.797–798.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterB.QuasisimpleSource ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H X Y W : Subgroup G}

/-- A proper original overcomponent cannot have solvable proper Sylow overgroups. -/
theorem HStarGeneratingComponent.not_solvableSylowOvergroups_of_proper_at
    (C : HStarGeneratingComponent T L H X)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hXY : X < Y) (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y) :
    ¬ SolvableSylowOvergroups Y := by
  have hTX := C.normalized_of_overcomponent_at structural modules hH hXY.le hY
  have hTY := (structural Y hY).1
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Group.IsPerfect Y := Chapter1.mem_L_isPerfect hY.maximal_faithful.1.1
  let B := X.subgroupOf Y
  obtain ⟨U,hU⟩ := (T.subtype
    (show (T : Subgroup G) ≤ Y ⊔ (T : Subgroup G) from le_sup_right)).exists_map_subtype_eq_inf_of_normalizes
      (show Y ≤ Y ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le Y.le_normalizer hTY)
  have hU' : (U : Subgroup Y).map Y.subtype = (T : Subgroup G) ⊓ Y := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using hU
  have hUT : (U : Subgroup Y) ≤ (T : Subgroup G).subgroupOf Y := by
    intro x hx
    have hm : (x : G) ∈ (T : Subgroup G) ⊓ Y :=
      hU' ▸ mem_map_of_mem Y.subtype hx
    exact hm.1
  have hUB : (U : Subgroup Y) ≤ normalizer (B : Set Y) :=
    (hUT.trans (comap_mono hTX)).trans
      (le_normalizer_comap Y.subtype)
  have hs : ¬ Group.IsSolvable B := by
    intro hs
    let := hs
    exact Chapter1.mem_L_not_isSolvable
      (C.exists_maximal_overcomponent hH).1
      (Group.isSolvable_of_surjective
        (f := (subgroupOfEquivOfLe hXY.le).toMonoidHom)
        (subgroupOfEquivOfLe hXY.le).surjective)
  intro h
  have he := h.eq_top_of_sylow_normalizes U B hUB hs
  have he' : Y ≤ X := subgroupOf_eq_top.mp he
  exact hXY.not_ge he'

private theorem solvableSylow_of_core {Y : Subgroup G}
    (h : SolvableSylowOvergroups (Y ⧸ pCore 2 Y)) : SolvableSylowOvergroups Y := by
  apply SolvableSylowOvergroups.of_two_kernel
    (QuotientGroup.mk' (pCore 2 Y)) (QuotientGroup.mk'_surjective _)
  · rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  · exact h

private theorem solvableSylow_of_faithful_small
    {Y W : Subgroup G} (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y)
    (E : ChosenModule T Y W) (n : ℕ) (hn : n = 5 ∨ n = 6)
    (e : letI := E.actionCentralizer_normal
      (Y ⧸ (centralizer (W : Set G)).subgroupOf Y) ≃* alternatingGroup (Fin n)) :
    SolvableSylowOvergroups Y := by
  let := E.actionCentralizer_normal
  let := hY.quasisimple
  let : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simp only [Nat.card_fin]; omega)
  let r := e.toMonoidHom.comp E.coreToFaithful
  have hr : Function.Surjective r := e.surjective.comp E.coreToFaithful_surjective
  have hk : r.ker = center (Y ⧸ pCore 2 Y) := by
    have hh := IsQuasisimple.comap_center_of_surjective r hr
    rw [alternatingGroup.center_eq_bot (by simp only [Nat.card_fin]; omega),
      MonoidHom.comap_bot] at hh
    exact hh
  apply solvableSylow_of_core
  apply SolvableSylowOvergroups.of_central_quotient r hr hk.le
  rcases hn with rfl | rfl
  · intro U B _ hB
    exact alternatingGroup.isSolvable_subgroup_five_of_ne_top B hB
  · exact AlternatingSix.ProperSylowOvergroups.isSolvable

private theorem solvableSylow_hexEven :
    SolvableSylowOvergroups Atlas.Codes.HexEvenAutomorphisms := by
  let : Group.IsPerfect Atlas.Codes.HexEvenAutomorphisms := Representation.Hexacode.even_isPerfect
  apply SolvableSylowOvergroups.of_central_quotient
    (QuotientGroup.mk' (center Atlas.Codes.HexEvenAutomorphisms))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])
  exact SolvableSylowOvergroups.of_equiv Representation.Hexacode.even_quotient_center_equiv
    AlternatingSix.ProperSylowOvergroups.isSolvable

/-- The surviving literal rows for a proper overcomponent, before the
exterior and alternating-eight exclusions. -/
inductive HStarProperRows (E : ChosenModule T Y W) : Prop
  | exterior
      (groupEquiv : (Y ⧸ pCore 2 Y) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
      (dimension : Module.finrank (ZMod 2) E.space = 10)
      (irreducible : IsIrreducible E.quotientAction)
  | alternating (n : ℕ) (degree : n = 7 ∨ n = 8)
      (action : letI := E.actionCentralizer_normal
        ActionEquiv E.faithfulCentralAction (alternatingNatural n))
  | sevenFour
      (groupEquiv : letI := E.actionCentralizer_normal
        (Y ⧸ (centralizer (W : Set G)).subgroupOf Y) ≃* alternatingGroup (Fin 7))
      (dimension : Module.finrank (ZMod 2) E.space = 4)

/-- Restrict the seven source rows on the actual proper H-star overcomponent. -/
theorem HStarGeneratingComponent.proper_rows_at
    (C : HStarGeneratingComponent T L H X)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hXY : X < Y) (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y)
    (E : ChosenModule T Y W) : HStarProperRows E := by
  let := E.actionCentralizer_normal
  have hn := C.not_solvableSylowOvergroups_of_proper_at structural modules hH hXY hY
  have hthree (e : (Y ⧸ pCore 2 Y) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
      False := hn (solvableSylow_of_core (SolvableSylowOvergroups.of_equiv e
        (Matrix.PSL3Two.solvableSylowOvergroups_specialLinear_of_card_two (by simp))))
  cases modules Y W hY E with
  | linear n degree action =>
    exact (C.not_natural_overcomponent_at (by omega) h D structural hTI hH hXY.le hY E
      ⟨action⟩).elim
  | linearThreeExtension groupEquiv _ _ => exact (hthree groupEquiv).elim
  | linearFiveExterior groupEquiv dimension irreducible =>
    exact .exterior groupEquiv dimension irreducible
  | alternating n lower upper action =>
    by_cases hs : n = 5 ∨ n = 6
    · exact (hn (solvableSylow_of_faithful_small hY E n hs action.groupEquiv)).elim
    · exact .alternating n (by omega) action
  | alternatingSevenFour groupEquiv dimension => exact .sevenFour groupEquiv dimension
  | g2 action =>
    exact (hn (solvableSylow_of_core (SolvableSylowOvergroups.of_equiv action.groupEquiv
      Atlas.G2.binaryDerived_solvableSylowOvergroups))).elim
  | tripleSix groupEquiv _ _ _ =>
    exact (hn (solvableSylow_of_core (SolvableSylowOvergroups.of_equiv groupEquiv
      solvableSylow_hexEven))).elim

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
