module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentResidualOpening
public import Theory.GroupTheory.SolvableSylowOvergroupLifts
public import Theory.GroupTheory.SylowLocalCore
public import Theory.SpecificGroups.PSL3Two.SolvableSylowOvergroups
public import Theory.SpecificGroups.G2Even.BinaryDerivedSolvableOvergroups
public import Theory.SpecificGroups.AlternatingSix.ProperSylowOvergroups
public import Theory.SpecificGroups.Alternating.FiveProperSubgroups

/-!
# First restriction of proper terminal overcomponents

A proper overcomponent cannot have only solvable proper Sylow-two overgroups:
its Sylow subgroup normalizes the nonsolvable terminal residual, so their join
would be the whole perfect overcomponent and force the residual to be the
whole overcomponent. This eliminates the SL₃(2), A₅, A₆, G₂(2)′ and triple-cover
rows of the seven-module theorem, using the actual two-core and action kernels.
The surviving alternatives retain their original actions and dimensions.

In the seven-letter rows, the central quotient marking is constructed from the
faithful marking through the literal two-core projection. Recognition of the
residual as A₅ and exclusion of the other surviving rows remain with
qt-d-1231-terminal-component; this is a restriction step, not the completed
source theorem. Its assembly application is in TerminalComponentProperModels.

Source: Aschbacher–Smith, 12.2.7, printed pp.797–798, as used in 12.3.12, p.811.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable {S : Setup T L V} {D : S.LocalAnalysis}
namespace TerminalPoint
variable (P : TerminalPoint S D)

theorem proper_overcomponent_not_solvableSylowOvergroups
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    {Y : Subgroup G} (hY : Y ∈ Chapter1.LStar G (T : Subgroup G))
    (hKY : P.K < Y) (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G)) :
    ¬ SolvableSylowOvergroups Y := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Group.IsPerfect Y := Chapter1.mem_L_isPerfect hY.1
  let B := P.K.subgroupOf Y
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
    (hUT.trans (comap_mono P.sylow_normalizes_residual)).trans
      (le_normalizer_comap Y.subtype)
  have hs : ¬ Group.IsSolvable B := by
    intro hs
    let := hs
    exact Chapter1.mem_L_not_isSolvable
      (P.residual_local_and_quasisimple structural modules hr hw).1
      (Group.isSolvable_of_surjective
        (f := (subgroupOfEquivOfLe hKY.le).toMonoidHom)
        (subgroupOfEquivOfLe hKY.le).surjective)
  intro h
  have he := h.eq_top_of_sylow_normalizes U B hUB hs
  have he' : Y ≤ P.K := subgroupOf_eq_top.mp he
  exact hKY.not_ge he'

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

/-- The surviving source rows, retaining their original actions and dimensions. -/
inductive ProperOvercomponentAlternatives {Y W : Subgroup G}
    (E : ChosenModule T Y W) : Prop
  | linear (n : ℕ) (degree : n = 4 ∨ n = 5)
      (action : ActionEquiv E.quotientAction
        (specialLinearNatural (k := ZMod 2) n))
  | linearFiveExterior
      (groupEquiv : (Y ⧸ pCore 2 Y) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
      (dimension : Module.finrank (ZMod 2) E.space = 10)
      (irreducible : Representation.IsIrreducible E.quotientAction)
  | alternating (n : ℕ) (degree : n = 7 ∨ n = 8)
      (action : letI := E.actionCentralizer_normal
        ActionEquiv E.faithfulCentralAction (alternatingNatural n))
  | alternatingSevenFour
      (groupEquiv : letI := E.actionCentralizer_normal
        (Y ⧸ (centralizer (W : Set G)).subgroupOf Y) ≃* alternatingGroup (Fin 7))
      (dimension : Module.finrank (ZMod 2) E.space = 4)

/-- Eliminate all solvable-Sylow-overgroup models on the actual terminal
residual, without presupposing a marking of its two-core quotient. -/
theorem proper_overcomponent_alternatives
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    {Y W : Subgroup G} (hY : Y ∈ Chapter1.LStar G (T : Subgroup G))
    (hKY : P.K < Y) (E : ChosenModule T Y W) :
    ProperOvercomponentAlternatives E := by
  let := E.actionCentralizer_normal
  have h := P.residual_overgroup_hypothesis structural modules hr hw hY hKY.le
  have hn := P.proper_overcomponent_not_solvableSylowOvergroups
    structural modules hr hw hY hKY E.sylow_normalizes_component
  have hthree (e : (Y ⧸ pCore 2 Y) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
      False := hn (solvableSylow_of_core (SolvableSylowOvergroups.of_equiv e
        (Matrix.PSL3Two.solvableSylowOvergroups_specialLinear_of_card_two (by simp))))
  cases modules G T Y W h E with
  | linear n degree action =>
    rcases degree with rfl | degree
    · exact (hthree action.groupEquiv).elim
    · exact .linear n degree action
  | linearThreeExtension groupEquiv _ _ => exact (hthree groupEquiv).elim
  | linearFiveExterior groupEquiv dimension irreducible =>
    exact .linearFiveExterior groupEquiv dimension irreducible
  | alternating n lower upper action =>
    by_cases hs : n = 5 ∨ n = 6
    · exact (hn (solvableSylow_of_faithful_small h E n hs action.groupEquiv)).elim
    · exact .alternating n (by omega) action
  | alternatingSevenFour groupEquiv dimension =>
    exact .alternatingSevenFour groupEquiv dimension
  | g2 action =>
    exact (hn (solvableSylow_of_core (SolvableSylowOvergroups.of_equiv action.groupEquiv
      Atlas.G2.binaryDerived_solvableSylowOvergroups))).elim
  | tripleSix groupEquiv _ _ _ =>
    exact (hn (solvableSylow_of_core (SolvableSylowOvergroups.of_equiv groupEquiv
      solvableSylow_hexEven))).elim

/-- In the two seven-letter rows, the faithful marking gives the literal
central quotient required by the proper-branch setup. -/
theorem proper_overcomponent_seven_central_quotient
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    {Y W : Subgroup G} (hY : Y ∈ Chapter1.LStar G (T : Subgroup G))
    (hKY : P.K < Y) (E : ChosenModule T Y W)
    (e : letI := E.actionCentralizer_normal
      (Y ⧸ (centralizer (W : Set G)).subgroupOf Y) ≃* alternatingGroup (Fin 7)) :
    Nonempty (CentralQuotient Y ≃* alternatingGroup (Fin 7)) := by
  let := E.actionCentralizer_normal
  let := (P.residual_overgroup_hypothesis structural modules hr hw hY hKY.le).quasisimple
  let r := e.toMonoidHom.comp E.coreToFaithful
  have hr : Function.Surjective r := e.surjective.comp E.coreToFaithful_surjective
  have hk : r.ker = center (Y ⧸ pCore 2 Y) := by
    have hh := IsQuasisimple.comap_center_of_surjective r hr
    rw [alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 7)),
      MonoidHom.comap_bot] at hh
    exact hh
  let f := r.comp (QuotientGroup.mk' (pCore 2 Y))
  have hf : Function.Surjective f := hr.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = (center (Y ⧸ pCore 2 Y)).comap (QuotientGroup.mk' (pCore 2 Y)) := by
    change r.ker.comap (QuotientGroup.mk' (pCore 2 Y)) = _
    rw [hk]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
