module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.SixMoved
public import Theory.GroupAction.FixedQuotientCentralizer

/-!
# The literal natural quotient of the original A₆ moved subgroup

The B.5 moved-section coordinates identify U_K/C_U_K(K) with the natural
A₆ module. The map on actors is the original component projection followed
by the chosen natural marking. Neither a short group nor a two-core kernel
for that actor map is assumed.

Source: Aschbacher–Smith B.5.1 and 13.6.22, printed pp.99–103 and932.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
open ChapterB.QuasisimpleSource ComponentSelection SourceContainment
open LinearThree.CentralAction.ModuleAlternatives
open LinearThree.CentralAction
variable {G : Type*} [Group G]
variable (K L T : Subgroup G) (z v : G)
variable (hL : Tv T v ≤ normalizer (Lv L v : Set G))
variable (hz : Tv T v ≤ centralizer ({z} : Set G))
variable [IsElementaryAbelian 2 (WK K L T z v)]

noncomputable def six_quotientModel
    (hK : K ≤ Gv v)
    (s : MovedSection (wkRepresentation K L T z v hL hz)
      (plusImage K L T z v hL hz K))
    (e : ActionEquiv (s.action.comp (plusImage K L T z v hL hz K).subtype)
      (alternatingNatural 6)) :
    ConjugationQuotientModel K (UK K L T z v)
      (BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 6)) := by
  let c := movedEquivUK K L T z v hL hz s
  let q := s.central.toSubmodule.mkQ.toAddMonoidHom.toMultiplicative
  let f := e.linearEquiv.toAddEquiv.toMultiplicative
  refine {
    normalizes := K_normalizes_UK K L T z v hL hz
    actor := e.groupEquiv.toMonoidHom.comp (componentPlus K L T z v hK hL hz)
    quotient := f.toMonoidHom.comp (q.comp c.symm.toMonoidHom)
    surjective := f.surjective.comp ((Submodule.mkQ_surjective _).comp c.symm.surjective)
    kernel := ?_
    equivariant := ?_ }
  · ext u
    change f (q (c.symm u)) = 1 ↔ (u : G) ∈ centralizer (K : Set G)
    rw [map_eq_one_iff f f.injective]
    change s.central.toSubmodule.mkQ (c.symm u).toAdd = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact mem_sectionCentral_iff K L T z v hL hz hK s (c.symm u).toAdd
  · intro k u
    have hcu : c.symm ((UK K L T z v).normalizerMonoidHom
        ⟨k, K_normalizes_UK K L T z v hL hz k.property⟩ u) =
        Multiplicative.ofAdd (s.space.toRepresentation
          (componentPlus K L T z v hK hL hz k) (c.symm u).toAdd) := by
      apply c.injective
      rw [c.apply_symm_apply]
      apply Subtype.ext
      change (k : G) * (u : G) * (k : G)⁻¹ =
        ((wkRepresentation K L T z v hL hz
          (componentPlus K L T z v hK hL hz k) (c.symm u).toAdd.val).toMul : G)
      rw [componentPlus_apply, wkRepresentation_apply]
      rfl
    change f (q (c.symm _)) = _
    rw [hcu]
    apply Multiplicative.ofAdd.injective
    exact e.intertwines (componentPlus K L T z v hK hL hz k)
      (s.central.toSubmodule.mkQ (c.symm u).toAdd)

theorem six_quotientModel_actor_surjective
    (hK : K ≤ Gv v)
    (s : MovedSection (wkRepresentation K L T z v hL hz)
      (plusImage K L T z v hL hz K))
    (e : ActionEquiv (s.action.comp (plusImage K L T z v hL hz K).subtype)
      (alternatingNatural 6)) :
    Function.Surjective (six_quotientModel K L T z v hL hz hK s e).actor :=
  e.groupEquiv.surjective.comp (componentPlus_surjective K L T z v hK hL hz)

theorem six_quotientModel_of_actionData
    [(plusImage K L T z v hL hz K).Normal]
    (hK : K ≤ Gv v)
    (m : SixModels.ActionData (wkRepresentation K L T z v hL hz)
      (plusImage K L T z v hL hz K)) :
    ∃ a : ConjugationQuotientModel K (UK K L T z v)
      (BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 6)),
      Function.Surjective a.actor := by
  obtain ⟨e⟩ := m.natural
  let s := Classifier.liftSection m.component_le_offenders m.conclusion.sectionData
  let e' : ActionEquiv (s.action.comp (plusImage K L T z v hL hz K).subtype)
      (alternatingNatural 6) := {
    groupEquiv := (subgroupOfEquivOfLe m.component_le_offenders).symm.trans e.groupEquiv
    linearEquiv := e.linearEquiv
    intertwines := fun c w => e.intertwines ((subgroupOfEquivOfLe m.component_le_offenders).symm c) w }
  exact ⟨six_quotientModel K L T z v hL hz hK s e',
    six_quotientModel_actor_surjective K L T z v hL hz hK s e'⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
