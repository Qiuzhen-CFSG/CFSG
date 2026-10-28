module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.ClassifiedSections.Models
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.QuotientAction
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.HexacodeEven
public import Theory.Alternating.OddCentralCovers
public import Theory.Representation.Quotient

public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!
# Preserve the actual section in the quasisimple classification

Every clause of the original B.5.1 conclusion gives the group alternative
used in 15.3.49(l). In the triple-A₆ clause, the marked cubic center and
central quotient identify the concrete even hexacode group. Recognition of
its faithful irreducible six-dimensional action supplies an intertwiner;
the existing equivariant quotient comparison then retains the literal
source section I / C_I(L), with I in Irr⁺(L,V).

Source: Aschbacher–Smith, B.4.2(8), B.5.1(1), K.1.3, and 15.3.49(l),
combined manuscript of 1 March 2004, printed pp.86, 99, 453, and 1144.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels
open ComponentReduction ModelReduction BinaryModels ModelSieve
open ChapterB ChapterB.QuasisimpleSource
universe u v
variable {D : Type u} [Group D] [Finite D]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) (L : Subgroup D) [IsQuasisimple L]

/-- The source triple-cover row supplies the actual equivariant hexacode section. -/
theorem hexSection_of_tripleSix
    (s : MovedSection ρ L) (hI : IsIrrPlus ρ L s.space.toSubmodule)
    (hf : Function.Injective s.action)
    (hi : IsIrreducible (s.action.comp L.subtype))
    (a : SourceInduction.ProjectiveLine.TripleSixAction s.action L) :
    Nonempty (HexSection ρ L) := by
  have hc : Nat.card (center L) = 3 := by
    rw [Nat.card_congr a.centerEquiv.toEquiv]
    simp
  obtain ⟨q⟩ := GLS3.Chapter5.OddCentralCovers.triple_six_equiv_hexacode a.quotientEquiv hc
  let τ := (s.action.comp L.subtype).comp q.symm.toMonoidHom
  have ht : Function.Injective τ :=
    (hf.comp L.subtype_injective).comp q.symm.injective
  have hir : IsIrreducible τ :=
    (irreducible_comp_surjective_iff q.symm.toMonoidHom q.symm.surjective _).mpr hi
  obtain ⟨e⟩ := ChapterK.Alternating.EvenRecognition.exists_actionEquiv τ ht hir a.dimension
  let a' : ActionEquiv (s.action.comp L.subtype) Hexacode.evenAction := {
    groupEquiv := q.trans e.groupEquiv
    linearEquiv := e.linearEquiv
    intertwines := by
      intro l v
      have he := e.intertwines (q l) v
      simpa only [τ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        q.symm_apply_apply, MulEquiv.trans_apply] using he }
  let b := IrreducibleBranch.centralQuotientEquiv s hI
  refine ⟨{
    space := s.space.toSubmodule
    stable := hI.choose
    full := hI.choose_spec.1
    irreducible := hI.choose_spec.2
    groupEquiv := a'.groupEquiv
    moduleEquiv := b.symm.toLinearEquiv.trans a'.linearEquiv
    equivariant := ?_ }⟩
  intro g v
  exact (congrArg a'.linearEquiv (b.symm.isIntertwining g v)).trans
    (a'.intertwines g (b.symm v))

private noncomputable def alternatingFiveEquiv :
    alternatingGroup (Fin 5) ≃* Matrix.SpecialLinearGroup (Fin 2) BinaryField.four.Carrier :=
  (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K := BinaryField.four.Carrier) (by
      change Nat.card (GaloisField 2 2) = 4
      rw [GaloisField.card 2 2 (by decide)]
      decide)).some.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot).trans
        QuotientGroup.quotientBot)

private noncomputable def alternatingSixEquiv :
    alternatingGroup (Fin 6) ≃* commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) := by
  let e := Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
  exact ((e.subgroupMap _).trans (MulEquiv.subgroupCongr (by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
    exact alternatingGroup.commutator_perm_eq (by norm_num)))).symm

private noncomputable def alternatingEightEquiv :
    alternatingGroup (Fin 8) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
  Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans Atlas.Order20160A8.sl4TwoEquivPSL.symm

private noncomputable def derivedEquiv {X : Type*} [Group X] [Group.IsPerfect X] :
    X ≃* commutator X :=
  topEquiv.symm.trans (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top.symm)

/-- Exhaust the original quasisimple source conclusion, preserving its
literal Irr⁺ section and action mark in the exceptional triple-cover case. -/
theorem componentSection_of_quasisimple_source
    (c : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ L) :
    ComponentSectionAlternative ρ L := by
  cases c.clause_one with
  | irreducible hI hf hi row _ =>
    cases row with
    | linearTwo F _ e _ _ =>
      exact componentSection_linearTwo ρ L F e.groupEquiv
    | linearThree F _ e _ =>
      exact componentSection_linearThree ρ L F e.groupEquiv
    | symplectic F _ _ e _ =>
      let : Group.IsPerfect (Matrix.symplecticGroup (Fin 2) F.Carrier) :=
        Group.IsPerfect.ofSurjective (f := e.groupEquiv.toMonoidHom) e.groupEquiv.surjective
      exact componentSection_symplectic ρ L F (e.groupEquiv.trans derivedEquiv)
    | symplecticTwo e _ =>
      exact componentSection_symplectic ρ L BinaryField.two e.subgroupEquiv
    | g2 F _ _ e _ _ =>
      let : Group.IsPerfect (Atlas.G2.Model F.Carrier) :=
        Group.IsPerfect.ofSurjective (f := e.groupEquiv.toMonoidHom) e.groupEquiv.surjective
      exact componentSection_g2 ρ L F (e.groupEquiv.trans derivedEquiv)
    | g2Two e _ _ =>
      exact componentSection_g2 ρ L BinaryField.two e.subgroupEquiv
    | symmetric n hn e _ _ =>
      rcases hn with rfl | rfl
      · exact componentSection_linearTwo ρ L BinaryField.four
          (e.subgroupEquiv.trans alternatingFiveEquiv)
      · exact .alternating_seven ⟨e.subgroupEquiv⟩
    | alternatingSix _ e _ _ =>
      exact componentSection_symplectic ρ L BinaryField.two
        (e.groupEquiv.trans alternatingSixEquiv)
    | alternatingSeven _ _ e _ _ _ => exact .alternating_seven ⟨e⟩
    | tripleSix _ a _ =>
      exact .triple_cover (hexSection_of_tripleSix ρ L c.sectionData hI hf hi a)
    | binaryLinear n hn _ e _ =>
      exact componentSection_binaryLinear ρ L n hn e.groupEquiv
    | orthogonalSix _ _ e _ _ =>
      exact componentSection_binaryLinear ρ L 4 (Or.inl rfl)
        (e.groupEquiv.trans alternatingEightEquiv)
    | symmetricEight _ e _ =>
      exact componentSection_binaryLinear ρ L 4 (Or.inl rfl)
        (e.subgroupEquiv.trans alternatingEightEquiv)
    | exteriorFive _ _ e _ _ _ =>
      exact componentSection_binaryLinear ρ L 5 (Or.inr rfl) e
  | doubleThree F _ e _ _ =>
    exact componentSection_linearThree ρ L F e.groupEquiv
  | naturalDual n hn _ h =>
    obtain ⟨e⟩ := h
    exact componentSection_binaryLinear ρ L n hn e.groupEquiv
  | repeatedNatural n _ hn _ _ _ h =>
    obtain ⟨e⟩ := h
    exact componentSection_binaryLinear ρ L n hn e.groupEquiv

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels
