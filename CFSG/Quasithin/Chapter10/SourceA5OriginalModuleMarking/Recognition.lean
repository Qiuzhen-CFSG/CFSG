module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.RankOneRecognition.FieldFour

/-!
# Recognition on the literal original moved central quotient

The original A₅ quotient acts faithfully on [V,L]/C_[V,L](L), with the
original quotient map as coordinates. If this actual action is irreducible,
the unrestricted binary A₅ classifier gives natural SL₂(4) or deleted
permutation coordinates and dimension four. No numerical or escaping
normalizer premise is needed.

Irreducibility is the remaining genuine source3.2.6 input. The deleted
quotient alternative here does not yet identify the whole moved factor;
that requires the projective central-cover argument of I.1.5–6.
Source: Aschbacher–Smith,10.1.1, printed p.741.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))

local instance originalQuotientFieldFourAlgebra :
    Algebra (ZMod 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1) :=
  ZMod.algebra _ 2

local instance originalQuotientMovedElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- The actual original A₅ representation on the literal moved central quotient. -/
def originalMovedQuotientAction :
    Representation (ZMod 2) (alternatingGroup (Fin 5))
      (Additive ((⁅D.fullModule,L⁆ : Subgroup G) ⧸
        (sourceMovedFixed D).subgroupOf ⁅D.fullModule,L⁆)) :=
  (source_a5_original_moved_quotient_action D e).choose

/-- The original inclusions and quotient coordinates for this representation. -/
def originalMovedQuotientSection :
    Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      ((originalMovedQuotientAction D e).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) :=
  (source_a5_original_moved_quotient_action D e).choose_spec.choose

theorem originalMovedQuotientAction_faithful :
    Function.Injective (originalMovedQuotientAction D e) :=
  (source_a5_original_moved_quotient_action D e).choose_spec.choose_spec.1

theorem originalMovedQuotientSection_coordinates (w : (⁅D.fullModule,L⁆ : Subgroup G)) :
    ((originalMovedQuotientSection D e).coordinates w).toAdd =
      Additive.ofMul (QuotientGroup.mk'
        ((sourceMovedFixed D).subgroupOf ⁅D.fullModule,L⁆) w) :=
  (source_a5_original_moved_quotient_action D e).choose_spec.choose_spec.2 w

/-- The only missing source premise for quotient recognition is irreducibility
of this exact action, not a chosen model or a numerical bound. -/
theorem source_a5_original_quotient_alternatives_of_irreducible
    (hi : (originalMovedQuotientAction D e).IsIrreducible) :
    let Q := Additive ((⁅D.fullModule,L⁆ : Subgroup G) ⧸
      (sourceMovedFixed D).subgroupOf ⁅D.fullModule,L⁆)
    let ρ := originalMovedQuotientAction D e
    Module.finrank (ZMod 2) Q = 4 ∧
      ((∃ f : alternatingGroup (Fin 5) ≃*
          SL(2,Representation.OrthogonalFourMinus.FiniteModel.Field 1),
        Nonempty (ρ.Equiv (Representation.SL2.BinarySmall.natural.comp f.toMonoidHom))) ∨
      ∃ f : alternatingGroup (Fin 5) ≃* alternatingGroup (Fin 5),
        Nonempty (ρ.Equiv
          (Representation.OrthogonalFourMinus.AlternatingFive.alternatingRepresentation.comp
            f.toMonoidHom))) := by
  let := hi
  apply ChapterG.Section09.DefiningCharacteristic.alternating_five_irreducible_action_alternatives
    (originalMovedQuotientAction D e) (MulEquiv.refl _)
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨g,hg⟩ := exists_ne (1 : alternatingGroup (Fin 5))
  refine ⟨g,fun h => hg ?_⟩
  exact originalMovedQuotientAction_faithful D e
    (h.trans (originalMovedQuotientAction D e).map_one.symm)

end CFSG.Quasithin.Chapter10
