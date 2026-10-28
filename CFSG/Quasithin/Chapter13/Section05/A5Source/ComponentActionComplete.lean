module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.ComponentAction
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction.ConjugatePairs
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction.Commutator
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction

/-!
# The unconditional original A₅ component action

Original F.9.5(2) and(6.i) now supply both universal source inputs.
The original A₅ context therefore constructs the faithful action with fixed
codimension two and every S₃ conjugate pair without a recognition premise.
Source: Aschbacher–Smith13.5.20, printed p.923.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
open ComponentReduction.Fitting.SourceAction Representation.BinaryOffender
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
include d hA312 hH hU

/-- The original component action, with both F.9 source inputs proved. -/
theorem source_component_action_complete :
    let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
    let hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
    let : (D.V₁.subgroupOf D.UH).Normal := point_normal_in_UH hf
    let : IsElementaryAbelian 2 (Quotient (D := D)) := quotient_elementary hf
    Function.Injective (representation hf) ∧
      fixedCodim (representation hf) (Source.starImage H V) = 2 ∧
      ∀ x : Source.Hstar H, ¬ IsPGroup 2 (Source.starImage H V ⊔
        (Source.starImage H V).map (MulAut.conj x).toMonoidHom : Subgroup (Source.Hstar H)) →
        Nonempty ((Source.starImage H V ⊔
          (Source.starImage H V).map (MulAut.conj x).toMonoidHom : Subgroup (Source.Hstar H)) ≃*
          Equiv.Perm (Fin 3)) :=
  source_component_action d hA312 hH hU source_F95Six

end CFSG.Quasithin.Chapter13.Section05.A5Source
