module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.At.OriginalSize
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At.Recognition
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.SourceAt

/-!
# The two genuine local types on the original nonabelian flag

Splitting the center of the actual closure gives either the original
G₂(3)-type configuration, with H equal to the point normalizer and M equal
to L, or HS1--HS2 on the original seed V and flag point. The large
extraspecial alternative and both HS local source structures are supplied
by their proved source theorems.

The second theorem applies the completed large-three-core recognition. Its
only remaining alternatives are the original strongly-three-embedded point
normalizer and the actual HS local type. This does not assert either final
recognition theorem. Earlier source implications retain their same-G,T
producers. Source: Aschbacher--Smith 14.4.14, printed p.1012; I.4.5 and
I.4.8, printed pp.417--418.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section08.SourceCases
open Subgroup Theory.GroupTheory ClassificationModels
open scoped IsMulCommutative
open Chapter12.Section02 Chapter12.Section08
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Section04 Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (earlier : Earlier1332CaseOneAt T)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
include d h earlier structural alternatives classification hne

/-- Both local recognition inputs are constructed on the original flag.
No order, local-data, overgroup, or recognition hypothesis remains. -/
theorem nonabelian_local_types_at :
    (∃ c : DimensionFour.G2ThreeConfiguration G, c.H = F.H ∧ c.M = L) ∨
      ∃ z : G, F.Vi 1 = zpowers z ∧ HigmanSims.TypeAt z V := by
  by_cases hZ : F.ZU = F.Vi 1
  · have hc := CaseOneLarge.source_extraspecial_order_eq_thirtyTwo_at
      d h earlier structural alternatives classification F hne hZ
    exact Or.inl (CaseOneDimensionFour.At.source_configuration_on
      d h structural alternatives F hne hZ hc)
  · exact Or.inr (CaseOneHS.type_of_source_at d earlier h.quotient_model
      h.chosen structural alternatives F hne classification hZ)

/-- The completed G₂(3) branch leaves precisely strong three-embedding at
the original point normalizer or the original HS local type. -/
theorem nonabelian_recognition_or_remaining_at :
    IsG2At G 3 ∨
      (F.H ≠ ⊤ ∧ 3 ∣ Nat.card F.H ∧
        ∀ a : G, a ∉ F.H →
          ¬ 3 ∣ Nat.card (F.H ⊓ F.H.map (MulAut.conj a).toMonoidHom : Subgroup G)) ∨
      ∃ z : G, F.Vi 1 = zpowers z ∧ HigmanSims.TypeAt z V := by
  rcases nonabelian_local_types_at d h earlier structural alternatives classification F hne with
    ⟨c, hcH, _⟩ | hs
  · rcases ChapterI.Section04To05.G2Recognition.recognition_or_strong_three c with hs | hr
    · exact Or.inr (Or.inl (by simpa only [hcH] using hs))
    · exact Or.inl ⟨ZMod 3, inferInstance, inferInstance, Nat.card_zmod 3, hr⟩
  · exact Or.inr (Or.inr hs)

end CFSG.Quasithin.Chapter14.Section08.SourceCases
