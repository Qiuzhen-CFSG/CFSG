module
public import CFSG.Quasithin.ChapterB.Section04.SmallRatioClassification.Sporadic.Marked
public import CFSG.Quasithin.ChapterB.Section04.SmallRatioClassification.Sporadic.Groups
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource

/-!
# The sporadic branch for the original chief action in 13.5.21

The actual chief action has a marked involution moving at most two binary
dimensions. The whole-action Mathieu markings and the native degree bounds
exclude every entry of the eleven-carrier Theorem C sporadic list. This
supplies the full B.4.2-or-Table-B.4.5 conclusion for that source action,
without replacing either table or assuming a general B.4.5 classifier.

The hypotheses preserve the original ambient action, quasisimple generalized
Fitting subgroup and literal central quotient. In particular the marked
involution may lie outside the component. The unrestricted M22 code and
triple-cover rows remain in Table B.4.5; the extra source involution excludes
them only in this application.

Source: Aschbacher--Smith B.4.5, K.4 and 13.5.21, printed pp.87,457--460,923--924.
-/

public section
namespace CFSG.Quasithin.ChapterB.SmallRatioClassification
open Representation Representation.BinaryOffender Subgroup Theory.GroupTheory
open ChapterK.SporadicCatalogue
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- All eleven sporadic carriers are impossible for the original action with its
actual marked involution of displacement at most two. -/
theorem sporadic_false_of_marked_involution
    (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hm : ChapterA.Section02.IsTheoremCSporadicModel (L ⧸ center L))
    (t : G) (ht : orderOf t = 2) (hd : fixedCodim ρ (zpowers t) ≤ 2) : False := by
  rcases hm with ⟨name,hne,he⟩ | he
  · cases name with
    | m11 => exact Sporadic.m11_false h he t ht hd
    | m12 => have hlo := Sporadic.m12_involution_ge_four h he t ht; omega
    | m22 => have hlo := Sporadic.m22_involution_ge_three h he t ht; omega
    | m23 => exact (not_lt_of_ge hd) (Sporadic.m23_involution_gt_two h he t ht)
    | m24 => exact Sporadic.m24_false h he t ht hd
    | j2 => exact Sporadic.j2_false h he t ht hd
    | hs => exact Sporadic.hs_false h he t ht hd
    | j3 => exact hne rfl
    | j4 => exact Sporadic.other_cubic_false h (Or.inr (Or.inl he))
    | he => exact Sporadic.other_cubic_false h (Or.inr (Or.inr (Or.inl he)))
    | ru => exact Sporadic.other_cubic_false h (Or.inr (Or.inr (Or.inr he)))
  · exact Sporadic.other_cubic_false h (Or.inl he)

/-- The literal full-table consumer for the marked source chief action. Its
stronger displacement datum makes a separate quadratic-ratio premise unnecessary. -/
theorem sporadic_case_of_marked_involution
    (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hm : ChapterA.Section02.IsTheoremCSporadicModel (L ⧸ center L))
    (t : G) (ht : orderOf t = 2) (hd : fixedCodim ρ (zpowers t) ≤ 2) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) ∨
      Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource.TableB45 ρ L :=
  (sporadic_false_of_marked_involution h hm t ht hd).elim

/-- The same literal consumer in displacement-range coordinates supplied by a chief section. -/
theorem sporadic_case_of_displacement_rank
    (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hm : ChapterA.Section02.IsTheoremCSporadicModel (L ⧸ center L))
    (t : G) (ht : orderOf t = 2)
    (hd : Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) ≤ 2) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) ∨
      Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource.TableB45 ρ L := by
  apply sporadic_case_of_marked_involution h hm t ht
  simpa only [fixedCodim_zpowers_eq_displacement_rank] using hd

end CFSG.Quasithin.ChapterB.SmallRatioClassification
