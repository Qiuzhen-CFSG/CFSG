module
public import Theory.SpecificGroups.SporadicOneCentralizer
public import Theory.Mathieu.InvolutionCentralizerOdd
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.InvolutionCentralizerOdd
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.OneCentralizer
public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.NonrootSocle

/-!+# The sporadic rows of the G.4.1 one-centralizer inspection

Every sporadic in the literal Theorem C list has an odd divisor in each
involution centralizer. This dispatcher retains the actual carrier equivalence
and the specified involution, without any Sylow-centrality or all-centralizer
hypothesis. The final application restricts the ambient two-group centralizer
of one c₂ element to its original subgroup of Sp₄(F).

Source: Aschbacher--Smith G.4.1, printed p.342, the inspection of Theorem C
involution centralizers. This discharges the entire sporadic family in that
inspection; the other source families remain separate.
-/

public section
open Subgroup Theory.GroupTheory.CentralizerSmallKernelTransport
namespace CFSG.Quasithin.ChapterA.Section02
open ClassificationModels

private theorem named_not_two_centralizer (name : SporadicName) (hn : name ≠ .j3)
    (i : name.Carrier) (hi : orderOf i = 2) :
    ¬ IsPGroup 2 (centralizer ({i} : Set name.Carrier)) := by
  cases name with
  | m11 => exact Sporadic.Mathieu.m11_involution_centralizer_not_isPGroup i hi
  | m12 => exact Sporadic.Mathieu.m12_involution_centralizer_not_isPGroup i hi
  | m22 => exact Sporadic.Mathieu.m22_involution_centralizer_not_isPGroup i hi
  | m23 => exact Sporadic.Mathieu.m23_involution_centralizer_not_isPGroup i hi
  | m24 => exact Sporadic.Mathieu.m24_involution_centralizer_not_isPGroup i hi
  | j2 => exact Sporadic.LeechRelated.J2.not_isPGroup_involution_centralizer i hi
  | j3 => exact (hn rfl).elim
  | j4 => exact Janko4.not_isPGroup_involution_centralizer i hi
  | hs => exact Sporadic.LeechRelated.HS.not_isPGroup_involution_centralizer i hi
  | he => exact Held.not_isPGroup_involution_centralizer i hi
  | ru => exact Rudvalis.not_isPGroup_involution_centralizer i hi

/-- The actual Theorem C sporadic list has no involution with a two-group centralizer. -/
theorem IsTheoremCSporadicModel.not_isPGroup_centralizer
    {G : Type*} [Group G] (h : IsTheoremCSporadicModel G)
    (i : G) (hi : orderOf i = 2) : ¬ IsPGroup 2 (centralizer ({i} : Set G)) := by
  intro hp
  rcases h with h | h
  · obtain ⟨name, hn, ⟨e⟩⟩ := h
    exact named_not_two_centralizer name hn (e i) ((e.orderOf_eq i).trans hi)
      (hp.of_equiv (centralizerEquiv e i))
  · obtain ⟨e⟩ := h
    exact Janko1.not_isPGroup_involution_centralizer (e i) ((e.orderOf_eq i).trans hi)
      (hp.of_equiv (centralizerEquiv e i))

end CFSG.Quasithin.ChapterA.Section02

namespace CFSG.Quasithin.ChapterG.Section04
open Theory.SpecificGroups.SymplecticFour
open ChapterA.Section02

/-- A literal subgroup containing the specified c₂ involution cannot be a
sporadic Theorem C model. The ambient centralizer supplies the only local premise. -/
theorem not_sporadic_of_one_isC2
    {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (N : Subgroup (Sp F))
    (i : N) (hi : InvolutionTypes.IsC2 (i : Sp F)) :
    ¬ IsTheoremCSporadicModel N := by
  intro h
  have hp := TwoConjugate.isPGroup_centralizer_of_isC2 hF (i : Sp F) hi
  have he : centralizer ({i} : Set N) =
      (centralizer ({(i : Sp F)} : Set (Sp F))).comap N.subtype := by
    ext x
    rw [mem_centralizer_singleton_iff, mem_comap,
      mem_centralizer_singleton_iff, ← Subtype.coe_inj]
    rfl
  have hpN : IsPGroup 2 (centralizer ({i} : Set N)) := by
    rw [he]
    exact hp.comap_subtype
  exact h.not_isPGroup_centralizer i ((orderOf_coe i).symm.trans hi.1) hpN

end CFSG.Quasithin.ChapterG.Section04
