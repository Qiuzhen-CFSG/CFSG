module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsIntersectionSource
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsSingularSource
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.IntersectingPairs

/-!
# Original singular cores in the hypothetical HS branch

The actual returned pair supplies a singular point centralized by the
unchanged full Sylow subgroup. The independent original intersection bound
now permits the F.9 application in its literal centralizer. In particular,
its polar hyperplane lies in the actual two-core. The original A8 action
transports this statement to every nonzero singular point.

These consequences do not assume nonsingular centralizer control or the
later abelianness of the whole conjugate span. The final HS exclusion
remains separate.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original escaping singular centralizer satisfies the actual F.9
hypothesis, and its full polar hyperplane lies in its intrinsic two-core. -/
theorem SourceHypothesis.exists_original_hs_singular_point_core
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ hZ : ZV L V = ⊥, ∃ z : V, z ≠ 1 ∧ ¬ D.Nonsingular z ∧
      (T : Subgroup G) ≤ Gv (z : G) ∧ ¬ Gv (z : G) ≤ M L ∧
      (D.fullSetup hZ T z).Gz ∈ (D.fullSetup hZ T z).Hz ∧
      ((D.fullSetup hZ T z).f9 (Gv (z : G))).Hypothesis ∧
      (D.fullSetup hZ T z).V₅ ≤ (Gv (z : G)).pCoreIn 2 := by
  obtain ⟨hZ,z,hz,hs,hTz,hout,_,hHz⟩ :=
    H.exists_original_hs_singular_centralizer D hTV hTI v hv he
  have hbound := H.original_hs_conjugate_intersection_bound D hTV hTI v hv he
  have hn : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G) := by
    change (T : Subgroup G) ≤ normalizer (zpowers (z : G) : Set G)
    apply hTz.trans
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    rw [zpowers_eq_closure,centralizer_closure]
    rfl
  have hf := H.original_f9_of_earlier_geometry D hZ z hz hTV hn hbound hHz
  have hGz : (D.fullSetup hZ T z).Gz = Gv (z : G) := (D.fullSetup hZ T z).Gz_eq
  rw [hGz] at hf
  refine ⟨hZ,z,hz,hs,hTz,hout,hHz,hf,?_⟩
  exact (le_conjugateSpanBy _ _).trans hf.UH_le_QH

/-- Every original nonzero singular polar hyperplane lies in the actual
point centralizer two-core in the hypothetical HS contrary branch. -/
theorem SourceHypothesis.original_hs_singular_perpendicular_core
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ hZ : ZV L V = ⊥, ∀ w : V, w ≠ 1 → ¬ D.Nonsingular w →
      (D.fullSetup hZ T w).V₅ ≤ (Gv (w : G)).pCoreIn 2 := by
  obtain ⟨hZ,z,hz,_,hTz,hout,_,_⟩ :=
    H.exists_original_hs_singular_point_core D hTV hTI v hv he
  have hn : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G) := by
    change (T : Subgroup G) ≤ normalizer (zpowers (z : G) : Set G)
    apply hTz.trans
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    rw [zpowers_eq_closure,centralizer_closure]
    rfl
  refine ⟨hZ,?_⟩
  intro w hw hsw
  exact H.original_singular_perpendicular_core D hZ z hz hTV hn
    (H.original_hs_conjugate_intersection_bound D hTV hTI v hv he) (by rwa [(D.fullSetup hZ T z).Gz_eq]) w hw hsw

end CFSG.Quasithin.Chapter12.Section06
