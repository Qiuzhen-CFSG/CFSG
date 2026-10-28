module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Zero.Bounds
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.ChapterE.Section06.Basic

/-!
# The original exterior module satisfies E.6.1

The original local uniqueness theorem gives the maximal two-local group
and its uniqueness clause. The marked Sylow action makes V normal in T,
while C_T(V)=O₂(LT) supplies the second normalizer in E.6.1(3).
The TI clause is exactly the preceding structural source result.

Structural1222At remains the earlier input owned by qt-d-1222-source;
no numerical bound or escaping-centralizer conclusion is assumed.
Source: Aschbacher--Smith, 12.2.6 and 12.5.6, using E.6.1.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 ChapterE.Section06
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- E.6.1 on the original V and M=N_G(L), retaining only the earlier TI input. -/
theorem hypothesisE61
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    HypothesisE61 KnownSimple.IsKnownSimple T s.marking.M V := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have he : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L T L le_rfl
      D.sylow_normalizes_component) (le_componentOrbit L T)
  have hmax := hu.normalizer_maximal
  rw [he] at hmax
  refine ⟨h.simpleQTKE, hmax, D.sylow_normalizes_component,
    D.ne_bot, D.elementary, D.le_sylow,
    (normal_subgroupOf_iff_le_normalizer D.le_sylow).mpr
      (le_sup_right.trans s.normalizes), ((structural L h).2.2 V D).2.2.1, ?_⟩
  intro N hN hle
  change N = normalizer (L : Set G)
  rw [← he]
  apply hu.normalizer_unique N hN
  apply le_trans ?_ hle
  refine le_inf (le_inf (sup_le L.le_normalizer D.sylow_normalizes_component)
    s.normalizes) ?_
  change L ⊔ (T : Subgroup G) ≤ normalizer
    (((T : Subgroup G) ⊓ centralizer (V : Set G) : Subgroup G) : Set G)
  rw [exterior_sylow_centralizer_eq_core s h]
  exact (L ⊔ (T : Subgroup G)).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
