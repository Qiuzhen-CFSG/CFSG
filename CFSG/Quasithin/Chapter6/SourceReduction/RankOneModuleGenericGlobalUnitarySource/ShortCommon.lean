module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.ShortTransport

/-!
# Common centralizers for a specified unitary comparison

Retain the supplied whole reduced comparison when choosing the short root.
The native opposite-centralizer bound and the actual full-normalizer
product give C_{N_G(K)}(t) ≤ N_G(L). Ambient long-root containment then
bounds every common centralizer with the original right-center roots.
This form lets the F.4.42 proof use the very comparison defining the
full-normalizer extension, without changing its marks.

Source: Aschbacher–Smith F.4.42, printed p.295.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
open ChapterF.UnitarySource.FourPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The common-centralizer bound uses the specified overlap and short-root mark. -/
theorem Preparation.unitary_short_common_centralizers_at
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] ((T : Subgroup G) ⊓ L)) (amalgam m hm).reverse) :
      let t := (ChapterF.UnitarySource.FourShortTransport.sourceShort m hm e).val
      t ∈ L.pCoreIn 2 ∧ orderOf t = 2 ∧
      normalizer (residual H : Set G) ⊓ centralizer ({t} : Set G) ≤ normalizer (L : Set G) ∧
      ∀ z ∈ (center (residual H)).map (residual H).subtype, orderOf z = 2 →
        centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) ≤ normalizer (L : Set G) := by
  let P := ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L)
  have hr : ∀ i, (solvableResidual (P i)).map (P i).subtype = ![L,residual H] i :=
    d.reduced_parabolic_residuals h hH.1.1.2 hp
      (hc.elim (.unitary m hm) (.unitaryExtension m hm))
  have hPN (i : Fin 2) : P i ≤ normalizer (![L,residual H] i : Set G) := by
    rw [←hr i]
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      (solvableResidual (P i)).le_normalizer_map (P i).subtype
  have hLP : L ≤ P 0 := le_sup_left.trans le_sup_left
  have hcore : (P 0).pCoreIn 2 = L.pCoreIn 2 := le_antisymm
    (plane_comparison_core_le_residual_core m hm (P 0) L e.left (hr 0))
    (pCoreIn_mono_of_normalizes hLP (hPN 0))
  have hNQ : normalizer (L : Set G) ≤ normalizer ((P 0).pCoreIn 2 : Set G) := by
    rw [hcore]
    exact normalizer_le_normalizer_characteristic_image L (pCore 2 L)
  have hloc := d.unitary_normalizer_local_conditions h hH hp m hm hc
  have hbound := ChapterF.UnitarySource.FourShortTransport.sourceShort_opposite_centralizer
    m hm e (normalizer (L : Set G)) (normalizer (residual H : Set G)) (hPN 0) hNQ (by
      intro g hg
      obtain ⟨k,hk,b,hb,he⟩ := hloc.factor_right g hg
      exact ⟨k,(show residual H ≤ P 1 from le_sup_left.trans le_sup_left) hk,b,hb.1,he⟩)
  refine ⟨?_,ChapterF.UnitarySource.FourShortTransport.sourceShort_order m hm e,hbound,?_⟩
  · rw [←hcore]
    exact ChapterF.UnitarySource.FourShortTransport.sourceShort_mem_core m hm e
  · intro z hz hz2 g hg
    exact hbound ⟨d.unitary_central_involution_centralizers h hH hp m hm hc 1 z hz hz2 hg.2,hg.1⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
