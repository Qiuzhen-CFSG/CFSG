module
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.FourShortTransport
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.MarkedAction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.Centralizers

/-!
# Ambient common centralizers of the prepared unitary short root

Use the original reduced comparison, retaining its entire overlap, to mark
an actual short root t. In N_G(K)=K D, where K=O²(H) and
D=N_G(L)∩N_G(K), an element centralizing t has its K-factor carrying t
back into O₂(L). The native short-root transporter theorem therefore puts
that factor in the reduced overlap. Hence C_{N_G(K)}(t)≤N_G(L).

The proved ambient long-root centralizer bound then gives
C_G(t)∩C_G(z)≤N_G(L) for every involution z in the original center of K.
This is a genuine ambient common-centralizer statement, derived from the
prepared input without realization, fusion or centralizer callbacks. It
retains both orientations, the degree-two comparisons and q=4. The marked
root and comparison are returned together for subsequent fixed-coset work.

Source: Aschbacher–Smith F.4.42, printed p.295 of `refs/quasithin.pdf`.
Full ambient short-centralizer containment, quotient unique fixed cosets,
outer transfer and the order comparison remain further obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
open ChapterF.UnitarySource.FourPlacement
namespace UnitarySource
variable {G : Type*} [Group G] [Finite G]
private theorem reverse_comparison (P : Fin 2 → Subgroup G) (L R : Subgroup G)
    (hL : faithfulLocal L)
    (hr : ∀ i, (solvableResidual (P i)).map (P i).subtype = ![L,R] i)
    (m : ℕ) (hm : 1 ≤ m) (hm' : 1 < m)
    (b : R ≃* PointLocal.ProjectiveLocal m hm)
    (hz : (center (pCore 2 R)).map (pCore 2 R).subtype ≤ center R)
    (he : Nonempty (RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (P 0) (P 0 ⊓ P 1) (P 1) inf_le_left inf_le_right)
        (amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (P 0) (P 0 ⊓ P 1) (P 1) inf_le_left inf_le_right)
        (amalgam m hm).reverse)) :
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (P 0) (P 0 ⊓ P 1) (P 1) inf_le_left inf_le_right)
      (amalgam m hm).reverse) := by
  rcases he with he | he <;> obtain ⟨e⟩ := he
  · let a : solvableResidual (P 0) ≃* L :=
      ((solvableResidual (P 0)).equivMapOfInjective (P 0).subtype
        (P 0).subtype_injective).trans (MulEquiv.subgroupCongr (hr 0))
    let c : solvableResidual (pointParabolic m hm) ≃* PointLocal.ProjectiveLocal m hm :=
      ((solvableResidual (pointParabolic m hm)).equivMapOfInjective
        (pointParabolic m hm).subtype (pointParabolic m hm).subtype_injective).trans
          (MulEquiv.subgroupCongr (PointLocal.pointParabolic_solvableResidual m hm hm'))
    exact (faithful_not_core_center_central hL
      (a.symm.trans (e.left.solvableResidualEquiv.trans (c.trans b.symm))) hz).elim
  · exact ⟨e⟩
end UnitarySource

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The actual short root selected through the whole reduced amalgam has
its centralizer in the opposite full normalizer contained in N_G(L).
The same mark therefore has the ambient common-centralizer bound with
every long root in the original right-residual center. -/
theorem Preparation.unitary_short_root_common_centralizers
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    1 < m ∧ n = 2*m ∧
    ∃ e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] ((T : Subgroup G) ⊓ L)) (amalgam m hm).reverse,
      let t := (ChapterF.UnitarySource.FourShortTransport.sourceShort m hm e).val
      t ∈ L.pCoreIn 2 ∧ orderOf t = 2 ∧
      normalizer (residual H : Set G) ⊓ centralizer ({t} : Set G) ≤ normalizer (L : Set G) ∧
      ∀ z ∈ (center (residual H)).map (residual H).subtype, orderOf z = 2 →
        centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨hm',hn,he⟩ := d.unitary_reduced_native_comparison h hH.1.1.2 hp m hm hc
  obtain ⟨_,_,_,⟨b⟩,_⟩ := hc.elim
    (d.unitary_local_structure h hH.1.1.2 hp m hm)
    (d.unitaryExtension_local_structure h hH.1.1.2 hp m hm)
  let P := ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L)
  have hr : ∀ i, (solvableResidual (P i)).map (P i).subtype = ![L,residual H] i :=
    d.reduced_parabolic_residuals h hH.1.1.2 hp
      (hc.elim (fun he => .unitary m hm he) (fun he => .unitaryExtension m hm he))
  have hz := (d.unitary_core_structure h hH.1.1.2 hp m hm hc).2.2.2.2.2.2.2.2.2
  obtain ⟨e⟩ := UnitarySource.reverse_comparison P L (residual H) h.local_mem.2 hr m hm hm' b hz he
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
  refine ⟨hm',hn,e,?_,ChapterF.UnitarySource.FourShortTransport.sourceShort_order m hm e,hbound,?_⟩
  · rw [←hcore]
    exact ChapterF.UnitarySource.FourShortTransport.sourceShort_mem_core m hm e
  · intro z hz hz2 g hg
    exact hbound ⟨d.unitary_central_involution_centralizers h hH hp m hm hc 1 z hz hz2 hg.2,hg.1⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
