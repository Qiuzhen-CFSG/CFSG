module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Selection
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Residual
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.SourceInterface

/-!
# From cubic exchanged planes to the common source interface

Once the earlier marker has prime three, its faithful residual calculation
identifies the cubic moved plane. The residual intersection proves escape
from M_Z, and exchanging the planes proves noncentrality by the actual
rank-two normalizer argument. Thus the finite action producer need only
construct its original planes and their Sylow action, for either size.

Source: Aschbacher--Smith 15.1.24--25, printed pp.1101--1102.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The geometric data still needed from the original finite action.
There is no component action, cubic escape, or noncentrality assumption. -/
structure ExchangedPlaneGeometry (d : CaseIComponentData T M Mc V) : Prop where
  sizes :
    (d.row = .four ∧ Nat.card d.Z1 = 2 ∧
      Nat.card d.nineFixedPlane = 4 ∧ Nat.card d.nineMovingPlane = 4) ∨
    (d.row = .six ∧ Nat.card d.Z1 = 4 ∧
      Nat.card d.nineFixedPlane = 16 ∧ Nat.card d.nineMovingPlane = 16)
  planes_sup : d.nineFixedPlane ⊔ d.nineMovingPlane = V
  planes_inf : d.nineFixedPlane ⊓ d.nineMovingPlane = ⊥
  marked_le_fixed : d.Z1 ≤ d.nineFixedPlane
  index : d.S.relIndex (T : Subgroup G) = 2
  fixes_planes : d.S ≤ normalizer (d.nineFixedPlane : Set G) ∧
    d.S ≤ normalizer (d.nineMovingPlane : Set G)
  fixed_centralizer_index : (centralizer (d.nineFixedPlane : Set G)).relIndex d.S = 2
  exchanges : ∀ t ∈ (T : Subgroup G), t ∉ d.S →
    d.nineFixedPlane.map (MulAut.conj t).toMonoidHom = d.nineMovingPlane ∧
    d.nineMovingPlane.map (MulAut.conj t).toMonoidHom = d.nineFixedPlane

/-- Complete the exchanged source from the earlier prime-three component
and the actual finite-action plane geometry. Both plane sizes are retained. -/
theorem PreExclusionSource.exchangedSource {d : CaseIComponentData T M Mc V}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V) (s : d.PreExclusionSource h.normalized 3)
    (g : d.ExchangedPlaneGeometry) : d.ExchangedSource := by
  let := h.elementary
  let := s.quasisimple
  have hYid : (primeToResidual 3 d.nineCubic).map d.nineCubic.subtype = d.nineCubic := by
    rw [nineCubic,←map_embedded_primeToResidual_of_hom 3
      (primeToResidual 3 (M ⊓ d.G1 : Subgroup G)) (M ⊓ d.G1).subtype,
      embedded_primeToResidual_eq_of_normal 3 (primeToResidual 3 (M ⊓ d.G1 : Subgroup G)) le_rfl]
  have hYp : IsPPerfect 2 d.nineCubic :=
    (isPPerfect_primeToResidual 3 2 (by decide)).of_surjective
      ((primeToResidual 3 (M ⊓ d.G1 : Subgroup G)).equivMapOfInjective
        (M ⊓ d.G1).subtype (M ⊓ d.G1).subtype_injective).toMonoidHom
      ((primeToResidual 3 (M ⊓ d.G1 : Subgroup G)).equivMapOfInjective
        (M ⊓ d.G1).subtype (M ⊓ d.G1).subtype_injective).surjective
  have hYV : d.nineCubic ≤ normalizer (V : Set G) :=
    ((map_subtype_le _).trans inf_le_left).trans h.normalized
  have he : ⁅V,d.nineCubic⁆ = d.nineMovingPlane :=
    caseI_cubic_commutator_of_residual_card_three h.normalized
      (d.Z1_le_fixed.trans inf_le_left) s.residual_card
  have hm : ⁅d.nineMovingPlane,d.nineCubic⁆ = d.nineMovingPlane := by
    rw [←he]
    exact commutator_isPPerfect_idempotent d.nineCubic V hYp
      (IsElementaryAbelian.isPGroup 2 V) hYV
  have hV2ne : d.nineMovingPlane ≠ ⊥ := by
    intro hb
    rcases g.sizes with hs | hs <;> have hc := hs.2.2.2 <;>
      rw [hb,card_bot] at hc <;> omega
  have hYnon : ¬ d.nineCubic ≤ centralizer (V : Set G) := by
    intro hc
    apply hV2ne
    rw [←he,commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hc
  have hYout : ¬ d.nineCubic ≤ d.MZ := by
    intro hb
    have hYH : d.nineCubic ≤ M ⊓ Mc ⊓ d.G1 := by
      intro y hy
      have hc : y ∈ M ⊓ d.G1 := map_subtype_le _ hy
      exact ⟨⟨hc.1,(hb hy).2⟩,hc.2⟩
    have hh := embedded_pResidual_mono 2 hYH
    rw [(pResidual_eq_top_iff 2 d.nineCubic).mpr hYp,
      ←MonoidHom.range_eq_map,range_subtype,s.residual_intersection] at hh
    exact hYnon (hh.trans ((map_subtype_le _).trans inf_le_right))
  obtain ⟨t,ht,htS⟩ : ∃ t ∈ (T : Subgroup G), t ∉ d.S := by
    by_contra! hh
    have hi := relIndex_eq_one.mpr hh
    rw [g.index] at hi
    contradiction
  exact {
    sizes := g.sizes
    odd_core := s.odd_core
    quasisimple := s.quasisimple
    local_component := s.local_component
    component_sylow := s.component_sylow
    centralizer_sylow := s.centralizer_sylow
    outside_M := s.outside_M
    ordinary := s.ordinary
    planes_sup := g.planes_sup
    planes_inf := g.planes_inf
    marked_le_fixed := g.marked_le_fixed
    index := g.index
    sylow_normal := s.sylow_normal
    fixes_planes := g.fixes_planes
    fixed_centralizer_index := g.fixed_centralizer_index
    exchanges := g.exchanges
    exchange_exists := ⟨t,ht,htS⟩
    cubic_escape := hYout
    cubic_idempotent := hYid
    cubic_two_perfect := hYp
    cubic_normalizes := hYV
    cubic_commutator := he
    cubic_moving := hm
    fixed_noncentral := fun hf => d.fixed_plane_not_centralizes hG hf
      d.nineFixedPlane d.nineMovingPlane d.nineCubic g.marked_le_fixed
      ((IsElementaryAbelian.isPGroup 2 V).to_le inf_le_left) hV2ne hYid hm t
      ((g.exchanges t ht htS).2)
    seed_bound := s.seed_bound
    moving_noncentral := s.moving_noncentral
    core_nontrivial := s.core_nontrivial
    characteristic_control := s.characteristic_control
    core_normalizer := s.core_normalizer
    sylow_normalizes_MZ := s.sylow_normalizes_MZ
    sylow_normalizes_Q1 := s.sylow_normalizes_Q1 }

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
