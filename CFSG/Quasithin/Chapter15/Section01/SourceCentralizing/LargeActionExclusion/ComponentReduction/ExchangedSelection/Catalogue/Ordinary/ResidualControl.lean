module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.LocalGeometry
public import Theory.GroupTheory.CentralCommutatorQuotient

/-!
# Residual control before the ordinary rank-one exclusions

The literal residual-intersection identity makes every two-perfect subgroup
of M ∩ M_Z centralize V. In particular O²(M ∩ G₁) escapes M_Z, since its
commutator with V acts nontrivially on the selected component. This uses
neither a cubic residual nor an exchanged plane.

These facts give the two contradiction arguments in 15.1.21 once the model
supplies its Borel/Thompson geometry: a two-perfect Borel subgroup controlled
by J(S)=J(T) centralizes V, and an actor centralizing L cannot generate the
moving plane by commutators. The required model geometry remains explicit.
Source: Aschbacher--Smith 15.1.18(2), 15.1.19(7), 15.1.21, pp.1092--1098.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The original 15.1.18(2) identity controls every two-perfect subgroup
of the intersection, not just a particular recognized Borel. -/
theorem PreExclusionSource.twoPerfect_intersection_centralizes
    (s : d.PreExclusionSource h.normalized p) {B : Subgroup G}
    (hB : IsPPerfect 2 B) (hBM : B ≤ M) (hBZ : B ≤ d.MZ) :
    B ≤ centralizer (V : Set G) := by
  have hBI : B ≤ M ⊓ Mc ⊓ d.G1 :=
    le_inf (le_inf hBM (hBZ.trans inf_le_right)) (hBZ.trans inf_le_left)
  have hh := embedded_pResidual_mono 2 hBI
  rw [(pResidual_eq_top_iff 2 B).mpr hB, ← MonoidHom.range_eq_map,
    range_subtype, s.residual_intersection] at hh
  exact hh.trans ((map_subtype_le _).trans inf_le_right)

/-- Even before fixing the prime, the original two-residual escapes M_Z. -/
theorem PreExclusionSource.twoResidual_not_le_MZ
    (s : d.PreExclusionSource h.normalized p) :
    ¬ (pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype ≤ d.MZ := by
  let C := M ⊓ d.G1
  let R := (pResidual 2 C).map C.subtype
  have hR : IsPPerfect 2 R := (isPPerfect_pResidual (G := C) 2).of_surjective
    ((pResidual 2 C).equivMapOfInjective C.subtype C.subtype_injective).toMonoidHom
    ((pResidual 2 C).equivMapOfInjective C.subtype C.subtype_injective).surjective
  intro hout
  have hc := s.twoPerfect_intersection_centralizes (h := h) hR
    ((map_subtype_le _).trans inf_le_left) hout
  have hv : ⁅V,R⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hc
  apply s.moving_noncentral
  change ⁅d.L,⁅V,R⁆⁆ = ⊥
  rw [hv, commutator_bot_right]

/-- The original moving subgroup lies in S, with no assumption on its order. -/
theorem PreExclusionSource.moving_le_sylow
    (_s : d.PreExclusionSource h.normalized p) (hTM : (T : Subgroup G) ≤ M) :
    ⁅V,(pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype⁆ ≤ d.S := by
  let := h.elementary
  have hVT : V ≤ (T : Subgroup G) := by
    let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer h.normalized
    let := IsElementaryAbelian.subgroupOf h.le_selected (p := 2)
    have hh := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf M)).le_sylow_of_normal
      (T.subtype hTM)
    simpa only [map_subgroupOf_eq_of_le h.le_selected, Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hTM] using map_mono (f := M.subtype) hh
  have hmove : ⁅V,(pResidual 2 (M ⊓ d.G1 : Subgroup G)).map
      (M ⊓ d.G1).subtype⁆ ≤ V :=
    le_normalizer_iff_commutator_le_left.mp
      (((map_subtype_le _).trans inf_le_left).trans h.normalized)
  exact hmove.trans (le_inf hVT
    (V.le_centralizer.trans (centralizer_le (d.Z1_le_fixed.trans inf_le_left))))

/-- The contradiction in cases (i) and (iii) of 15.1.21. The Borel (or its
specified torus subgroup) supplies only its actual local geometry. -/
theorem PreExclusionSource.false_of_thompson_borel
    (s : d.PreExclusionSource h.normalized p) (hTM : (T : Subgroup G) ≤ M)
    (hJ : elementaryAbelianMaxJ d.S = elementaryAbelianMaxJ (T : Subgroup G))
    (hNJ : normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤ M)
    {B : Subgroup G} (hB : IsPPerfect 2 B) (hBZ : B ≤ d.MZ)
    (hBJ : B ≤ normalizer (elementaryAbelianMaxJ d.S : Set G))
    (hfix : d.S ⊓ centralizer (B : Set G) ≤ d.S ⊓ centralizer (d.L : Set G)) :
    False := by
  have hBM : B ≤ M := by rw [hJ] at hBJ; exact hBJ.trans hNJ
  have hBV := s.twoPerfect_intersection_centralizes (h := h) hB hBM hBZ
  have hmoveV : ⁅V,(pResidual 2 (M ⊓ d.G1 : Subgroup G)).map
      (M ⊓ d.G1).subtype⁆ ≤ V :=
    le_normalizer_iff_commutator_le_left.mp
      (((map_subtype_le _).trans inf_le_left).trans h.normalized)
  have hmoveB := hmoveV.trans (le_centralizer_iff.mp hBV)
  have hmoveL := ((le_inf (s.moving_le_sylow (h := h) hTM) hmoveB).trans hfix).trans inf_le_right
  apply s.moving_noncentral
  rw [commutator_comm]
  exact commutator_eq_bot_iff_le_centralizer.mpr hmoveL

/-- The contradiction in case (ii) of 15.1.21. Centralization by the
actual actor and the moving-commutator identity force the moving subgroup
to centralize L, even when L has a nontrivial central two-cover. -/
theorem PreExclusionSource.false_of_moving_actor_centralizes
    (s : d.PreExclusionSource h.normalized p) {Y : Subgroup G}
    (hYL : Y ≤ centralizer (d.L : Set G))
    (hmove : ⁅⁅V,(pResidual 2 (M ⊓ d.G1 : Subgroup G)).map
      (M ⊓ d.G1).subtype⁆,Y⁆ =
        ⁅V,(pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype⁆) :
    False := by
  let W := ⁅V,(pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype⁆
  have hWN : W ≤ normalizer (d.L : Set G) := le_sup_right.trans s.residual_normalizes
  have hc : ⁅Y,W⁆ ≤ centralizer (d.L : Set G) := by
    apply commutator_le.mpr
    intro y hy w hw
    exact commutator_mem_centralizer_of_normalizes d.L (hYL hy) (hWN hw)
  rw [commutator_comm, hmove] at hc
  apply s.moving_noncentral
  rw [commutator_comm]
  exact commutator_eq_bot_iff_le_centralizer.mpr hc

/-- The actual O²(M ∩ G₁) acts nontrivially on L. This is the action input
used to exclude the remaining odd-characteristic models in 15.1.20(3). -/
theorem PreExclusionSource.twoResidual_not_centralizes_component
    (s : d.PreExclusionSource h.normalized p) :
    ¬ (pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype ≤
      centralizer (d.L : Set G) := by
  let := h.elementary
  let R := (pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype
  have hRp : IsPPerfect 2 R := isPPerfect_embedded_pResidual 2 _
  have hRN : R ≤ normalizer (V : Set G) :=
    ((map_subtype_le _).trans inf_le_left).trans h.normalized
  intro hc
  exact s.false_of_moving_actor_centralizes (h := h) hc
    (commutator_isPPerfect_idempotent R V hRp (IsElementaryAbelian.isPGroup 2 V) hRN)

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
