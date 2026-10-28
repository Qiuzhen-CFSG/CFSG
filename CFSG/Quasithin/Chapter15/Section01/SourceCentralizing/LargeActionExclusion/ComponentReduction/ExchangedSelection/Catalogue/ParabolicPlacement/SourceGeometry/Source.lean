module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Selection
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.CentralizerNormalizer
public import Theory.GroupTheory.CentralKernelSylowRigidity

/-!
# Source quotient geometry before the row exclusions

The original seed bound and full module put the central involutions in
N(L). The center of L is a two-group, by subnormal inheritance of the
trivial odd core. In the literal N_G₁(L)/C_G₁(L) quotient, the centralizer
of the seed lifts: its full preimage contains S_L, and a commutator into
the central two-group kernel vanishing on that Sylow vanishes everywhere.
This gives the source image centralizer and its placement in M_L, hence
movement of the order-two omega center by an escaping O^{3′}(M ∩ L).

Escape also implies survival modulo O₂(G₁). The earlier SQTK component
normalizer theorem therefore puts the full S-centralizer in N(L), even
for a constrained component. The published faithful-image reduction now
proves (**), and supplies the geometry input of the family consumer (!).
The same-pair placement (*) remains a separate obligation of the catalogue
owner qt-e-15122-pre-exclusion-catalogue. The marker application retains
both source primes and the literal selected component.

Source: Aschbacher--Smith, original 15.1.22(**), printed p.1099.
-/

public section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

theorem PreExclusionSource.source_central_seed_normalizes
    (s : d.PreExclusionSource h.normalized p) (hfull : V = localModule T M) :
    centralInvolutions T ≤ normalizer (d.L : Set G) := by
  have hZV : centralInvolutions T ≤ V := hfull ▸ le_conjugateSpanBy _ _
  have hZL : d.Z1 ≤ centralizer (d.L : Set G) :=
    le_centralizer_iff.mp d.L_component.1
  exact (le_inf le_rfl hZV).trans (s.seed_bound.trans
    (sup_le (hZL.trans (Subgroup.centralizer_le_normalizer _))
      (le_sup_right.trans s.residual_normalizes)))

theorem PreExclusionSource.source_central_seed_plus
    (s : d.PreExclusionSource h.normalized p) (hfull : V = localModule T M)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hcard : Nat.card d.plusOmega = 2) :
    d.plus (centralInvolutions T) = d.plusOmega :=
  d.central_seed_plus_eq_omega h hTM hu (s.source_central_seed_normalizes (h := h) hfull) hcard

theorem PreExclusionSource.source_center_two
    (s : d.PreExclusionSource h.normalized p) : IsPGroup 2 (center d.L) := by
  have ho : pPrimeCore 2 d.L = ⊥ := by
    let e : d.L.subgroupOf d.G1 ≃* d.L := subgroupOfEquivOfLe d.L_component.1
    have ho' : pPrimeCore 2 (d.L.subgroupOf d.G1) = ⊥ :=
      Subgroup.IsSubnormal.pPrimeCore_eq_bot s.odd_core _ d.L_component.2.subnormal
    have hh := pPrimeCore_map_iso 2 e
    rw [ho', Subgroup.map_bot] at hh
    exact hh.symm
  exact isPGroup_of_nilpotent_normal (p := 2) (center d.L)
    inferInstance inferInstance ho

/-- Restriction of the literal plus quotient to L, with central kernel. -/
noncomputable def componentPlusHom (d : CaseIComponentData T M Mc V) :
    d.L →* d.ComponentPlus := d.plusMap.comp (inclusion d.component_le_normalizer)

theorem componentPlusHom_ker (d : CaseIComponentData T M Mc V) :
    d.componentPlusHom.ker = center d.L := by
  ext x
  change d.plusMap (inclusion d.component_le_normalizer x) = 1 ↔ x ∈ center d.L
  constructor
  · intro hx
    have hc := (QuotientGroup.eq_one_iff (N := d.componentKernel)
      (inclusion d.component_le_normalizer x)).mp hx
    exact mem_center_iff.mpr (fun y => Subtype.ext (hc y y.property))
  · intro hx
    apply (QuotientGroup.eq_one_iff (N := d.componentKernel)
      (inclusion d.component_le_normalizer x)).mpr
    intro y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hy⟩)

theorem PreExclusionSource.source_plus_centralizer_lifts
    (s : d.PreExclusionSource h.normalized p) (hfull : V = localModule T M)
    (hTM : (T : Subgroup G) ≤ M)
    (x : d.L)
    (hx : d.componentPlusHom x ∈
      centralizer (d.plus (centralInvolutions T) : Set d.ComponentPlus)) :
    (x : G) ∈ centralizer (centralInvolutions T : Set G) := by
  let f := d.componentPlusHom
  let C := (centralizer (d.plus (centralInvolutions T) : Set d.ComponentPlus)).comap f
  have hn := s.source_central_seed_normalizes (h := h) hfull
  have hZN := (d.central_seed_le_sylowNormalizer (d.marked_le_sylow h hTM) hn).trans
    d.sylowNormalizer_le_componentNormalizer
  obtain ⟨P,hP⟩ := s.component_sylow
  have hPC : (P : Subgroup d.L) ≤ C := by
    intro y hy w hw
    obtain ⟨z,hz,rfl⟩ := hw
    have hyT := d.SL_le_S.trans d.S_le_T (hP ▸ mem_map_of_mem d.L.subtype hy)
    exact congrArg d.plusMap (Subtype.ext
      (centralInvolutions_le_centralizer_sylow T hz y hyT).symm)
  intro z hz
  let zN : d.componentNormalizer := ⟨z,hZN hz⟩
  let a := d.L.normalizerMonoidHom ⟨z,hn hz⟩
  have ha : f.comp (a.toMonoidHom.comp C.subtype) = f.comp C.subtype := by
    ext y
    have hh := y.property (d.plusMap zN) (mem_map_of_mem d.plusMap hz)
    change d.plusMap (zN * inclusion d.component_le_normalizer (y : d.L) * zN⁻¹) =
      d.plusMap (inclusion d.component_le_normalizer (y : d.L))
    change d.plusMap zN * d.plusMap (inclusion d.component_le_normalizer (y : d.L)) =
      d.plusMap (inclusion d.component_le_normalizer (y : d.L)) * d.plusMap zN at hh
    rw [map_mul,map_mul,map_inv,hh,mul_inv_cancel_right]
  have he := MonoidHom.eq_of_central_pGroup_kernel_of_sylow f
    (d.componentPlusHom_ker.le) (d.componentPlusHom_ker.symm ▸ s.source_center_two (h := h))
    (a.toMonoidHom.comp C.subtype) C.subtype ha (P.subtype hPC) (by
      intro y hy
      apply Subtype.ext
      change z * (y : G) * z⁻¹ = (y : G)
      have hyT := d.SL_le_S.trans d.S_le_T (hP ▸
        mem_map_of_mem d.L.subtype (show (y : d.L) ∈ P from hy))
      rw [← centralInvolutions_le_centralizer_sylow T hz (y : G) hyT,
        mul_inv_cancel_right])
  have hh := congrArg (fun ff : C →* d.L => (ff ⟨x,hx⟩ : G)) he
  change z * (x : G) * z⁻¹ = x at hh
  exact mul_inv_eq_iff_eq_mul.mp hh

/-- The literal image centralizer and its placement, on both component branches. -/
theorem PreExclusionSource.source_plus_centralizer
    (s : d.PreExclusionSource h.normalized p) (hfull : V = localModule T M)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc}) :
    d.plus d.L ⊓ centralizer (d.plus (centralInvolutions T) : Set d.ComponentPlus) =
      d.plus (d.L ⊓ centralizer (centralInvolutions T : Set G)) ∧
    d.plus (d.L ⊓ centralizer (centralInvolutions T : Set G)) ≤ d.plus d.ML := by
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  refine ⟨le_antisymm ?_ ?_, map_mono (comap_mono ?_)⟩
  · rintro _ ⟨⟨x,hx,rfl⟩,hc⟩
    exact mem_map_of_mem d.plusMap ⟨hx,
      s.source_plus_centralizer_lifts (h := h) hfull hTM ⟨x,hx⟩ hc⟩
  · exact le_inf (map_mono (comap_mono inf_le_left)) (d.plus_centralizes _ _ inf_le_right)
  · intro x hx
    exact ⟨⟨d.L_component.1 hx.1,hMc.2 hx.2⟩,hx.1⟩

theorem PreExclusionSource.source_plusOmega_moved
    (s : d.PreExclusionSource h.normalized p) (hfull : V = localModule T M)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hcard : Nat.card d.plusOmega = 2)
    (hout : ¬ d.localThreeResidual ≤ d.ML) :
    ¬ d.plusOmega ≤ centralizer (d.plus d.localThreeResidual : Set d.ComponentPlus) := by
  intro hc
  rw [← s.source_central_seed_plus (h := h) hfull hTM hu hcard] at hc
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  apply hout
  intro y hy
  have hyL := d.localThreeResidual_le_component hy
  have hcy : d.componentPlusHom ⟨y,hyL⟩ ∈
      centralizer (d.plus (centralInvolutions T) : Set d.ComponentPlus) :=
    le_centralizer_iff.mp hc (mem_map_of_mem d.plusMap
      (show (⟨y,d.component_le_normalizer hyL⟩ : d.componentNormalizer) ∈
        d.localThreeResidual.subgroupOf d.componentNormalizer from hy))
  exact ⟨⟨d.L_component.1 hyL,hMc.2
    (s.source_plus_centralizer_lifts (h := h) hfull hTM ⟨y,hyL⟩ hcy)⟩,hyL⟩


theorem PreExclusionSource.source_residual_centralizer_normalizes
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hout : ¬ d.localThreeResidual ≤ d.ML) :
    d.S ⊓ centralizer (d.localThreeResidual : Set G) ≤ normalizer (d.L : Set G) := by
  let := h.elementary
  have hsq : IsSQTK KnownSimple.IsKnownSimple d.G1 := caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
    ((IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left))
  have hQ : IsSQTK KnownSimple.IsKnownSimple (d.G1 ⧸ pCore 2 d.G1) := by
    refine ⟨?_, hsq.isKGroup.quotient _⟩
    intro r hr ho
    let : Fact r.Prime := ⟨hr⟩
    exact (primeRank_quotient_le_of_isTwoGroup r ho _ pCore_isPGroup).trans
      (hsq.stronglyQuasithin r hr ho)
  have hYL := d.localThreeResidual_le_component
  have hYG := hYL.trans d.L_component.1
  have hSL := (s.local_intersections (h := h) hG hu hTM).2.1
  obtain ⟨P,hP⟩ := s.centralizer_sylow
  have hOS : (pCore 2 d.G1).map d.G1.subtype ≤ d.S := by
    rw [←hP]
    exact map_mono (pCore_isPGroup.le_sylow_of_normal P)
  have hYcore : ¬ d.localThreeResidual.subgroupOf d.G1 ≤ pCore 2 d.G1 := by
    intro hc
    apply hout
    intro y hy
    exact hSL ⟨hOS (mem_map_of_mem d.G1.subtype
      (hc (show (⟨y,hYG hy⟩ : d.G1) ∈ d.localThreeResidual.subgroupOf d.G1 from hy))),hYL hy⟩
  have hn := Chapter1.Section02.cComponent_centralizer_le_normalizer_of_not_le_twoCore
    hQ d.L_component.2 (comap_mono hYL) hYcore
  intro x hx
  have hi : (⟨x,d.S_le_G1 hx.1⟩ : d.G1) ∈
      normalizer (d.L.subgroupOf d.G1 : Set d.G1) :=
    hn (fun y hy => Subtype.ext (hx.2 y hy))
  have he := subgroupOf_normalizer_eq (show d.L ≤ d.G1 from d.L_component.1)
  have hi' : (⟨x,d.S_le_G1 hx.1⟩ : d.G1) ∈ (normalizer (d.L : Set G)).subgroupOf d.G1 :=
    he.symm ▸ hi
  exact hi'

/-- Both source-geometric inputs of the published family consumer, with
no ordinary-component assumption and no normalization callback. -/
theorem PreExclusionSource.source_plus_geometry
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hfull : V = localModule T M) (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hcard : Nat.card d.plusOmega = 2) (hout : ¬ d.localThreeResidual ≤ d.ML) :
    (¬ d.plusOmega ≤ centralizer (d.plus d.localThreeResidual : Set d.ComponentPlus)) ∧
    d.S ⊓ centralizer (d.localThreeResidual : Set G) ≤ normalizer (d.L : Set G) :=
  ⟨s.source_plusOmega_moved (h := h) hfull hTM hu hcard hout,
    s.source_residual_centralizer_normalizes (h := h) hG hTM hu hout⟩

/-- The full centralizer assertion of source 15.1.22(**). Only its two
stated premises, omega-center order and residual escape, remain. -/
theorem PreExclusionSource.source_residual_centralizer
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hfull : V = localModule T M) (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hcard : Nat.card d.plusOmega = 2) (hout : ¬ d.localThreeResidual ≤ d.ML) :
    d.S ⊓ centralizer (d.localThreeResidual : Set G) =
      d.S ⊓ centralizer (d.L : Set G) := by
  obtain ⟨hm,hn⟩ := s.source_plus_geometry (h := h) hG hfull hTM hu hcard hout
  exact d.localThreeResidual_centralizer_of_plus_movement hTM hcard hm hn

/-- Discharge the geometry input of the actual family consumer. The
same-pair placement is the separate preliminary assertion (*). -/
theorem PreExclusionSource.parabolic_family_centralizer_of_placement
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hfull : V = localModule T M) (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hplacement : ∀ P ∈ d.sourceParabolics, P ≤ M ⊓ d.L ∨ P ≤ d.ML)
    (hcard : Nat.card d.plusOmega = 2)
    (F : Set (Subgroup G)) (hF : F ⊆ d.sourceParabolics) (hout : ¬ sSup F ≤ d.ML) :
    (∀ P ∈ F, ¬ P ≤ d.ML → P ≤ M) ∧
      (¬ d.localThreeResidual ≤ d.ML) ∧
      d.S ⊓ centralizer (d.localThreeResidual : Set G) =
        d.S ⊓ centralizer (d.L : Set G) :=
  s.parabolic_family_centralizer_of_source_inputs (h := h) hG hu hTM hplacement hcard
    (s.source_plus_geometry (h := h) hG hfull hTM hu hcard) F hF hout

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The general marker now supplies the full source plus geometry before
any row exclusion. The order-two and escape premises are precisely those
in 15.1.22(**); their model-specific discharge remains with the catalogue. -/
theorem PreparedChosenModule.source_preExclusion_plus_geometry
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      centralInvolutions T ≤ normalizer (d.L : Set G) ∧
      (d.plus d.L ⊓ centralizer (d.plus (centralInvolutions T) : Set d.ComponentPlus) =
        d.plus (d.L ⊓ centralizer (centralInvolutions T : Set G)) ∧
        d.plus (d.L ⊓ centralizer (centralInvolutions T : Set G)) ≤ d.plus d.ML) ∧
      (Nat.card d.plusOmega = 2 → d.plus (centralInvolutions T) = d.plusOmega ∧
        (¬ d.localThreeResidual ≤ d.ML →
          d.S ⊓ centralizer (d.localThreeResidual : Set G) =
            d.S ⊓ centralizer (d.L : Set G))) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,s.source_central_seed_normalizes (h := h) hfull,
    s.source_plus_centralizer (h := h) hfull hM.1.2 hu,?_⟩
  intro hc
  exact ⟨s.source_central_seed_plus (h := h) hfull hM.1.2 hu hc,
    s.source_residual_centralizer (h := h) hG hfull hM.1.2 hu hc⟩

end CFSG.Quasithin.Chapter15.Section01
