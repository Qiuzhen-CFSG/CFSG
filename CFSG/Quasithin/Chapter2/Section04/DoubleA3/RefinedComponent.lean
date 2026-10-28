module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.OriginalComponent
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.NativeSource.Source
public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.C129Complete

/-!
# The refined catalogue at the original paired-cubic centralizer

The actual pair (J(S), H ∩ C_G(z₂)) belongs to the original local-pair
family. The selected Sylow group and the product z₁z₂ then construct the
full 2.3.9 source setup, with the same ambient T, M and component inclusion.
Applying the proved earlier refinement removes its excluded model families
before the special A₄ normalizer inspection in 2.4.32. The genuine binary
M₂₂ residual remains explicit.

Source: Aschbacher–Smith 2.3.9(7), pp.525–526, used in 2.4.32, p.547.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.DoubleA3
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}

/-- The literal local pair inside the second involution centralizer. -/
theorem SourceCentralizerGeometry.refinement_pair
    (g : SourceCentralizerGeometry c) (hR : sourceR d ∈ beta M) :
    (sourceR d,d.H ⊓ involutionCentralizer g.z₂) ∈
      localPairsIn (Chapter1.He G) M (involutionCentralizer g.z₂) := by
  let H := involutionCentralizer g.z₂
  let W := zpowers g.z₂
  have hRS : sourceR d ≤ (d.S : Subgroup d.H).map d.H.subtype :=
    sSup_le (fun _ h => h.1)
  have hRH : sourceR d ≤ d.H := hRS.trans (map_subtype_le _)
  have hUR : c.U₂ ≤ sourceR d := c.baumann ▸ c.second.module_le
  have hWcard : Nat.card W = 2 := by rw [Nat.card_zpowers,g.order_second]
  have hp : IsPGroup 2 W := IsPGroup.of_card (n:=1) (by simpa using hWcard)
  have hne : W ≠ ⊥ := by intro hh; rw [hh,card_bot] at hWcard; omega
  have hWH : W ≤ d.H := zpowers_le.mpr (hRH (hUR g.second_mem))
  have hc : centralizer (W : Set G) = H := by
    change centralizer (zpowers g.z₂ : Set G) = centralizer ({g.z₂} : Set G)
    rw [zpowers_eq_closure,centralizer_closure]
  have hn : normalizer (W : Set G) = H :=
    le_antisymm ((normalizer_le_centralizer_of_card_two W hWcard).trans hc.le)
      (hc.symm ▸ Subgroup.centralizer_le_normalizer _)
  have hWH' : W ≤ H := hn ▸ W.le_normalizer
  have hJe : d.H ⊓ H ∈ Chapter1.He G := by
    rw [←hn]
    exact Chapter1.normalizer_mem_He_of_isPGroup d.mem_gammaEvenZero.2 hp hWH
  have hWQ : W ≤ twoCore (d.H ⊓ H) :=
    le_pCoreIn_of_normalizes hp (le_inf hWH hWH') (hn.symm ▸ inf_le_right)
  have hRHi : sourceR d ≤ H := by
    intro r hr
    exact mem_centralizer_singleton_iff.mpr (g.second_fixed r hr)
  have hout : ¬ d.H ⊓ H ≤ M := fun hle => d.outside
    ((le_inf (map_subtype_le _) g.first_block_le_second_centralizer).trans hle)
  exact ⟨⟨hR,hJe,fun he => hne (bot_unique (he ▸ hWQ)),le_inf hRH hRHi,hout⟩,inf_le_right⟩

/-- The source setup keeps the original Sylow group and central involution. -/
noncomputable def SourceCentralizerGeometry.refinement_setup
    (g : SourceCentralizerGeometry c) (hM : IsMaximalTwoLocal M)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hR : sourceR d ∈ beta M)
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K) :
    ComponentRefinement.MathieuSourceSetup (involutionCentralizer g.z₂)
      (K.map (involutionCentralizer g.z₂).subtype) M g.P₂ (g.z₁*g.z₂) := by
  let H := involutionCentralizer g.z₂
  have hRS : sourceR d ≤ (d.S : Subgroup d.H).map d.H.subtype :=
    sSup_le (fun _ h => h.1)
  have hRT : sourceR d ≤ (T : Subgroup G) := hRS.trans c.original.T_le
  have hU₁R : c.U₁ ≤ sourceR d := c.baumann ▸ c.first.module_le
  have hU₂R : c.U₂ ≤ sourceR d := c.baumann ▸ c.second.module_le
  have hz₂T : g.z₂ ∈ (T : Subgroup G) := hRT (hU₂R g.second_mem)
  have hc : (center (T : Subgroup G)).map (T : Subgroup G).subtype ≤
      (g.P₂ : Subgroup H).map H.subtype := by
    rw [g.second_intersection]
    rintro x ⟨a,ha,rfl⟩
    refine ⟨a.property,mem_centralizer_singleton_iff.mpr ?_⟩
    exact (congrArg Subtype.val (mem_center_iff.mp ha ⟨g.z₂,hz₂T⟩)).symm
  have hPT : (g.P₂ : Subgroup H).map H.subtype < (T : Subgroup G) := by
    apply lt_of_le_of_ne (g.second_intersection ▸ inf_le_left)
    intro he
    have hi := g.second_sylow_index
    rw [he,relIndex_self] at hi
    omega
  have hzT : g.z₁*g.z₂ ∈ (T : Subgroup G) :=
    hRT ((sourceR d).mul_mem (hU₁R g.first_mem) (hU₂R g.second_mem))
  have hz : g.z₁*g.z₂ ∈ (center (T : Subgroup G)).map (T : Subgroup G).subtype := by
    refine ⟨⟨_,hzT⟩,mem_center_iff.mpr ?_,rfl⟩
    intro t
    exact Subtype.ext (g.product_centralizes_sylow t t.property)
  have hk : (K.map H.subtype).subgroupOf H = K := by
    exact comap_map_eq_self_of_injective H.subtype_injective K
  exact ⟨T,hM,hTM,hu,Or.inr g.second_max,sourceR d,d.H⊓H,
    g.refinement_pair hR,g.second_span ▸ le_sup_left,map_subtype_le _,hk.symm ▸ hK,
    hPT,hc,hz,g.product_order⟩

/-- Apply the full earlier refinement to the actual selected component. -/
theorem SourceCentralizerGeometry.original_refined_catalogue
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hpair : d.L0 ≠ d.block)
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K) :
    let A := K.map (involutionCentralizer g.z₂).subtype
    ComponentRefinement.RefinedIntersection A M
      ((g.P₂ : Subgroup _).map (involutionCentralizer g.z₂).subtype) (g.z₁*g.z₂) ∨
      (Nat.card (pCore 2 A) = 2 ∧ Nonempty ((A ⧸ pCore 2 A) ≃* Sporadic.Mathieu.M22) ∧
        IsCyclic (center (T : Subgroup G))) := by
  have hg := d.paired_cubic_source_sylow_geometry hG T hM hTM hu hST hpair c.cubic_first
  exact ((g.refinement_setup hM hTM hu hg.2.2.2.2.2.1 K hK).source_refinement_or_binary_mathieu
    hG (fun _ _ _ => ChapterA.Section02.theoremsABC_knownSimple) localC129Input_knownSimple).2

end CFSG.Quasithin.Chapter2.DoubleA3
