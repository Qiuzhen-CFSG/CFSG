module
public import CFSG.Quasithin.Chapter10.SourceA5OffenderNormalization
public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerGeneration
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.FixedVectors
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.ParameterExclusion

/-!
# The original small offender normalizes the moved factor

A nontrivial displacement would supplement the opposite factor in the full
module. Point-centralizer generation would then place the original component,
and its conjugate by an exchanging offender element, in the conjugate maximal
local subgroup. The cubic residual rigidity excludes that containment.
Consequently the displacement vanishes. A noncentral normalizing involution
has a fixed vector outside the component-fixed space, forcing the whole
small offender to stabilize the original moved factor.

The literal chosen-module irreducibility and the genuine separate-factor,
component-normalizer and point-centralizer bounds remain explicit. The
normalization and common fixed-space implications are proved here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Proposition 10.2.12, printed pp.754–755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
local instance (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

theorem source_a5_offender_displacement_eq_bot
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hcent : ∀ u ∈ ⁅D.fullModule,L⁆, u ≠ 1 → centralizer ({u} : Set G) ≤ D.maximalLocal)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    {g b : G} (hg : g ∉ D.maximalLocal)
    (hb : b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal ⊓
      normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (hbn : b ∉ centralizer (L.map (MulAut.conj g).toMonoidHom : Set G)) :
    ⁅(⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal,
      ⁅D.fullModule,L⁆ ⊓ centralizer ({b} : Set G)⁆ = ⊥ := by
  by_contra hQ
  let V := D.fullModule
  let W := ⁅D.fullModule,L⁆
  let U := W.map (MulAut.conj t).toMonoidHom
  let P := W.map (MulAut.conj g).toMonoidHom
  let A := P ⊓ D.maximalLocal
  let Q := ⁅A,W ⊓ centralizer ({b} : Set G)⁆
  let N := D.maximalLocal.map (MulAut.conj g).toMonoidHom
  have hQV : Q ≤ P ⊓ V :=
    source_nonnormal_offender_displacement_le D hn ht htn hcross hcent hb.1.1 hbn
  have hWV : W ≤ V := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  have hUV : U ≤ V := (map_mono hWV).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp
      (D.maximalLocal_normalizes_fullModule (le_normalizer_componentOrbit L T ht)))
  have hs := (source_a5_nontrivial_offender_displacement_supplement D e hn ht htn
    hcross hcent hNL hg hb hbn hQ).2
  have hQN : ∀ q ∈ Q, q ≠ 1 → centralizer ({q} : Set G) ≤ N := by
    intro q hq hqne
    obtain ⟨w,hw,hew⟩ := (hQV hq).1
    have hwne : w ≠ 1 := by
      intro he
      apply hqne
      rw [←hew,he,map_one]
    rw [←hew]
    change centralizer ({(MulAut.conj g) w} : Set G) ≤ N
    rw [←CentralizerSmallKernelTransport.map_centralizer (MulAut.conj g) w]
    exact map_mono (hcent w hw hwne)
  have hLN : L ≤ N := source_a5_le_of_supplement_point_centralizers D e Q U N
    (hQV.trans inf_le_right) hUV hs hcross hQN
  obtain ⟨a,ha,han⟩ : ∃ a ∈ A, a ∉ normalizer (W : Set G) := by
    by_contra! hAN
    have hfix := source_a5_offender_fixed_space_of_normalizes D e hn ht htn
      hcross hcent hNL hg hAN hb.1.1 hbn
    exact hQ (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hfix))
  have hVM : V ≤ D.maximalLocal := D.fullModule_le_orbit.trans (localOrbit T L).le_normalizer
  have haN : a ∈ N := map_mono (hWV.trans hVM) ha.1
  have hLaN : L.map (MulAut.conj a).toMonoidHom ≤ N :=
    (map_mono hLN).trans_eq (mem_normalizer_iff_map_conj_eq.mp (N.le_normalizer haN))
  obtain ⟨s,hsT,hsn,hpair,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  have hLa : L.map (MulAut.conj a).toMonoidHom ≠ L := by
    intro he
    apply han
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅V,L⁆).map (MulAut.conj a).toMonoidHom = ⁅V,L⁆
    have hm : V.map (MulAut.conj a).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule ha.2)
    rw [map_commutator,hm,he]
  have he := (source_nonnormal_maximal_pair D hn hsT hsn a ha.2).resolve_left hLa
  have hRN : localOrbit T L ≤ N := by
    rw [hpair,←he]
    exact sup_le hLN hLaN
  have hd : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,card_alternatingGroup]
    decide
  exact hg ((source_nonnormal_orbit_le_conjugate_maximal_iff D hn hd g).mp hRN)

theorem source_a5_small_offender_normalizes_moved
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hcent : ∀ u ∈ ⁅D.fullModule,L⁆, u ≠ 1 → centralizer ({u} : Set G) ≤ D.maximalLocal)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    {g : G} (hg : g ∉ D.maximalLocal)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 2) :
    (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal ≤
      normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  let W := ⁅D.fullModule,L⁆
  let P := W.map (MulAut.conj g).toMonoidHom
  let A := P ⊓ D.maximalLocal
  obtain ⟨b,hb,hbM,hbW,hbn⟩ :=
    source_a5_small_offender_exists_noncentral_normalizing_element D e hn hsmall
  have hbne : b ≠ 1 := fun he => hbn (he ▸ one_mem _)
  let := source_full_moved_elementary D
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.map _
  have ho : orderOf b = 2 := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian b hb) hbne
  have hX := source_a5_original_involution_fixed_not_le_of_irreducible D e hi hbW ho
  have hzero := source_a5_offender_displacement_eq_bot D e hn ht htn hcross hcent hNL hg
    ⟨⟨hb,hbM⟩,hbW⟩ hbn
  exact source_nonnormal_normalizes_moved_of_fixed_subgroup D hn ht htn hcross
    (W ⊓ centralizer ({b} : Set G)) A inf_le_left hX inf_le_right
    (le_centralizer_iff.mpr (commutator_eq_bot_iff_le_centralizer.mp hzero))

theorem source_a5_small_offender_moduleA_lower
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hcent : ∀ u ∈ ⁅D.fullModule,L⁆, u ≠ 1 → centralizer ({u} : Set G) ≤ D.maximalLocal)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    {g : G} (hg : g ∉ D.maximalLocal) {k : ℕ} (hk : k ≤ 2)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ k)
    (hactive : ¬ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal ≤
      centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)) :
    ((4-k : ℕ) : ℕ∞) ≤ moduleA
      ((automizerRepresentation ⁅D.fullModule,L⁆).comp
        (inducedAutomizer ⁅D.fullModule,L⁆ D.maximalLocal).subtype) := by
  exact source_a5_offender_moduleA_lower_of_normalizes D e hn ht htn hcross hcent hNL
    g hg hk hsmall
    (source_a5_small_offender_normalizes_moved D e hi hn ht htn hcross hcent hNL hg
      (hsmall.trans hk)) hactive

theorem source_a5_corank_one_offender_centralizes_moved
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hcent : ∀ u ∈ ⁅D.fullModule,L⁆, u ≠ 1 → centralizer ({u} : Set G) ≤ D.maximalLocal)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    {g : G} (hg : g ∉ D.maximalLocal)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 1) :
    (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal ≤
      centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  by_contra hactive
  have hlo := source_a5_small_offender_moduleA_lower D e hi hn ht htn hcross hcent hNL
    hg (by decide : 1 ≤ 2) hsmall hactive
  have hhi := source_a5_original_local_moduleA_le_two_of_separate_factors D e hi ht htn hcross
  have hh : (4-1 : ℕ) ≤ 2 := by exact_mod_cast hlo.trans hhi
  omega

theorem source_a5_deleted_corank_two_offender_centralizes_moved
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (f : alternatingGroup (Fin 5) ≃* alternatingGroup (Fin 5))
    (c : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      (Representation.OrthogonalFourMinus.AlternatingFive.alternatingRepresentation.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hcent : ∀ u ∈ ⁅D.fullModule,L⁆, u ≠ 1 → centralizer ({u} : Set G) ≤ D.maximalLocal)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    {g : G} (hg : g ∉ D.maximalLocal)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 2) :
    (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal ≤
      centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  by_contra hactive
  have hlo := source_a5_small_offender_moduleA_lower D e hi hn ht htn hcross hcent hNL
    hg (le_refl 2) hsmall hactive
  have hhi := source_a5_original_local_moduleA_le_one_of_deleted D e f c
    (source_original_moved_stabilizer_le_component_normalizer D ht htn hcross)
  have hh : (4-2 : ℕ) ≤ 1 := by exact_mod_cast hlo.trans hhi
  omega

end CFSG.Quasithin.Chapter10
