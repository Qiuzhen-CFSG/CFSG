module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.Closure

/-!
# The original seed and its two component supports

Vanishing of the full orbit-fixed subgroup in the central Hall context turns
Irr-plus minimality into actual irreducibility of the unchanged seed. Each
relative normal factor therefore either centralizes that seed or generates it
by commutators. If separation fails, both original factors move the whole
seed; conjugation by the full maximal normalizer extends this to the entire
full module. The final application gives crossed disjoint support or full
movement by both components, retaining the original exchanger and seed.

This is the support reduction for D.3.6--7 and 10.1.1. The tensor exclusion,
constituent recognition and final SeedAnalysisAt assembly remain with
qt-d-10-nona5-central-hall-orders. No source separation is asserted here.
Source: Aschbacher--Smith, printed pp.196--199,581 and741.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

private theorem seed_le_full : D.seed ≤ D.fullModule :=
  (le_componentOrbit D.seed T).trans (le_componentOrbit _ _)

/-- The original seed has no proper nonzero orbit-invariant subgroup in
 the central Hall context. -/
theorem seed_subgroup_eq_bot_or_top
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (J : Subgroup G) (hJS : J ≤ D.seed)
    (hOJ : localOrbit T L ≤ normalizer (J : Set G)) :
    J = ⊥ ∨ J = D.seed := by
  rcases ReducedNormal.subspaceImage_eq_or_le_centralizer (localJoin T L)
      (localOrbit T L) le_sup_left D.homogeneous.isIrrPlus J hJS hOJ with he | hc
  · exact Or.inr he
  · left
    apply bot_unique
    intro x hx
    have hh : (⟨x,seed_le_full D (hJS hx)⟩ : D.fullModule) ∈ D.fullCentralizer := hc hx
    rw [fullCentralizer_eq_bot_of_central_hstar D c] at hh
    exact mem_bot.mpr (congrArg Subtype.val (mem_bot.mp hh))

local instance : IsElementaryAbelian 2 D.seed := by
  let := D.module_elementary
  exact IsElementaryAbelian.of_injective
    (inclusion (show D.seed ≤ D.moduleSubgroup from le_componentOrbit D.seed T))
    (inclusion_injective _)

/-- Conjugation by the original component orbit on the unchanged seed. -/
@[expose] noncomputable def originalSeedAction :
    Representation (ZMod 2) (localOrbit T L) (Additive D.seed) :=
  Representation.elementaryRepresentation
    (D.seed.normalizerMonoidHom.comp (inclusion D.orbit_normalizes_seed))

/-- The original seed, with no quotient or replacement, is irreducible for L₀
 in the central Hall context. -/
theorem originalSeedAction_irreducible
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B) :
    (originalSeedAction D).IsIrreducible := by
  let : Nontrivial D.seed := (Subgroup.nontrivial_iff_ne_bot D.seed).mpr D.seed_ne_bot
  let d : Representation.BinaryConjugationSection (localOrbit T L) D.seed ⊥
      (originalSeedAction D) := {
    section_le := (le_componentOrbit D.seed T).trans D.module_le_orbit
    kernel_le := bot_le
    normalized := D.orbit_normalizes_seed
    coordinates := {
      toFun v := Multiplicative.ofAdd (Additive.ofMul v)
      map_one' := rfl
      map_mul' _ _ := rfl }
    onto := fun v => ⟨v.toAdd.toMul,rfl⟩
    kernel_eq := by ext v; simp
    equivariant := fun _ _ => rfl }
  apply d.irreducible_of_subgroup_minimal
  intro J hJS hOJ
  exact (seed_subgroup_eq_bot_or_top D c J hJS hOJ).symm.imp id (fun h => h.le)

/-- Every relative normal factor either centralizes the original seed or
 generates all of it by commutators. -/
theorem seed_factor_movement
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (A : Subgroup G) (hAO : A ≤ localOrbit T L)
    (hAN : localOrbit T L ≤ normalizer (A : Set G)) :
    D.seed ≤ centralizer (A : Set G) ∨ ⁅D.seed,A⁆ = D.seed := by
  have hAS : A ≤ normalizer (D.seed : Set G) := hAO.trans D.orbit_normalizes_seed
  have hnorm : localOrbit T L ≤ normalizer (↑(⁅D.seed,A⁆ : Subgroup G) : Set G) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (D.orbit_normalizes_seed hx),
      mem_normalizer_iff_map_conj_eq.mp (hAN hx)]
  exact (seed_subgroup_eq_bot_or_top D c ⁅D.seed,A⁆
    (le_normalizer_iff_commutator_le_left.mp hAS) hnorm).imp
      (fun he => commutator_eq_bot_iff_le_centralizer.mp he) id

private theorem opposite_normalized
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) :
    localOrbit T L ≤ normalizer (L.map (MulAut.conj t).toMonoidHom : Set G) := by
  have hh := map_mono (f := (MulAut.conj t).toMonoidHom)
    (le_normalizer_iff_commutator_le_left.mp (source_nonnormal_orbit_le_normalizer D hn))
  have ho : (localOrbit T L).map (MulAut.conj t).toMonoidHom = localOrbit T L :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_componentOrbit L T ht)
  rw [map_commutator,ho] at hh
  exact le_normalizer_iff_commutator_le_left.mpr hh

/-- Failure of separation makes both original components generate the same
 seed. This uses the literal original seed, in either orientation. -/
theorem seed_both_factors_moved_of_not_separated
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) :
    ⁅D.seed,L⁆ = D.seed ∧ ⁅D.seed,L.map (MulAut.conj t).toMonoidHom⁆ = D.seed := by
  have hp := componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
    (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 c.nonnormal)
    inf_le_right ht htn
  exact ⟨(seed_factor_movement D c L (le_componentOrbit L T)
      (source_nonnormal_orbit_le_normalizer D c.nonnormal)).resolve_left
        (fun hc => hsep (Or.inr hc)),
    (seed_factor_movement D c _ (le_sup_right.trans hp.symm.le)
      (opposite_normalized D c.nonnormal ht)).resolve_left (fun hc => hsep (Or.inl hc))⟩

/-- In the nonseparated branch each component moves the entire full module.
 This is a tensor-support statement, not irreducibility for one component. -/
theorem full_both_factors_moved_of_not_separated
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) :
    ⁅D.fullModule,L⁆ = D.fullModule ∧
      ⁅D.fullModule,L.map (MulAut.conj t).toMonoidHom⁆ = D.fullModule := by
  obtain ⟨hleft,hright⟩ := seed_both_factors_moved_of_not_separated D c ht htn hsep
  have hfull : ⁅D.fullModule,L⁆ = D.fullModule := by
    apply le_antisymm (moved_le_fullModule D)
    conv_lhs => rw [D.fullModule_eq_seed_orbit]
    apply iSup_le
    intro m
    have hs : D.seed.map (MulAut.conj (m : G)).toMonoidHom ≤ D.fullModule :=
      (map_mono (seed_le_full D)).trans_eq
        (mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule m.property))
    have hh := source_nonnormal_maximal_pair D c.nonnormal ht htn (m:G)⁻¹
      (D.maximalLocal.inv_mem m.property)
    have hmove : ⁅D.seed,L.map (MulAut.conj (m:G)⁻¹).toMonoidHom⁆ = D.seed := by
      rcases hh with he | he
      · simpa only [he] using hleft
      · simpa only [he] using hright
    have he := congrArg (fun J : Subgroup G => J.map (MulAut.conj (m:G)).toMonoidHom) hmove
    have hi : (L.map (MulAut.conj (m:G)⁻¹).toMonoidHom).map
        (MulAut.conj (m:G)).toMonoidHom = L := by
      rw [map_map]
      have hid : (MulAut.conj (m:G)).toMonoidHom.comp
          (MulAut.conj (m:G)⁻¹).toMonoidHom = MonoidHom.id G := by
        ext x
        simp [MulAut.conj_apply,mul_assoc]
      rw [hid,map_id]
    rw [map_commutator,hi] at he
    exact he.ge.trans (commutator_mono hs le_rfl)
  refine ⟨hfull,?_⟩
  have hh := congrArg (fun J : Subgroup G => J.map (MulAut.conj t).toMonoidHom) hfull
  have hv : D.fullModule.map (MulAut.conj t).toMonoidHom = D.fullModule :=
    mem_normalizer_iff_map_conj_eq.mp
      (D.maximalLocal_normalizes_fullModule (le_normalizer_componentOrbit L T ht))
  simpa only [map_commutator,hv] using hh

/-- The original Hall module has either crossed disjoint support or full
 movement by both components. No stability, module equality or constituent
 hypothesis is supplied. -/
theorem source_crossed_or_tensor_support
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    (⁅D.fullModule,L⁆ ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∧
      Disjoint ⁅D.fullModule,L⁆ ((⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)) ∨
    (⁅D.fullModule,L⁆ = D.fullModule ∧
      ⁅D.fullModule,L.map (MulAut.conj t).toMonoidHom⁆ = D.fullModule) := by
  by_cases hs : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)
  · exact Or.inl ⟨full_moved_centralizes_opposite_of_seed_separated D ht htn hs,
      moved_pair_disjoint_of_seed_separated D c ht htn hs⟩
  · exact Or.inr (full_both_factors_moved_of_not_separated D c ht htn hs)

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
