module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.MovedCubic
public import CFSG.Quasithin.Chapter10.SourceA5OriginalIrreducibility.MaximalAction
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Reconstructing the original seed from a stable constituent

Separation of the original seed propagates around its full M-orbit and
makes the two moved factors disjoint in the central Hall context. If a
subgroup of W = [V_M,L] is invariant under M ∩ N(L), its M-orbit is the
join of that subgroup and its exchanged conjugate. Minimality of V_M and
the product-order formula force this subgroup to be W or trivial.

Consequently an actual N_M(L)-invariant L-Irr⁺ constituent inside W makes
W L-minimal. In either orientation, the original seed is then W or its
exchanged conjugate, proving its N_T(L)-stability and V_M = V_T without
replacing the original FundamentalSetup. The existence of separation and
the invariant constituent remain source obligations of this owner.

Source: Aschbacher--Smith D.3.6, D.3.21(3), and the reselection in 3.2.6,
printed pp.196,204--207,581; central Hall application in 10.2.3, p.745.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

omit [Finite G] in
private theorem conjugate_map_eq (A : Subgroup G) {g : G}
    (hg : g ∈ normalizer (A : Set G)) : A.map (MulAut.conj g).toMonoidHom = A :=
  mem_normalizer_iff_map_conj_eq.mp hg

private theorem seed_conjugate_separated
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)) (m : D.maximalLocal) :
    D.seed.map (MulAut.conj (m : G)).toMonoidHom ≤ centralizer (L : Set G) ∨
    D.seed.map (MulAut.conj (m : G)).toMonoidHom ≤
      centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hpair := source_nonnormal_maximal_pair D hn ht htn
  rcases hsep with hs | hs
  · have hh := map_mono (f := (MulAut.conj (m : G)).toMonoidHom) hs
    rw [Theory.GroupTheory.map_centralizer_equiv] at hh
    change D.seed.map (MulAut.conj (m : G)).toMonoidHom ≤
      centralizer (((L.map (MulAut.conj t).toMonoidHom).map
        (MulAut.conj (m : G)).toMonoidHom) : Set G) at hh
    rw [map_map] at hh
    have he : (MulAut.conj (m : G)).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
        (MulAut.conj ((m : G)*t)).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply,mul_assoc]
    rw [he] at hh
    rcases hpair ((m : G)*t)
        (D.maximalLocal.mul_mem m.property (le_normalizer_componentOrbit L T ht)) with he | he
    · rw [he] at hh
      exact Or.inl hh
    · rw [he] at hh
      exact Or.inr hh
  · have hh := map_mono (f := (MulAut.conj (m : G)).toMonoidHom) hs
    rw [Theory.GroupTheory.map_centralizer_equiv] at hh
    change D.seed.map (MulAut.conj (m : G)).toMonoidHom ≤
      centralizer ((L.map (MulAut.conj (m : G)).toMonoidHom) : Set G) at hh
    rcases hpair m m.property with he | he
    · rw [he] at hh
      exact Or.inl hh
    · rw [he] at hh
      exact Or.inr hh

/-- Separation propagates through the full M-orbit, without local/full equality. -/
theorem full_moved_centralizes_opposite_of_seed_separated
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)) :
    ⁅D.fullModule,L⁆ ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hnorm : D.fullModule ≤ normalizer
      (centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) : Set G) := by
    have hO : localOrbit T L ≤ normalizer (L.map (MulAut.conj t).toMonoidHom : Set G) := by
      -- Normalization is transported through its commutator characterization.
      have hb : ⁅L,localOrbit T L⁆ ≤ L :=
        le_normalizer_iff_commutator_le_left.mp (source_nonnormal_orbit_le_normalizer D hn)
      have hc := map_mono (f := (MulAut.conj t).toMonoidHom) hb
      rw [map_commutator,conjugate_map_eq (localOrbit T L)
        (le_normalizer_componentOrbit L T ht)] at hc
      exact le_normalizer_iff_commutator_le_left.mpr hc
    exact D.fullModule_le_orbit.trans
      (hO.trans (normalizer_le_normalizer_centralizer _))
  conv_lhs => rw [D.fullModule_eq_seed_orbit]
  apply commutator_iSup_le_of_relative_normal D.fullModule L _ _ hnorm
  · intro m
    exact le_iSup (fun g : D.maximalLocal =>
      D.seed.map (MulAut.conj (g : G)).toMonoidHom) m |>.trans_eq
        D.fullModule_eq_seed_orbit.symm
  · intro m
    rcases seed_conjugate_separated D ht htn hsep m with hc | hc
    · exact (commutator_eq_bot_iff_le_centralizer.mpr hc).le.trans bot_le
    · have hh := map_mono (f := (MulAut.conj (m : G)).toMonoidHom)
        (le_normalizer_iff_commutator_le_left.mp D.orbit_normalizes_seed)
      rw [map_commutator,conjugate_map_eq (localOrbit T L) m.property] at hh
      exact ((commutator_mono le_rfl (le_componentOrbit L T)).trans hh).trans hc

/-- The full crossed conclusion needs only separation of the original seed. -/
theorem crossed_of_seed_separated
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)) :
    ∀ s ∈ (T : Subgroup G), s ∉ normalizer (L : Set G) →
      (⁅D.fullModule,L⁆).map (MulAut.conj s).toMonoidHom ≤ centralizer (L : Set G) := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  apply crossed_of_one D ht htn
  have hh := map_mono (f := (MulAut.conj t).toMonoidHom)
    (full_moved_centralizes_opposite_of_seed_separated D ht htn hsep)
  rw [Theory.GroupTheory.map_centralizer_equiv] at hh
  change (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤
    centralizer (((L.map (MulAut.conj t).toMonoidHom).map
      (MulAut.conj t).toMonoidHom) : Set G) at hh
  rw [conjugate_twice_eq_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn)
      inf_le_right ht] at hh
  exact hh


/-- The paired moved subgroup identity for any original Sylow exchanger. -/
theorem fullModule_pair_at
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    D.fullModule = ⁅D.fullModule,L⁆ ⊔
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  obtain ⟨s,hs,hsn,_,hV,_⟩ := source_nonnormal_fullModule_pair D hn
  have he : L.map (MulAut.conj s).toMonoidHom = L.map (MulAut.conj t).toMonoidHom :=
    (source_nonnormal_maximal_pair D hn ht htn s
      (le_normalizer_componentOrbit L T hs)).resolve_left
      (fun he => hsn (mem_normalizer_iff_map_conj_eq.mpr he))
  have hv (g : G) (hg : g ∈ (T : Subgroup G)) :
      D.fullModule.map (MulAut.conj g).toMonoidHom = D.fullModule :=
    mem_normalizer_iff_map_conj_eq.mp
      (D.maximalLocal_normalizes_fullModule (le_normalizer_componentOrbit L T hg))
  rw [map_commutator,hv s hs,he] at hV
  simpa only [map_commutator,hv t ht] using hV

private theorem seed_eq_active_moved
    (A B : Subgroup G) (hpair : localOrbit T L = A ⊔ B)
    (hsep : D.seed ≤ centralizer (B : Set G)) : D.seed = ⁅D.seed,A⁆ := by
  have hseed : D.seed = ⁅D.seed,localOrbit T L⁆ :=
    ReducedNormal.subspaceImage_eq_commutator (localJoin T L) D.seedSpace
      (localOrbit T L) le_sup_left D.homogeneous.invariant
      D.homogeneous.isIrrPlus.choose_spec.1
  have hAN : A ≤ normalizer (D.seed : Set G) :=
    (le_sup_left.trans hpair.ge).trans D.orbit_normalizes_seed
  exact hseed.trans (commutator_eq_of_centralizing_sup
    (by simpa only [sup_comm] using hpair.symm)
    (le_centralizer_iff.mp hsep) hAN).symm

private theorem seed_eq_moved_of_minimal
    (hmin : MovedMinimal D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G)) :
    D.seed = ⁅D.fullModule,L⁆ := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hp := componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
    (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn)
    inf_le_right ht htn
  have he := seed_eq_active_moved D L _ hp hsep
  have hsW : D.seed ≤ ⁅D.fullModule,L⁆ := by
    rw [he]
    exact commutator_mono ((le_componentOrbit D.seed T).trans (le_componentOrbit _ _)) le_rfl
  rcases hmin D.seed hsW ((le_componentOrbit L T).trans D.orbit_normalizes_seed) with h | h
  · exact h
  · exact (D.seed_ne_bot (he.trans (commutator_eq_bot_iff_le_centralizer.mpr h))).elim

/-- Multiplicity one on the actual moved subgroup recovers every seed clause,
including stability and local/full equality, in either orientation. -/
theorem separatedSeed_of_separated_and_movedMinimal
    (hmin : MovedMinimal D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)) : SeparatedSeed D t := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hi := source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn
  have hp := componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G)) hi
    inf_le_right ht htn
  have hsV : D.seed ≤ D.moduleSubgroup := le_componentOrbit _ _
  have hstabW : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤
      normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
    intro s hs
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅D.fullModule,L⁆).map (MulAut.conj s).toMonoidHom = ⁅D.fullModule,L⁆
    rw [map_commutator,conjugate_map_eq L hs.2,
      conjugate_map_eq D.fullModule
        (D.maximalLocal_normalizes_fullModule (le_normalizer_componentOrbit L T hs.1))]
  have hseed : D.seed = ⁅D.fullModule,L⁆ ∨
      D.seed = (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom := by
    rcases hsep with hc | hc
    · exact Or.inl (seed_eq_moved_of_minimal D hmin ht htn hc)
    · have he : D.seed = ⁅D.seed,L.map (MulAut.conj t).toMonoidHom⁆ :=
        seed_eq_active_moved D _ L (by simpa only [sup_comm] using hp) hc
      let U := D.seed.map (MulAut.conj t⁻¹).toMonoidHom
      have hcancel (J : Subgroup G) :
          (J.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t⁻¹).toMonoidHom = J := by
        rw [map_map]
        have h : (MulAut.conj t⁻¹).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
            MonoidHom.id G := by ext x; simp [MulAut.conj_apply,mul_assoc]
        rw [h,map_id]
      have hcomm : U = ⁅U,L⁆ := by
        have hh := congrArg (map (MulAut.conj t⁻¹).toMonoidHom) he
        rw [map_commutator,hcancel] at hh
        exact hh
      have hUV : U ≤ D.fullModule := by
        exact (map_mono (f := (MulAut.conj t⁻¹).toMonoidHom)
          (hsV.trans (le_componentOrbit _ _))).trans_eq
          (mem_normalizer_iff_map_conj_eq.mp
            (D.maximalLocal_normalizes_fullModule
              (le_normalizer_componentOrbit L T ((T : Subgroup G).inv_mem ht))))
      have hUW : U ≤ ⁅D.fullModule,L⁆ := by
        rw [hcomm]
        exact commutator_mono hUV le_rfl
      have hLU : L ≤ normalizer (U : Set G) := by
        have hh := map_mono (f := (MulAut.conj t⁻¹).toMonoidHom)
          (le_normalizer_iff_commutator_le_left.mp D.orbit_normalizes_seed)
        rw [map_commutator,conjugate_map_eq (localOrbit T L)
          (le_normalizer_componentOrbit L T ((T : Subgroup G).inv_mem ht))] at hh
        exact le_normalizer_iff_commutator_le_left.mpr
          ((commutator_mono le_rfl (le_componentOrbit L T)).trans hh)
      have hU : U = ⁅D.fullModule,L⁆ := by
        rcases hmin U hUW hLU with hh | hh
        · exact hh
        · have hz : U = ⊥ := hcomm.trans (commutator_eq_bot_iff_le_centralizer.mpr hh)
          exact (D.seed_ne_bot ((map_eq_bot_iff_of_injective D.seed (MulAut.conj t⁻¹).injective).mp hz)).elim
      right
      have hh := congrArg (map (MulAut.conj t).toMonoidHom) hU
      change (D.seed.map (MulAut.conj t⁻¹).toMonoidHom).map
        (MulAut.conj t).toMonoidHom = _ at hh
      rw [map_map] at hh
      have h : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t⁻¹).toMonoidHom =
          MonoidHom.id G := by ext x; simp [MulAut.conj_apply,mul_assoc]
      simpa only [h,map_id] using hh
  have hstab : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer (D.seed : Set G) := by
    rcases hseed with he | he
    · rw [he]
      exact hstabW
    · rw [he]
      intro s hs
      have hopp : (L.map (MulAut.conj t).toMonoidHom).map
          (MulAut.conj s).toMonoidHom = L.map (MulAut.conj t).toMonoidHom := by
        have hcomp : (L.map (MulAut.conj t).toMonoidHom).map
            (MulAut.conj s).toMonoidHom = L.map (MulAut.conj (s*t)).toMonoidHom := by
          rw [map_map]
          congr 1
          ext x
          simp [MulAut.conj_apply,mul_assoc]
        rw [hcomp]
        rcases source_nonnormal_maximal_pair D hn ht htn (s*t)
            (D.maximalLocal.mul_mem (le_normalizer_componentOrbit L T hs.1)
              (le_normalizer_componentOrbit L T ht)) with h | h
        · exfalso
          apply htn
          have hm := (normalizer (L : Set G)).mul_mem
            ((normalizer (L : Set G)).inv_mem hs.2)
            (mem_normalizer_iff_map_conj_eq.mpr h)
          simpa only [inv_mul_cancel_left] using hm
        · exact h
      apply mem_normalizer_iff_map_conj_eq.mpr
      change ((⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom).map
        (MulAut.conj s).toMonoidHom = (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom
      rw [map_commutator,conjugate_map_eq D.fullModule
        (D.maximalLocal_normalizes_fullModule (le_normalizer_componentOrbit L T ht)),
        map_commutator,conjugate_map_eq D.fullModule
        (D.maximalLocal_normalizes_fullModule (le_normalizer_componentOrbit L T hs.1)),hopp]
  refine ⟨?_,hstab,hsep⟩
  have hsplit := componentOrbit_eq_sup_of_index_two D.seed T (normalizer (L : Set G))
    hi hstab ht htn
  change D.fullModule = componentOrbit D.seed (T : Subgroup G)
  rw [fullModule_pair_at D ht htn,hsplit]
  rcases hseed with he | he
  · rw [he]
  · rw [he,conjugate_twice_eq_of_index_two ⁅D.fullModule,L⁆ T
      (normalizer (L : Set G)) hi hstabW ht,sup_comm]


/-- The full fixed part vanishes in the central Hall context, so separation
alone kills the central kernel of the whole moved subgroup. -/
theorem movedFixed_eq_bot_of_seed_separated
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)) : sourceMovedFixed D = ⊥ := by
  have hp : localOrbit T L = L ⊔ L.map (MulAut.conj t).toMonoidHom :=
    componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
    (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 c.nonnormal)
    inf_le_right ht htn
  have hc : sourceMovedFixed D ≤ centralizer (localOrbit T L : Set G) := by
    apply le_centralizer_iff.mpr
    rw [hp]
    exact sup_le (le_centralizer_iff.mp (show sourceMovedFixed D ≤ centralizer (L : Set G)
      from inf_le_right)) (le_centralizer_iff.mp
        (inf_le_left.trans (full_moved_centralizes_opposite_of_seed_separated D ht htn hsep)))
  apply bot_unique
  intro w hw
  have hm : (⟨w,moved_le_fullModule D hw.1⟩ : D.fullModule) ∈ D.fullCentralizer := hc hw
  rw [fullCentralizer_eq_bot_of_central_hstar D c] at hm
  exact mem_bot.mpr (congrArg Subtype.val (mem_bot.mp hm))

/-- The two literal moved factors have trivial intersection before proving
local/full equality or stability of the seed. -/
theorem moved_pair_disjoint_of_seed_separated
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)) :
    Disjoint ⁅D.fullModule,L⁆ ((⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) := by
  apply disjoint_iff.mpr
  apply bot_unique
  have hc := crossed_of_seed_separated D ht htn hsep t ht htn
  have hh : ⁅D.fullModule,L⁆ ⊓ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤
      sourceMovedFixed D := inf_le_inf_left _ hc
  simpa only [movedFixed_eq_bot_of_seed_separated D c ht htn hsep] using hh

/-- Crossed centralization separates the original Irr⁺ seed in the central
Hall context. No local/full equality is used. -/
theorem seed_separated_of_moved_centralizes_opposite
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G}
    (hcross : ⁅D.fullModule,L⁆ ≤
      centralizer (L.map (MulAut.conj t).toMonoidHom : Set G)) :
    D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G) := by
  have hsV : D.seed ≤ D.fullModule :=
    (le_componentOrbit D.seed T).trans (le_componentOrbit _ _)
  have hLS : L ≤ normalizer (D.seed : Set G) :=
    (le_componentOrbit L T).trans D.orbit_normalizes_seed
  have hJS : ⁅D.seed,L⁆ ≤ D.seed :=
    le_normalizer_iff_commutator_le_left.mp hLS
  have hOJ : localOrbit T L ≤ normalizer (↑(⁅D.seed,L⁆ : Subgroup G) : Set G) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅D.seed,L⁆).map (MulAut.conj x).toMonoidHom = ⁅D.seed,L⁆
    rw [map_commutator,conjugate_map_eq D.seed (D.orbit_normalizes_seed hx),
      conjugate_map_eq L (source_nonnormal_orbit_le_normalizer D c.nonnormal hx)]
  rcases ReducedNormal.subspaceImage_eq_or_le_centralizer (localJoin T L)
      (localOrbit T L) le_sup_left D.homogeneous.isIrrPlus ⁅D.seed,L⁆ hJS hOJ with he | hc
  · change ⁅D.seed,L⁆ = D.seed at he
    exact Or.inl (he.ge.trans ((commutator_mono hsV le_rfl).trans hcross))
  · right
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    intro x hx
    have hh : (⟨x,hsV (hJS hx)⟩ : D.fullModule) ∈ D.fullCentralizer := hc hx
    rw [fullCentralizer_eq_bot_of_central_hstar D c] at hh
    exact mem_bot.mpr (congrArg Subtype.val (mem_bot.mp hh))

/-- The seed clauses are exactly crossed centralization and multiplicity one
on the literal moved subgroup, under the original central Hall hypotheses. -/
theorem separatedSeed_iff_moved_minimal_and_crossed
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    SeparatedSeed D t ↔ MovedMinimal D ∧
      ⁅D.fullModule,L⁆ ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) := by
  constructor
  · intro hs
    exact ⟨(geometry_and_minimality_of_separatedSeed D ht htn hs).2,
      full_moved_centralizes_opposite_of_seed_separated D ht htn hs.separated⟩
  · rintro ⟨hmin,hcross⟩
    exact separatedSeed_of_separated_and_movedMinimal D hmin ht htn
      (seed_separated_of_moved_centralizes_opposite D c hcross)

private theorem fullOrbit_eq_pair_of_component_stable
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (J : Subgroup G)
    (hJ : D.maximalLocal ⊓ normalizer (L : Set G) ≤ normalizer (J : Set G)) :
    componentOrbit J D.maximalLocal = J ⊔ J.map (MulAut.conj t).toMonoidHom := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have htM : t ∈ D.maximalLocal := le_normalizer_componentOrbit L T ht
  apply le_antisymm
  · apply iSup_le
    intro m
    rcases source_nonnormal_maximal_pair D hn ht htn m m.property with he | he
    · rw [conjugate_map_eq J
        (hJ ⟨m.property,mem_normalizer_iff_map_conj_eq.mpr he⟩)]
      exact le_sup_left
    · have hm : t⁻¹ * (m : G) ∈ normalizer (L : Set G) := by
        apply mem_normalizer_iff_map_conj_eq.mpr
        calc
          L.map (MulAut.conj (t⁻¹ * (m : G))).toMonoidHom =
              (L.map (MulAut.conj (m : G)).toMonoidHom).map
                (MulAut.conj t⁻¹).toMonoidHom := by
            rw [map_map]
            congr 1
            ext x
            simp [MulAut.conj_apply,mul_assoc]
          _ = (L.map (MulAut.conj t).toMonoidHom).map
                (MulAut.conj t⁻¹).toMonoidHom := congrArg _ he
          _ = L := by
            rw [map_map]
            have h : (MulAut.conj t⁻¹).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
                MonoidHom.id G := by ext x; simp [MulAut.conj_apply,mul_assoc]
            rw [h,map_id]
      have hmap : J.map (MulAut.conj (m : G)).toMonoidHom =
          J.map (MulAut.conj t).toMonoidHom := by
        calc
          _ = (J.map (MulAut.conj (t⁻¹ * (m : G))).toMonoidHom).map
                (MulAut.conj t).toMonoidHom := by
            rw [map_map]
            congr 1
            ext x
            simp [MulAut.conj_apply,mul_assoc]
          _ = _ := congrArg (map (MulAut.conj t).toMonoidHom)
            (mem_normalizer_iff_map_conj_eq.mp
              (hJ ⟨D.maximalLocal.mul_mem (D.maximalLocal.inv_mem htM) m.property,hm⟩))
      rw [hmap]
      exact le_sup_right
  · exact sup_le (le_componentOrbit _ _)
      (le_iSup (fun m : D.maximalLocal => J.map (MulAut.conj (m : G)).toMonoidHom) ⟨t,htM⟩)

/-- Minimality of the full module gives irreducibility on W for the actual
component stabilizer in M, before any assertion of L-irreducibility. -/
theorem moved_minimal_under_component_stabilizer_of_seed_separated
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (J : Subgroup G) (hJW : J ≤ ⁅D.fullModule,L⁆)
    (hJ : D.maximalLocal ⊓ normalizer (L : Set G) ≤ normalizer (J : Set G)) :
    J = ⁅D.fullModule,L⁆ ∨ J = ⊥ := by
  let W := ⁅D.fullModule,L⁆
  have hWV : W ≤ D.fullModule := moved_le_fullModule D
  let U := componentOrbit J D.maximalLocal
  have hUV : U ≤ D.fullModule := iSup_conjugates_le_of_le_normalizer _ _ _
    (hJW.trans hWV) D.maximalLocal_normalizes_fullModule
  have hU := fullOrbit_eq_pair_of_component_stable D ht htn J hJ
  have hpair := fullModule_pair_at D ht htn
  have hdis := moved_pair_disjoint_of_seed_separated D c ht htn hsep
  rcases source_minimal_fullModule_eq_or_le_centralizer D c.minimal U
      (le_normalizer_componentOrbit _ _) hUV with he | hc
  · left
    have hjd : Disjoint J (J.map (MulAut.conj t).toMonoidHom) :=
      hdis.mono hJW (map_mono hJW)
    let := D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
    have hVV : D.fullModule ≤ centralizer (D.fullModule : Set G) :=
      le_centralizer_iff_isMulCommutative.mpr inferInstance
    have hJV : J ≤ D.fullModule := hJW.trans hWV
    have hWtV : W.map (MulAut.conj t).toMonoidHom ≤ D.fullModule :=
      (map_mono hWV).trans_eq (mem_normalizer_iff_map_conj_eq.mp
        (D.maximalLocal_normalizes_fullModule (le_normalizer_componentOrbit L T ht)))
    have hJtV : J.map (MulAut.conj t).toMonoidHom ≤ D.fullModule :=
      (map_mono hJW).trans hWtV
    have hWWt : W.map (MulAut.conj t).toMonoidHom ≤ normalizer (W : Set G) :=
      ((hWtV.trans hVV).trans (centralizer_le hWV)).trans (Subgroup.centralizer_le_normalizer _)
    have hJJt : J.map (MulAut.conj t).toMonoidHom ≤ normalizer (J : Set G) :=
      ((hJtV.trans hVV).trans (centralizer_le hJV)).trans (Subgroup.centralizer_le_normalizer _)
    have hwc := card_sup_eq_mul_of_normalizes_of_disjoint W
      (W.map (MulAut.conj t).toMonoidHom) hWWt hdis
    have hjc := card_sup_eq_mul_of_normalizes_of_disjoint J
      (J.map (MulAut.conj t).toMonoidHom) hJJt hjd
    rw [←hpair,card_map_of_injective (MulAut.conj t).injective] at hwc
    change componentOrbit J D.maximalLocal = D.fullModule at he
    rw [←hU,he,card_map_of_injective (MulAut.conj t).injective] at hjc
    have hcard : Nat.card W ≤ Nat.card J := by nlinarith
    exact Subgroup.eq_of_le_of_card_ge hJW hcard
  · right
    apply bot_unique
    intro x hx
    have hh : (⟨x,hJW.trans hWV hx⟩ : D.fullModule) ∈ D.fullCentralizer :=
      hc (le_componentOrbit J D.maximalLocal hx)
    rw [fullCentralizer_eq_bot_of_central_hstar D c] at hh
    exact mem_bot.mpr (congrArg Subtype.val (mem_bot.mp hh))

/-- An actual invariant Irr⁺ constituent in W upgrades the proved stabilizer
minimality to L-minimality. The constituent can be reselected: it need not
be the seed originally stored in D. This is the transport needed by the
replacement in D.3.21(3). -/
theorem movedMinimal_of_stabilizer_invariant_constituent
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (I : Submodule (ZMod 2) (Additive (ReducedNormal.ModuleGroup (localJoin T L))))
    (hI : Representation.BinaryOffender.IsIrrPlus (ReducedNormal.representation (localJoin T L))
      (L.subgroupOf (localJoin T L)) I)
    (hIW : ReducedNormal.subspaceImage (localJoin T L) I ≤ ⁅D.fullModule,L⁆)
    (hstable : D.maximalLocal ⊓ normalizer (L : Set G) ≤
      normalizer (ReducedNormal.subspaceImage (localJoin T L) I : Set G)) :
    MovedMinimal D := by
  have he : ReducedNormal.subspaceImage (localJoin T L) I = ⁅D.fullModule,L⁆ :=
    (moved_minimal_under_component_stabilizer_of_seed_separated D c ht htn hsep _ hIW
      hstable).resolve_right
      (ReducedNormal.subspaceImage_ne_bot _ _ (hI.ne_bot _))
  intro J hJW hLJ
  rcases ReducedNormal.subspaceImage_eq_or_le_centralizer (localJoin T L)
      L ((le_componentOrbit L T).trans le_sup_left) hI J
      (hJW.trans_eq he.symm) hLJ with h | h
  · exact Or.inl (h.trans he)
  · exact Or.inr h

/-- The same replacement constituent reconstructs all three clauses for the
original seed, including its orientation, stabilizer, and full/local equality. -/
theorem separatedSeed_of_stabilizer_invariant_constituent
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (I : Submodule (ZMod 2) (Additive (ReducedNormal.ModuleGroup (localJoin T L))))
    (hI : Representation.BinaryOffender.IsIrrPlus (ReducedNormal.representation (localJoin T L))
      (L.subgroupOf (localJoin T L)) I)
    (hIW : ReducedNormal.subspaceImage (localJoin T L) I ≤ ⁅D.fullModule,L⁆)
    (hstable : D.maximalLocal ⊓ normalizer (L : Set G) ≤
      normalizer (ReducedNormal.subspaceImage (localJoin T L) I : Set G)) :
    SeparatedSeed D t :=
  separatedSeed_of_separated_and_movedMinimal D
    (movedMinimal_of_stabilizer_invariant_constituent D c ht htn hsep I hI hIW hstable)
    ht htn hsep

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules


