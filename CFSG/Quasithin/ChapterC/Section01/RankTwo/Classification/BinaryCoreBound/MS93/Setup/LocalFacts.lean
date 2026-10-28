module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Defs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.MSInputs
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.PGroup.CharacteristicPairReduction

/-!
# Local stabilizers and existence of the MS93 critical distance

For a two-subgroup R containing O₂(M), its normal core is exactly O₂(M).
The characteristic-kernel calculation therefore identifies Q_alpha with
that core through embedM, and identifies T_beta with the embedded R. The
local two-residual transports through the same embedding, giving the exact
comparison for [Q_alpha,Ltilde_alpha].

The omega-center of a nontrivial finite two-group is nontrivial. Its image
at beta lies in Z_alpha. MS3 makes the graph action faithful, so Z_alpha
cannot lie in every first-neighborhood kernel. Well ordering then supplies
the least critical distance and containment at every smaller distance.
No tree property or finite completion is needed for this existence argument.

Source: MS93 (1993), notation and elementary local clauses of 2.0--2.1,
printed pp.854--855. Evenness and the later critical-pair lemmas are separate.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
variable {M : Type*} [Group M] (R : Subgroup M)

theorem normalCore_eq_twoCore (hp : IsPGroup 2 R) (hc : pCore 2 M ≤ R) :
    R.normalCore = pCore 2 M :=
  le_antisymm (le_sSup ⟨inferInstance, hp.to_le R.normalCore_le⟩)
    (normal_le_normalCore.mpr hc)

theorem Q_alpha_comap [Finite M] (hp : IsPGroup 2 R) (hc : pCore 2 M ≤ R) :
    (Q R (alpha R)).comap (embedM R) = pCore 2 M :=
  (neighborhoodKernel_m_base_comap_eq_normalCore R).trans (normalCore_eq_twoCore R hp hc)

theorem Q_alpha [Finite M] (hp : IsPGroup 2 R) (hc : pCore 2 M ≤ R) :
    Q R (alpha R) = (pCore 2 M).map (embedM R) := by
  rw [← Q_alpha_comap R hp hc, map_comap_eq]
  apply (inf_eq_right.mpr ?_).symm
  intro x hx
  have hh : x ∈ Mbar R := (stabilizer_m_base R) ▸ hx.1
  exact hh

theorem Q_beta [Finite M] : Q R (beta R) = R.map (embedM R) := by
  change neighborhoodKernel R (hVertex R 1) = _
  rw [neighborhoodKernel_h_base_eq_Sbar]
  change (embedS R).range = _
  rw [← embedM_comp_subtype, MonoidHom.range_comp, R.range_subtype]

theorem Ltilde_alpha [Finite M] :
    Ltilde R (alpha R) = (pResidual 2 M).map (embedM R) := by
  rw [Ltilde, alpha, stabilizer_m_base]
  change (pResidual 2 (embedM R).range).map (embedM R).range.subtype = _
  rw [← map_pResidual_of_surjective 2 (embedM R).rangeRestrict
    (embedM R).rangeRestrict_surjective, map_map,
    MonoidHom.subtype_comp_rangeRestrict]

theorem core_alpha [Finite M] (hp : IsPGroup 2 R) (hc : pCore 2 M ≤ R)
    {L : Subgroup M} (hL : pResidual 2 M = L) :
    core R (alpha R) = (⁅pCore 2 M, L⁆).map (embedM R) := by
  rw [core, Q_alpha R hp hc, Ltilde_alpha, hL, map_commutator]

theorem omegaCenter_le {G : Type*} [Group G] (A : Subgroup G) : omegaCenter A ≤ A :=
  map_subtype_le _

theorem omegaCenter_le_center {G : Type*} [Group G] (A : Subgroup G) :
    omegaCenter A ≤ (center A).map A.subtype := map_mono (map_subtype_le _)

theorem omegaCenter_ne_bot {G : Type*} [Group G] (A : Subgroup G)
    [Finite A] (hp : IsPGroup 2 A) (hne : A ≠ ⊥) : omegaCenter A ≠ ⊥ := by
  let : Nontrivial A := (nontrivial_iff_ne_bot A).mpr hne
  have he := omega_center_ne_bot hp
  intro hb
  apply he
  apply le_bot_iff.mp
  intro x hx
  have hmem : (x : G) ∈ omegaCenter A := mem_map_of_mem A.subtype hx
  rw [hb] at hmem
  apply Subtype.ext
  exact hmem

theorem Z_le_VBall (a : Vertex R) (i : ℕ) : Z R a ≤ VBall R a i :=
  le_iSup_of_le a (le_iSup_of_le (by simp) le_rfl)

theorem VBall_mono (a : Vertex R) {i j : ℕ} (hij : i ≤ j) :
    VBall R a i ≤ VBall R a j := by
  apply iSup_le
  intro b
  apply iSup_le
  intro hb
  exact le_iSup_of_le b (le_iSup_of_le (hb.trans hij) le_rfl)

theorem criticalPair_exists (a : Vertex R) (he : ∃ n, CriticalRadius R a n) :
    ∃ a', CriticalPair R a a' he := by
  classical
  exact Nat.find_spec he

theorem Z_le_Q_of_dist_lt (a : Vertex R) (he : ∃ n, CriticalRadius R a n)
    {a' : Vertex R} (hlt : (cosetGraph R).dist a a' < criticalDistance R a he) :
    Z R a ≤ Q R a' := by
  classical
  by_contra hn
  exact Nat.find_min he hlt ⟨a', rfl, hn⟩

theorem criticalDistance_le (a : Vertex R) (he : ∃ n, CriticalRadius R a n)
    {a' : Vertex R} (hn : ¬ Z R a ≤ Q R a') :
    criticalDistance R a he ≤ (cosetGraph R).dist a a' := by
  classical
  exact Nat.find_min' he ⟨a', rfl, hn⟩

theorem criticalRadius_exists_of_Z_ne_bot
    (hP : MSCharacteristicCondition R) (a : Vertex R) (hz : Z R a ≠ ⊥) :
    ∃ n, CriticalRadius R a n := by
  by_contra! hn
  apply hz
  apply le_bot_iff.mp
  rw [← actionKernel_eq_bot_of_characteristic R hP]
  intro x hx b
  have hle : Z R a ≤ Q R b := by
    by_contra hnb
    exact hn _ ⟨b, rfl, hnb⟩
  exact (hle hx).1

theorem omegaCenter_elementary {G : Type*} [Group G] (A : Subgroup G) :
    IsElementaryAbelian 2 (omegaCenter A) := by
  let : IsElementaryAbelian 2 (omega₁ (center A) (p := 2)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative (center A)
  let : IsElementaryAbelian 2 ((omega₁ (center A) (p := 2)).map (center A).subtype) :=
    IsElementaryAbelian.map _
  exact IsElementaryAbelian.map _

theorem mem_omegaCenter_iff {G : Type*} [Group G] {A : Subgroup G} {x : G} :
    x ∈ omegaCenter A ↔ x ∈ A ∧ x ^ 2 = 1 ∧ ∀ y ∈ A, y * x = x * y := by
  constructor
  · intro hx
    let := omegaCenter_elementary A
    refine ⟨omegaCenter_le A hx, elemPow_eq_one_of_isElementaryAbelian x hx, ?_⟩
    obtain ⟨z, hz, rfl⟩ := omegaCenter_le_center A hx
    intro y hy
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨y, hy⟩)
  · rintro ⟨hx, hp, hc⟩
    have hz : (⟨x, hx⟩ : A) ∈ center A := by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (hc y y.property)
    refine ⟨⟨x, hx⟩, ⟨⟨⟨x, hx⟩, hz⟩, ?_, rfl⟩, rfl⟩
    apply Subgroup.subset_closure
    change (⟨⟨x, hx⟩, hz⟩ : center A) ^ (2 ^ 1) = 1
    apply Subtype.ext
    apply Subtype.ext
    simpa using hp

theorem omegaCenter_map {G K : Type*} [Group G] [Group K]
    (A : Subgroup G) (f : G →* K) (hf : Function.Injective f) :
    omegaCenter (A.map f) = (omegaCenter A).map f := by
  ext x
  constructor
  · intro hx
    obtain ⟨⟨a, ha, rfl⟩, hp, hc⟩ := mem_omegaCenter_iff.mp hx
    refine ⟨a, mem_omegaCenter_iff.mpr ⟨ha, ?_, ?_⟩, rfl⟩
    · apply hf
      simpa using hp
    · intro b hb
      apply hf
      simpa using hc (f b) (mem_map_of_mem f hb)
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨ha, hp, hc⟩ := mem_omegaCenter_iff.mp ha
    apply mem_omegaCenter_iff.mpr
    refine ⟨mem_map_of_mem f ha, by simpa using congrArg f hp, ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    simpa using congrArg f (hc b hb)

theorem Z_alpha_ne_bot [Finite M] (hp : IsPGroup 2 R) (hne : R ≠ ⊥) :
    Z R (alpha R) ≠ ⊥ := by
  have hb : edgeOmega R (beta R) ≤ Z R (alpha R) := by
    change _ ≤ if color R (mVertex R 1) = false then _ else _
    rw [if_pos (show color R (mVertex R 1) = false from rfl)]
    exact le_iSup_of_le (beta R) (le_iSup_of_le (base_adjacent R) le_rfl)
  have hne' : edgeOmega R (beta R) ≠ ⊥ := by
    rw [edgeOmega, Q_beta, omegaCenter_map R (embedM R) (embedM_injective R)]
    intro h
    apply omegaCenter_ne_bot R hp hne
    apply le_bot_iff.mp
    intro x hx
    have hh0 : embedM R x ∈ (⊥ : Subgroup (FreeAmalgam R)) :=
      h ▸ mem_map_of_mem (embedM R) hx
    have hh : embedM R x = 1 := hh0
    apply embedM_injective R
    simpa using hh
  exact fun hz => hne' (le_bot_iff.mp (hz ▸ hb))

theorem criticalRadius_exists [Finite M]
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥) (hP : MSCharacteristicCondition R) :
    ∃ n, CriticalRadius R (alpha R) n :=
  criticalRadius_exists_of_Z_ne_bot R hP (alpha R) (Z_alpha_ne_bot R hp hne)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93
