module

public import CFSG.Quasithin.Chapter12.Section08.Setup.FlagGeometry
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.SourceKnownSimple

/-!
# The original higher-rank setup from same-ambient source results

The structural and recognition results are used only at the original G,T.
The known-simple source theorem supplies uniqueness directly, so no universal
EarlierSetupResults record is constructed from local implications. The actual
seed, its normalizer, invariant flag and escaping conjugator are retained.
The initial natural marking remains explicitly part of HigherRankHypothesis.
Source: Aschbacher--Smith 1.2.7, 12.8.2--3 and 12.9.2, pp.506,849--850,857.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section09.SourceAt
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

/-- Actual source normalizers and the unchanged seed's structural facts,
using the proved uniqueness theorem and only same-G,T structure. -/
theorem higherRank_normalizers_from_source_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    (T : Subgroup G) ≤ normalizer (L : Set G) ∧
      (T : Subgroup G) ≤ normalizer (V : Set G) ∧
      IsPReduced 2 (V.subgroupOf (L ⊔ (T : Subgroup G))) ∧
      (∀ g ∈ normalizer (L : Set G),
        V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
          V.map (MulAut.conj g).toMonoidHom = V) ∧
      IsMaximalTwoLocal (normalizer (L : Set G)) ∧
      {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N} =
        {normalizer (L : Set G)} ∧
      normalizer (V : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨hTL, _, hseeds⟩ := structural L h.source
  obtain ⟨hTV, hred, hTI, _⟩ := hseeds V h.chosen
  have horbit : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L (T : Subgroup G) L le_rfl hTL)
      (le_componentOrbit L _)
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple
    h.source.simpleQTKE T h.source.maximal_faithful.1
  have hm : IsMaximalTwoLocal (normalizer (L : Set G)) := by
    simpa only [horbit] using hu.normalizer_maximal
  have huniq : {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N} =
      {normalizer (L : Set G)} := by
    apply Set.ext
    intro N
    constructor
    · rintro ⟨hN, hLN⟩
      exact Set.mem_singleton_iff.mpr (by
        simpa only [horbit] using hu.normalizer_unique N hN hLN)
    · intro hN
      obtain rfl := Set.mem_singleton_iff.mp hN
      exact ⟨hm, sup_le L.le_normalizer hTL⟩
  refine ⟨hTL, hTV, hred, hTI, hm, huniq, ?_⟩
  let := h.chosen.elementary
  apply normalizer_le_of_unique_maximalTwoLocal (J := L ⊔ (T : Subgroup G))
  · intro N hN hJN
    exact Set.mem_singleton_iff.mp (huniq ▸
      show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
        from ⟨hN, hJN⟩)
  · exact IsElementaryAbelian.isPGroup 2 V
  · exact h.chosen.ne_bot
  · exact sup_le h.chosen.normalizes hTV

private theorem vector_escape
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (recognition : Theorem12213At KnownSimple.IsKnownSimple T)
    {x : G} (hx : x ∈ V) (hx1 : x ≠ 1) :
    ¬ centralizer ({x} : Set G) ≤ normalizer (L : Set G) := by
  have hex : ∃ v ∈ V, v ≠ 1 ∧
      ¬ centralizer ({v} : Set G) ≤ normalizer (L : Set G) := by
    rcases recognition L V h.source h.chosen with hv | hl | ha | hm
    · exact hv
    · obtain ⟨d, hd, hb, hg⟩ := hl
      have he := h.block_parameter hd hb
      subst d
      exact (h.no_nextLinear hg).elim
    · exact (h.no_A9 ha.2).elim
    · exact (h.no_M24 hm.2).elim
  obtain ⟨v, hv, hv1, hescape⟩ := hex
  obtain ⟨l, hl, he⟩ := h.vector_transitive hx hv hx1 hv1
  intro hc
  apply hescape
  intro y hy
  have hyc : l⁻¹ * y * l ∈ centralizer ({x} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have hyv := mem_centralizer_singleton_iff.mp hy
    rw [← he] at hyv
    have hh := congrArg (fun a : G => l⁻¹ * a * l) hyv
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, inv_mul_cancel,
      mul_one] using hh
  have hlM := L.le_normalizer hl
  have hyM := (normalizer (L : Set G)).mul_mem
    ((normalizer (L : Set G)).mul_mem hlM (hc hyc))
    ((normalizer (L : Set G)).inv_mem hlM)
  simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right, mul_inv_cancel,
    mul_one] using hyM

/-- The actual flag-point centralizer escapes the component normalizer from
the original recognition alternatives at this G,T. -/
theorem higherRank_flag_escape_from_source_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (recognition : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V n) : ¬ F.H ≤ normalizer (L : Set G) := by
  obtain ⟨z, hz, hpoint⟩ := SetupFlagGeometry.exists_point_generator F
    (by have := h.rank; omega)
  have hzV : z ∈ V := F.le_seed 1 (hpoint.symm ▸ mem_zpowers z)
  intro hH
  apply vector_escape h recognition hzV hz
  rw [← F.H_eq_centralizer (by have := h.rank; omega) z hpoint]
  exact hH

/-- Construct the original invariant flag and omitted-point conjugator,
including its point escape, solely from the same-ambient earlier sources. -/
theorem higherRank_flag_from_source_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (recognition : Theorem12213At KnownSimple.IsKnownSimple T) :
    primeRank 2 V = n ∧ ∃ F : InvariantFlag T V n,
      (∀ i, i ≤ n → ∀ A : Subgroup G, A ≤ V → Nat.card A = 2 ^ i →
        (T : Subgroup G) ≤ normalizer (A : Set G) → A = F.Vi i) ∧
      ¬ F.H ≤ normalizer (L : Set G) ∧
      ∃ z : G, z ≠ 1 ∧ F.Vi 1 = zpowers z ∧
        ∃ g : G, g ∈ F.P L ∧ g ∉ F.H := by
  let := h.chosen.elementary
  have hTV := ((structural L h.source).2.2 V h.chosen).1
  have hfull : Function.Surjective (setupSeedAction (L ⊔ (T : Subgroup G)) V
      (sup_le h.chosen.normalizes hTV)) := by
    intro a
    obtain ⟨x, hx, he⟩ := h.full_L_action a
    refine ⟨⟨x, (le_sup_left : L ≤ L ⊔ (T : Subgroup G)) hx⟩, ?_⟩
    ext v
    exact he v
  obtain ⟨hr, F, huniq, hex⟩ := SetupFlagGeometry.exists_flag_geometry
    (by have := h.rank; omega) h.seed_card h.chosen.normalizes hTV hfull
  exact ⟨hr, F, huniq, higherRank_flag_escape_from_source_at h recognition F, hex⟩

end CFSG.Quasithin.Chapter12.Section09.SourceAt
