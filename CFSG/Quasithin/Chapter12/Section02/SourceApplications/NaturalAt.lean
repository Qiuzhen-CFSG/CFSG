module

public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter12.Section08.Setup.FlagGeometry

/-!
# Natural-module geometry from same-ambient Chapter12 inputs

The full natural L-action constructs the flag. The kernel on LT is a
normal two-group: its intersection with L embeds into O₂(L), and LT/L
is a two-group. This identifies the literal kernel with O₂(LT).
The full local 12.2.13 alternatives give escape after aligning the block
parameter with the original natural rank. These facts feed the unchanged
local center-product theorem, including its conjugate-containment antecedent.

These are ambient-local versions of Setup.NaturalActions, Setup.Escape and
Setup.Consumers; their universal public APIs remain unchanged. The structural
and recognition producers remain explicit. Source: Aschbacher--Smith,
12.2.13, 12.8.3 and 12.8.10(5), printed pp.799,850,854.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section08.HigherRankHypothesis
open Section02 InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
variable (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
include h

/-- Normalization of the original component at this ambient Sylow. -/
theorem sylow_normalizes_at (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    (T : Subgroup G) ≤ normalizer (L : Set G) := (structural L h.source).1

/-- Invariance of this original chosen module. -/
theorem sylow_normalizes_seed_at (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    (T : Subgroup G) ≤ normalizer (V : Set G) :=
  ((structural L h.source).2.2 V h.chosen).1

/-- The same normalizer and exact maximal-overgroup set, using full A/C. -/
theorem maximal_unique_at (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    IsMaximalTwoLocal (normalizer (L : Set G)) ∧
    {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N} =
      {normalizer (L : Set G)} := by
  have hu := structural.maximal_unique h.source
  refine ⟨hu.1, ?_⟩
  ext N
  constructor
  · rintro ⟨hN, hLN⟩
    exact Set.mem_singleton_iff.mpr (hu.2 N hN hLN)
  · intro hN
    obtain rfl := Set.mem_singleton_iff.mp hN
    exact ⟨hu.1, sup_le L.le_normalizer (h.sylow_normalizes_at structural)⟩

/-- Normalizer control at the same original V. -/
theorem seed_normalizer_le_at (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    normalizer (V : Set G) ≤ normalizer (L : Set G) :=
  structural.chosen_normalizer_le h.source h.chosen

theorem full_LT_action_at (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    Function.Surjective (setupSeedAction (L ⊔ (T : Subgroup G)) V
      (sup_le h.chosen.normalizes (h.sylow_normalizes_seed_at structural))) := by
  intro a
  obtain ⟨x, hx, he⟩ := h.full_L_action a
  refine ⟨⟨x, (le_sup_left : L ≤ L ⊔ (T : Subgroup G)) hx⟩, ?_⟩
  ext v
  exact he v

/-- The full LT action has two-group kernel, by the extension LT/L. -/
theorem action_kernel_isPGroup_at (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    IsPGroup 2 (setupSeedAction (L ⊔ (T : Subgroup G)) V
      (sup_le h.chosen.normalizes (h.sylow_normalizes_seed_at structural))).ker := by
  let J := L ⊔ (T : Subgroup G)
  let N := L.subgroupOf J
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer
    (show L ≤ J from le_sup_left)).mpr
      (sup_le L.le_normalizer (h.sylow_normalizes_at structural))
  have hgen : N ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    rw [← subgroupOf_sup (show L ≤ J from le_sup_left)
      (show (T : Subgroup G) ≤ J from le_sup_right)]
    exact subgroupOf_self J
  have hquot : IsPGroup 2 (J ⧸ N) := isPGroup_quotient_of_sup_eq_top N
    ((T : Subgroup G).subgroupOf J) T.isPGroup'.comap_subtype hgen
  let f := setupSeedAction J V
    (sup_le h.chosen.normalizes (h.sylow_normalizes_seed_at structural))
  let q := (QuotientGroup.mk' N).comp f.ker.subtype
  have hqker : IsPGroup 2 q.ker := by
    let r : q.ker →* L :=
      (J.subtype.comp (f.ker.subtype.comp q.ker.subtype)).codRestrict L (by
        intro x
        exact (QuotientGroup.eq_one_iff (N := N) x.val.val).mp x.property)
    have hr : ∀ x : q.ker, r x ∈ pCore 2 L := by
      intro x
      have hc : (x.val.val : G) ∈ centralizer (V : Set G) := by
        exact (setupSeedAction_ker J V _).le x.val.property
      have hx : (r x : G) ∈ L.pCoreIn 2 :=
        h.centralizer_L ▸ show (r x : G) ∈ L ⊓ centralizer (V : Set G)
          from ⟨(r x).property, hc⟩
      obtain ⟨y, hy, he⟩ := hx
      exact (Subtype.ext he : y = r x) ▸ hy
    let r' : q.ker →* pCore 2 L := r.codRestrict _ hr
    apply pCore_isPGroup.of_injective r'
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : pCore 2 L => (x.val : G)) hab
  have hp := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup q hqker
  rw [comap_top] at hp
  exact hp.of_equiv topEquiv

/-- The literal equality C_LT(V)=O₂(LT), as required by LocalKernel. -/
theorem centralizer_LT_at (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let J := L ⊔ (T : Subgroup G)
  let f := setupSeedAction J V
    (sup_le h.chosen.normalizes (h.sylow_normalizes_seed_at structural))
  have hk : f.ker ≤ pCore 2 J := le_sSup ⟨inferInstance, h.action_kernel_isPGroup_at structural⟩
  have hm := map_mono (f := J.subtype) hk
  rw [setupSeedAction_ker, subgroupOf_map_subtype, inf_comm] at hm
  exact le_antisymm hm (le_inf (map_subtype_le _) h.chosen.core_centralizes)

/-- Apply all four ambient-local alternatives and eliminate its three actual
global alternatives. No escape premise for this setup is assumed. -/
theorem exists_escaping_vector_at (earlier : Theorem12213At KnownSimple.IsKnownSimple T) :
    ∃ v ∈ V, v ≠ 1 ∧ ¬ centralizer ({v} : Set G) ≤ normalizer (L : Set G) := by
  rcases earlier L V h.source h.chosen with hv | hl | ha | hm
  · exact hv
  · obtain ⟨d, hd, hb, hg⟩ := hl
    have he := h.block_parameter hd hb
    subst d
    exact (h.no_nextLinear hg).elim
  · exact (h.no_A9 ha.2).elim
  · exact (h.no_M24 hm.2).elim

/-- Escape holds at every nonidentity element of the chosen V. -/
theorem vector_centralizer_escape_at (earlier : Theorem12213At KnownSimple.IsKnownSimple T)
    {x : G} (hx : x ∈ V) (hx1 : x ≠ 1) :
    ¬ centralizer ({x} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨v, hv, hv1, hescape⟩ := h.exists_escaping_vector_at earlier
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

/-- Actual application to the marked source point normalizer. -/
theorem flag_escape_at (F : InvariantFlag T V n) (earlier : Theorem12213At KnownSimple.IsKnownSimple T) :
    ¬ F.H ≤ normalizer (L : Set G) := by
  have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by have := h.rank; omega)
  have hne : F.Vi 1 ≠ ⊥ := by intro he; simp [he] at hc
  obtain ⟨x', hx'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  let x : G := x'
  have hx : x ∈ F.Vi 1 := x'.property
  have hx1 : x ≠ 1 := fun he => hx' (Subtype.ext he)
  intro hH
  apply h.vector_centralizer_escape_at earlier (F.le_seed 1 hx) hx1
  have hpoint : F.Vi 1 = zpowers x := by
    have hxe : (⟨x, hx⟩ : F.Vi 1) ≠ 1 := fun he => hx1 (congrArg Subtype.val he)
    have hg := zpowers_eq_top_of_prime_card hc hxe
    have hm := congrArg (map (F.Vi 1).subtype) hg
    simpa only [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map,
      range_subtype, Subgroup.coe_subtype] using hm.symm
  rw [← F.H_eq_centralizer (by have := h.rank; omega) x hpoint]
  exact hH

/-- The existing SourceGeometry consumer now has its escape premise discharged. -/
theorem point_mem_Hz_at (F : InvariantFlag T V n) (earlier : Theorem12213At KnownSimple.IsKnownSimple T) :
    F.H ∈ F.Hz L (normalizer (L : Set G)) :=
  F.H_mem_Hz (by have := h.rank; omega) L _ (h.flag_escape_at F earlier)

/-- Construct Notation 12.8.2 and the omitted-point conjugator from the source
higher-rank hypothesis and its ambient-local structural predecessor. -/
theorem exists_flag_geometry_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    primeRank 2 V = n ∧ ∃ F : InvariantFlag T V n,
      (∀ i, i ≤ n → ∀ A : Subgroup G, A ≤ V → Nat.card A = 2 ^ i →
        (T : Subgroup G) ≤ normalizer (A : Set G) → A = F.Vi i) ∧
      ∃ z : G, z ≠ 1 ∧ F.Vi 1 = zpowers z ∧ ∃ g : G, g ∈ F.P L ∧ g ∉ F.H := by
  let := h.chosen.elementary
  exact SetupFlagGeometry.exists_flag_geometry (by have := h.rank; omega) h.seed_card
    h.chosen.normalizes (h.sylow_normalizes_seed_at structural) (h.full_LT_action_at structural)

/-- All nongeneric geometry inputs to the existing LocalKernel center-product
consumer are derived from the original higher-rank source alternative. -/
theorem localKernel_center_product_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (recognition : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    conjugate F.ZU g ≤ F.U →
      (F.ZU = centerIn (F.I₂ L) ⊔ F.Vi 1 ∧
        Disjoint (centerIn (F.I₂ L)) (F.Vi 1) ∧
        ∃ e : centerIn (F.I₂ L) × F.Vi 1 ≃* F.ZU,
          ∀ a b, (e (a, b) : G) = (a : G) * (b : G)) ∧
      ⁅L, centerIn (F.I₂ L)⁆ = ⊥ := by
  let := h.chosen.elementary
  exact F.localKernel_source_center_product h.source.simpleQTKE L (normalizer (L : Set G))
    ⟨by have := h.rank; omega, h.rank.2⟩ h.chosen.le_sylow h.chosen.normalizes
    (h.sylow_normalizes_at structural) h.residual
    (fun _ => ⟨h.naturalMarking⟩) rfl
    (h.maximal_unique_at structural).2
    ((Subgroup.centralizer_le_normalizer _).trans (h.seed_normalizer_le_at structural))
    h.centralizer_L (h.flag_escape_at F recognition)
    (h.binarySeedAction_surjective F) (fun _ => h.full_L_action)
    (h.centralizer_LT_at structural) hne g hgP hgH

end CFSG.Quasithin.Chapter12.Section08.HigherRankHypothesis
