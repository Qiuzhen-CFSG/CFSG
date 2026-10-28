module
public import Theory.GroupTheory.SylowNormalizerOuterAction
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.PGroup.OmegaAmbient
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Faithful actions on Sylow centers

In a simple group whose Sylow normalizer contains every proper Sylow
overgroup, the normalizer of a nontrivial characteristic Sylow subgroup
is the Sylow normalizer itself. A cyclic odd complement therefore covers
the full action when the Sylow subgroup acts trivially. Sylow-center fusion
and injective ambient transport retain the original normalizer and its
entire pointwise centralizer kernel.

Source: the rank-one argument in Aschbacher--Smith, Proposition 2.2.2,
printed pp.519--520; the unique-overgroup input is F.1.3(1), pp.259--260.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.SylowCenterAction
variable {K G : Type*} [Group K] [Group G]

structure Facts (Q : Subgroup K) : Prop where
  size : 2 < Nat.card Q
  cyclic : IsCyclic Q.normalizerMonoidHom.range
  odd : Odd (Nat.card Q.normalizerMonoidHom.range)
  transitive : ∀ a ∈ Q, a ≠ 1 → ∀ b ∈ Q, b ≠ 1 →
    ∃ n ∈ normalizer (Q : Set K), n * a * n⁻¹ = b

/-- The unique proper Sylow overgroup also normalizes every nontrivial
characteristic subgroup of that Sylow, in a simple group. -/
theorem normalizer_eq_of_unique_maximal [IsSimpleGroup K]
    (P : Sylow 2 K) (Q : Subgroup K) (hQ : Q ≠ ⊥) (hQP : Q ≤ P)
    (hN : normalizer (P : Set K) ≤ normalizer (Q : Set K))
    (hproper : normalizer (P : Set K) < ⊤)
    (hmax : ∀ B : Subgroup K, (P : Subgroup K) ≤ B → B < ⊤ →
      B ≤ normalizer (P : Set K)) :
    normalizer (Q : Set K) = normalizer (P : Set K) := by
  apply le_antisymm _ hN
  apply hmax _ (P.le_normalizer.trans hN)
  apply lt_top_iff_ne_top.mpr
  intro he
  let : Q.Normal := normalizer_eq_top_iff.mp he
  rcases (inferInstance : Q.Normal).eq_bot_or_eq_top with hb | ht
  · exact hQ hb
  · exact hproper.ne (top_unique (ht ▸ hQP.trans P.le_normalizer))

/-- A cyclic odd complement covers the entire action when the Sylow factor
centralizes the subgroup acted upon. -/
theorem cyclic_odd_of_complement [Finite K] (Q P D : Subgroup K)
    (hPD : D ≤ normalizer (P : Set K))
    (hN : normalizer (Q : Set K) = P ⊔ D)
    (hPC : P ≤ centralizer (Q : Set K))
    (hDcyc : IsCyclic D) (hDodd : Odd (Nat.card D)) :
    IsCyclic Q.normalizerMonoidHom.range ∧ Odd (Nat.card Q.normalizerMonoidHom.range) := by
  let := hDcyc
  have hPN : P ≤ normalizer (Q : Set K) := hPC.trans (centralizer_le_normalizer _)
  have hDN : D ≤ normalizer (Q : Set K) := hN.symm ▸ le_sup_right
  let f : D →* Q.normalizerMonoidHom.range :=
    Q.normalizerMonoidHom.rangeRestrict.comp (inclusion hDN)
  have hf : Function.Surjective f := by
    rintro ⟨a, n, rfl⟩
    have hn : (n : K) ∈ (P : Set K) * (D : Set K) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ hPD, ← hN]
      exact n.property
    obtain ⟨p, hp, d, hd, he⟩ := hn
    let pN : normalizer (Q : Set K) := ⟨p, hPN hp⟩
    let dN : normalizer (Q : Set K) := ⟨d, hDN hd⟩
    have hn : n = pN * dN := Subtype.ext he.symm
    have hp1 : Q.normalizerMonoidHom pN = 1 := by
      change pN ∈ Q.normalizerMonoidHom.ker
      rw [normalizerMonoidHom_ker]
      exact hPC hp
    refine ⟨⟨d, hd⟩, Subtype.ext ?_⟩
    change Q.normalizerMonoidHom dN = Q.normalizerMonoidHom n
    rw [hn, map_mul, hp1, one_mul]
  exact ⟨isCyclic_of_surjective f hf, Odd.of_dvd_nat hDodd (card_dvd_of_surjective f hf)⟩

/-- Conjugacy of central Sylow elements can be realized in its normalizer.
The inverse witnesses convert Mathlib's right-conjugation fusion formula. -/
theorem transitive_of_involution_fusion [Finite K] (P : Sylow 2 K) (Q : Subgroup K)
    (hQC : Q ≤ centralizer (P : Set K))
    (hN : normalizer (P : Set K) ≤ normalizer (Q : Set K))
    (horder : ∀ x ∈ Q, x ≠ 1 → orderOf x = 2)
    (hfusion : ∀ a b : K, orderOf a = 2 → orderOf b = 2 → IsConj a b) :
    ∀ a ∈ Q, a ≠ 1 → ∀ b ∈ Q, b ≠ 1 →
      ∃ n ∈ normalizer (Q : Set K), n * a * n⁻¹ = b := by
  intro a ha hane b hb hbne
  obtain ⟨g, hg⟩ := isConj_iff.mp (hfusion a b (horder a ha hane) (horder b hb hbne))
  have hh : (g⁻¹)⁻¹ * a * g⁻¹ ∈ centralizer (P : Set K) := by
    simpa only [inv_inv, hg] using hQC hb
  obtain ⟨n, hn, he⟩ := P.conj_eq_normalizer_conj_of_mem_centralizer a g⁻¹ (hQC ha) hh
  refine ⟨n⁻¹, hN ((normalizer (P : Set K)).inv_mem hn), ?_⟩
  simpa only [inv_inv, hg] using he.symm

private theorem map_normalizer (Q : Subgroup K) (f : K →* G) (hf : Function.Injective f) :
    (normalizer (Q : Set K)).map f = f.range ⊓ normalizer (Q.map f : Set G) := by
  apply le_antisymm (le_inf (map_le_range _ _) (le_normalizer_map f))
  rintro _ ⟨⟨x, rfl⟩, hx⟩
  refine ⟨x, ?_, rfl⟩
  have hh : (normalizer (Q.map f : Set G)).comap f = normalizer (Q : Set K) := by
    rw [comap_normalizer_eq_of_le_range (map_le_range _ _), comap_map_eq_self_of_injective hf]
  exact hh ▸ hx

/-- The full relative normalizer action on an injective image is conjugate
to the original full normalizer action, with its entire centralizer kernel. -/
theorem range_equiv_map (Q : Subgroup K) (f : K →* G) (hf : Function.Injective f) :
    Nonempty (Q.normalizerMonoidHom.range ≃*
      (normalizerAction f.range (Q.map f)).range) := by
  let eQ := Q.equivMapOfInjective f hf
  let eN := ((normalizer (Q : Set K)).equivMapOfInjective f hf).trans
    (MulEquiv.subgroupCongr (map_normalizer Q f hf))
  let eA := MulAut.congr eQ
  let a := normalizerAction f.range (Q.map f)
  have hc (n : normalizer (Q : Set K)) : eA (Q.normalizerMonoidHom n) = a (eN n) := by
    apply MulEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := eQ.surjective y
    apply Subtype.ext
    change (eQ (Q.normalizerMonoidHom n (eQ.symm (eQ x))) : G) = _
    rw [eQ.symm_apply_apply]
    change f ((n : K) * (x : K) * (n : K)⁻¹) =
      f (n : K) * f (x : K) * (f (n : K))⁻¹
    simp only [map_mul, map_inv]
  have he : Q.normalizerMonoidHom.range.map eA.toMonoidHom = a.range := by
    ext b
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨eN n, (hc n).symm⟩
    · rintro ⟨n, rfl⟩
      obtain ⟨m, rfl⟩ := eN.surjective n
      exact ⟨Q.normalizerMonoidHom m, ⟨m, rfl⟩, hc m⟩
  exact ⟨(eA.subgroupMap Q.normalizerMonoidHom.range).trans (MulEquiv.subgroupCongr he)⟩

/-- All four local action inputs transport on the literal subgroup embedding. -/
theorem Facts.map (Q : Subgroup K) (h : Facts Q) (f : K →* G) (hf : Function.Injective f) :
    2 < Nat.card (Q.map f) ∧
    IsCyclic (normalizerAction f.range (Q.map f)).range ∧
    Odd (Nat.card (normalizerAction f.range (Q.map f)).range) ∧
    (∀ a ∈ Q.map f, a ≠ 1 → ∀ b ∈ Q.map f, b ≠ 1 →
      ∃ n ∈ f.range ⊓ normalizer (Q.map f : Set G), n * a * n⁻¹ = b) := by
  obtain ⟨e⟩ := range_equiv_map Q f hf
  refine ⟨by simpa only [card_map_of_injective hf] using h.size,
    e.isCyclic.mp h.cyclic, ?_, ?_⟩
  · rw [← Nat.card_congr e.toEquiv]
    exact h.odd
  · rintro _ ⟨a, ha, rfl⟩ hane _ ⟨b, hb, rfl⟩ hbne
    obtain ⟨n, hn, he⟩ := h.transitive a ha (fun he => hane (he ▸ f.map_one))
      b hb (fun he => hbne (he ▸ f.map_one))
    refine ⟨f n, ⟨⟨n, rfl⟩, le_normalizer_map f ⟨n, hn, rfl⟩⟩, ?_⟩
    simpa only [map_mul, map_inv] using congrArg f he
end Theory.GroupTheory.SylowCenterAction
