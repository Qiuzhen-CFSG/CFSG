module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.Transport
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies.Divisibility
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies.HigmanSims.CoverBound

/-!
# Structural tests for the odd and sporadic residual rows

The normalizer quotient acts faithfully on the full component. Its component
image corresponds exactly to inner automorphisms, even for central covers.

For the residual comparison, primes other than two and three survive both
the covering kernel and the exceptional three-residual in Notation 16.5.5.
Thus different such prime divisors of the actual quotient fixed groups rule
out an isomorphism of the full modified residuals. When prime support agrees,
the order of the ordinary residual is bounded above by the center order times
the order of the model residual, and below by the latter order.

These are comparison tools for Aschbacher–Smith, combined manuscript of
1 March 2004, 16.5.6(4), printed p.1197, using 16.1.2 and 16.1.5 on
pp.1170–1172. They do not assert the family tables or their Sylow markings.
In particular the full quotient fixed group is never identified with the
image of the upstairs fixed group; only their two-residuals are compared.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.OtherRows
open Subgroup Theory.GroupTheory
open SylowSymmetry.ReverseDelta.Comparison
open SylowSymmetry.ReverseDelta.Comparison.OtherFamilies

variable {G : Type*} [Group G] {L : Subgroup G}

/-- The faithful action of N(L)/C(L) on the full component. -/
def actionHom (L : Subgroup G) : ActionQuotient L →* MulAut L :=
  QuotientGroup.lift _ L.normalizerMonoidHom (by rw [normalizerMonoidHom_ker])

theorem actionHom_injective : Function.Injective (actionHom L) :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr L.normalizerMonoidHom_ker.symm

/-- The specified actor has exactly its normalizer action. -/
theorem actionHom_actionMap (u : normalizer (L : Set G)) :
    actionHom L (actionMap (L := L) le_rfl u) = L.normalizerMonoidHom u := rfl

/-- The component action is conjugation by the specified component element. -/
theorem actionHom_component (k : L) :
    actionHom L (actionMap L.le_normalizer k) = MulAut.conj k := by
  ext x
  rfl

/-- Projection to N(L)/C(L) preserves the order of the induced automorphism. -/
theorem action_order (u : normalizer (L : Set G)) :
    orderOf (L.normalizerMonoidHom u) = orderOf (actionMap (L := L) le_rfl u) := by
  rw [← actionHom_actionMap]
  exact orderOf_injective (actionHom L) actionHom_injective _

/-- Being in L* means that the actual action is inner; the actor itself
need not lie in L. -/
theorem action_inner_iff (u : normalizer (L : Set G)) :
    (∃ k : L, L.normalizerMonoidHom u = MulAut.conj k) ↔
      actionMap (L := L) le_rfl u ∈ componentImage L := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, actionHom_injective ?_⟩
    rw [actionHom_component, actionHom_actionMap, hk]
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have he := (congrArg (actionHom L) hk).symm
    rwa [actionHom_component, actionHom_actionMap] at he

/-- An identification of the full upstairs fixed group identifies its
two-residual with the full ambient two-residual, without a central quotient. -/
noncomputable def fullFixedResidualEquiv {H : Type*} [Group H]
    (u : normalizer (L : Set G)) (e : (L.normalizerMonoidHom u).fixedSubgroup ≃* H) :
    involutionTwoResidual L u.val ≃* pResidual 2 H :=
  ((pResidual 2 (L ⊓ centralizer ({u.val} : Set G) : Subgroup G)).equivMapOfInjective
    _ (subtype_injective _)).symm.trans
    (((fixedCentralizerEquiv u.property).symm.trans e).subgroupMap _ |>.trans
      (MulEquiv.subgroupCongr
        (map_pResidual 2 ((fixedCentralizerEquiv u.property).symm.trans e))))

private theorem prime_dvd_residual_iff {H : Type*} [Group H] [Finite H]
    {p q : ℕ} [Fact p.Prime] (hq : q.Prime) (hqp : q ≠ p) :
    q ∣ Nat.card (pResidual p H) ↔ q ∣ Nat.card H := by
  constructor
  · exact fun h => h.trans (card_subgroup_dvd_card _)
  · intro h
    have hc := (pResidual p H).card_mul_index
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (isPGroup_quotient_pResidual (G := H) p)
    have hqn : ¬ q ∣ (pResidual p H).index := by
      rw [index_eq_card, hn]
      intro hd
      exact hqp ((Nat.dvd_prime (Fact.out : p.Prime)).mp
        (hq.dvd_of_dvd_pow hd) |>.resolve_left hq.ne_one)
    exact (hq.dvd_mul.mp (hc ▸ h)).resolve_right hqn

variable [Finite G]

/-- The exceptional modification preserves every prime divisor other than
three, without an unproved assertion that the model families are disjoint. -/
theorem prime_dvd_modified_iff_twoResidual {u : G} {q : ℕ}
    (hq : q.Prime) (hq3 : q ≠ 3) :
    q ∣ Nat.card (modifiedCentralizerResidual L u) ↔
      q ∣ Nat.card (involutionTwoResidual L u) := by
  classical
  unfold modifiedCentralizerResidual
  split_ifs
  · rw [card_map_of_injective (subtype_injective _)]
    exact prime_dvd_residual_iff hq hq3
  · rfl

/-- The genuine quotient-action fixed group detects odd prime divisors of
the upstairs two-residual. Covers are retained through the two-kernel. -/
theorem odd_prime_dvd_twoResidual_iff_fixed [IsQuasisimple L]
    (hodd : pPrimeCore 2 L = ⊥) {S : Type*} [Group S] [Finite S]
    (e : (L ⧸ center L) ≃* S) (u : normalizer (L : Set G))
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    q ∣ Nat.card (involutionTwoResidual L u.val) ↔
      q ∣ Nat.card (MulAut.centralQuotientAction e
        (L.normalizerMonoidHom u)).fixedSubgroup := by
  change q ∣ Nat.card (SylowSymmetry.ReverseDelta.residual L u.val) ↔ _
  rw [← odd_prime_dvd_centralImage_iff hodd
    ((SylowSymmetry.ReverseDelta.residual_le L u.val).trans inf_le_left) hq hq2,
    Nat.card_congr (centralImageModelEquiv hodd e u.property).toEquiv]
  exact odd_prime_dvd_residual_iff hq hq2

/-- This test is valid in both branches of Notation 16.5.5, on the actual
fixed group of the action on the specified central quotient model. -/
theorem prime_dvd_modified_iff_fixed [IsQuasisimple L]
    (hodd : pPrimeCore 2 L = ⊥) {S : Type*} [Group S] [Finite S]
    (e : (L ⧸ center L) ≃* S) (u : normalizer (L : Set G))
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3) :
    q ∣ Nat.card (modifiedCentralizerResidual L u.val) ↔
      q ∣ Nat.card (MulAut.centralQuotientAction e
        (L.normalizerMonoidHom u)).fixedSubgroup :=
  (prime_dvd_modified_iff_twoResidual hq hq3).trans
    (odd_prime_dvd_twoResidual_iff_fixed hodd e u hq hq2)

/-- A separating prime in the quotient fixed rows rules out an isomorphism
of the full modified residuals, including all their central kernels. -/
theorem no_equiv_of_fixed_prime [IsQuasisimple L]
    (hodd : pPrimeCore 2 L = ⊥) {S : Type*} [Group S] [Finite S]
    (e : (L ⧸ center L) ≃* S) (u v : normalizer (L : Set G))
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3)
    (hu : q ∣ Nat.card (MulAut.centralQuotientAction e
      (L.normalizerMonoidHom u)).fixedSubgroup)
    (hv : ¬ q ∣ Nat.card (MulAut.centralQuotientAction e
      (L.normalizerMonoidHom v)).fixedSubgroup) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃*
      modifiedCentralizerResidual L v.val) := by
  rintro ⟨f⟩
  have hd := (prime_dvd_modified_iff_fixed hodd e u hq hq2 hq3).mpr hu
  rw [Nat.card_congr f.toEquiv] at hd
  exact hv ((prime_dvd_modified_iff_fixed hodd e v hq hq2 hq3).mp hd)

/-- The order of the full residual is the model residual order times the
order of its own central kernel, which divides the component center order. -/
theorem twoResidual_card_factor [IsQuasisimple L]
    (hodd : pPrimeCore 2 L = ⊥) {S : Type*} [Group S]
    (e : (L ⧸ center L) ≃* S) (u : normalizer (L : Set G)) :
    ∃ k : ℕ, 0 < k ∧ k ∣ Nat.card (center L) ∧
      Nat.card (involutionTwoResidual L u.val) = k *
        Nat.card (pResidual 2 (MulAut.centralQuotientAction e
          (L.normalizerMonoidHom u)).fixedSubgroup) := by
  let hXL := (SylowSymmetry.ReverseDelta.residual_le L u.val).trans inf_le_left
  let f := centralImageMap hXL
  refine ⟨Nat.card f.ker, Nat.card_pos, centralImageMap_kernel_card_dvd_center hXL, ?_⟩
  change Nat.card (SylowSymmetry.ReverseDelta.residual L u.val) = _
  rw [← Nat.card_congr (centralImageModelEquiv hodd e u.property).toEquiv,
    ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f
      (centralImageMap_surjective hXL)).toEquiv]
  exact f.ker.card_mul_index.symm

/-- Size bounds preserve the possible cover rather than silently discarding it. -/
theorem twoResidual_card_bounds [IsQuasisimple L]
    (hodd : pPrimeCore 2 L = ⊥) {S : Type*} [Group S]
    (e : (L ⧸ center L) ≃* S) (u : normalizer (L : Set G)) :
    let n := Nat.card (pResidual 2 (MulAut.centralQuotientAction e
      (L.normalizerMonoidHom u)).fixedSubgroup)
    n ≤ Nat.card (involutionTwoResidual L u.val) ∧
      Nat.card (involutionTwoResidual L u.val) ≤ Nat.card (center L) * n := by
  obtain ⟨k, hk, hkd, he⟩ := twoResidual_card_factor hodd e u
  dsimp only
  rw [he]
  constructor
  · exact Nat.le_mul_of_pos_left _ hk
  · exact Nat.mul_le_mul_right _ (Nat.le_of_dvd Nat.card_pos hkd)

/-- For a perfect central row the modification has no effect. A size gap
larger than the entire covering kernel then separates it from the other row,
whose modification can only decrease its order. -/
theorem no_equiv_of_perfect_size_gap [IsQuasisimple L]
    (hodd : pPrimeCore 2 L = ⊥) {S : Type*} [Group S]
    (e : (L ⧸ center L) ≃* S) (u v : normalizer (L : Set G))
    [Group.IsPerfect (involutionTwoResidual L u.val)]
    (hgap : Nat.card (center L) * Nat.card (pResidual 2
      (MulAut.centralQuotientAction e (L.normalizerMonoidHom v)).fixedSubgroup) <
        Nat.card (pResidual 2
          (MulAut.centralQuotientAction e (L.normalizerMonoidHom u)).fixedSubgroup)) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃*
      modifiedCentralizerResidual L v.val) := by
  rintro ⟨f⟩
  have hsmall := (Nat.le_of_dvd Nat.card_pos
    (card_dvd_of_le (modifiedCentralizerResidual_le L v.val))).trans
    (twoResidual_card_bounds hodd e v).2
  have hlarge := (twoResidual_card_bounds hodd e u).1
  have he : Nat.card (involutionTwoResidual L u.val) =
      Nat.card (modifiedCentralizerResidual L v.val) := by
    rw [← modifiedResidual_eq_of_perfect u.val]
    exact Nat.card_congr f.toEquiv
  rw [he] at hlarge
  exact (not_lt_of_ge (hlarge.trans hsmall)) hgap

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.OtherRows
