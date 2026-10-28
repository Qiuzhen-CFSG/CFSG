module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Setup
public import BenderSuzuki.SE.Theorem4

/-!
# Distinguished counterexamples to the action theorem

An odd subgroup acted on nontrivially by a distinguished involution contains
a cyclic subgroup of odd prime order inverted by that same involution. Thus
failure of the odd-normalizer clause produces the source configuration (6A).
The finite maximal choice (6D) is made with the prime and involution fixed.

Only elementary lemmas of `SE.Theorem4` are used here; no ambient strong
embedding is assumed. The counting boundary at the end records outstanding
source obligations, not established theorems.

Source: GLS, Volume 4, Chapter 2, Proposition 3.8 and (6A)--(6D).
-/

noncomputable section

namespace BenderSuzuki.ZD

open Theory.GroupTheory PFAppendixIII PFchapter1section1

universe u

variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
/-- Unique conjugate membership gives the base-point instance of Lemma
3.1(h), directly on the actual coset action. -/
public theorem action_fixedPoint_eq_base (h : IsProductDisconnected Z M)
    {z : G} (hzZ : z ∈ Z) (hzM : z ∈ M) {beta : G ⧸ M}
    (hfix : z • beta = beta) : beta = QuotientGroup.mk 1 := by
  induction beta using Quotient.inductionOn with
  | h g =>
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq] at hfix
    have hconj : MulAut.conj g⁻¹ z ∈ M := by
      simpa [MulAut.conj_apply, smul_eq_mul, mul_assoc] using M.inv_mem hfix
    have hginv : g⁻¹ ∈ M := (h.conjugate_mem_iff z hzZ hzM g⁻¹).mp hconj
    exact QuotientGroup.eq.mpr (by simpa using hginv)

/-- The configuration (6A), retaining the distinguished involution. -/
public structure ActionCounterexample (Z : Set G) (M : Subgroup G)
    extends Theorem4bSixA M where
  hzZ : z ∈ Z

/-- The source maximality (6D) fixes both `p` and `z`. -/
public structure ActionMaximalCounterexample (Z : Set G) (M : Subgroup G) where
  data : ActionCounterexample Z M
  maximal : ∀ e : ActionCounterexample Z M,
    e.p = data.p → e.z = data.z →
      theorem4bInvertedCard e.z e.W ≤ theorem4bInvertedCard data.z data.W

/-- A concrete second fixed point gives the cardinal bound in (6A). -/
public theorem action_two_le_fixedPoints {W : Subgroup G}
    (hWM : W ≤ M) {beta : G ⧸ M}
    (hbeta : W ≤ MulAction.stabilizer G beta)
    (hne : beta ≠ QuotientGroup.mk 1) :
    2 ≤ Nat.card (theorem4bFixedPoints M W) := by
  let a : theorem4bFixedPoints M W :=
    ⟨QuotientGroup.mk 1, theorem4b_baseCoset_mem_fixedPoints hWM⟩
  let b : theorem4bFixedPoints M W :=
    ⟨beta, fun w hw => MulAction.mem_stabilizer_iff.mp (hbeta hw)⟩
  let f : Bool → theorem4bFixedPoints M W := fun t => cond t b a
  have hf : Function.Injective f := by
    intro s t hst
    cases s <;> cases t
    · rfl
    · exact False.elim (hne (by simpa [f, a, b] using (congrArg Subtype.val hst).symm))
    · exact False.elim (hne (by simpa [f, a, b] using congrArg Subtype.val hst))
    · rfl
  simpa using Nat.card_le_card_of_injective f hf

/-- Reduction of an arbitrary odd counterexample to (6A), with the same
distinguished involution and a subgroup of the original odd subgroup. -/
public theorem actionCounterexample_of_odd_subgroup
    (h : IsProductDisconnected Z M) {z : G} (hzZ : z ∈ Z) (hzM : z ∈ M)
    {W : Subgroup G} (hWodd : Odd (Nat.card W)) (hWM : W ≤ M)
    (hzNorm : z ∈ Subgroup.normalizer (W : Set G))
    (hnot : ¬ W ≤ Subgroup.centralizer ({z} : Set G))
    {beta : G ⧸ M} (hbeta : W ≤ MulAction.stabilizer G beta)
    (hne : beta ≠ QuotientGroup.mk 1) :
    ∃ d : ActionCounterexample Z M, d.z = z ∧ d.W ≤ W := by
  let c : Theorem4bCounterexample M :=
    ⟨z, W, h.involutions z hzZ, hzM, hWodd, hWM, hzNorm, hnot,
      action_two_le_fixedPoints hWM hbeta hne⟩
  obtain ⟨x, hxW, hxne, hzx⟩ := c.exists_inverted
  obtain ⟨p, y, hp, hyorder, hyW, hyne, hzy⟩ :=
    exists_prime_order_inverted_of_mem_odd_subgroup hxW hxne hzx hWodd
  have hyodd : Odd (orderOf y) := hWodd.of_dvd_nat (by
    simpa using orderOf_dvd_natCard (⟨y, hyW⟩ : W))
  have hpOdd : Odd p := hyorder ▸ hyodd
  let P := Subgroup.zpowers y
  have hPW : P ≤ W := Subgroup.zpowers_le.mpr hyW
  have hPp : IsPGroup p P := by
    apply IsPGroup.of_card (n := 1)
    simpa [P, Nat.card_zpowers] using hyorder
  have hPne : P ≠ ⊥ := by
    intro hbot
    have hyP : y ∈ P := Subgroup.mem_zpowers y
    rw [hbot] at hyP
    exact hyne hyP
  let d : ActionCounterexample Z M :=
    { p := p
      hp := hp
      hpOdd := hpOdd
      z := z
      W := P
      hz := h.involutions z hzZ
      hzM := hzM
      hWp := hPp
      hWM := hPW.trans hWM
      hzNorm := theorem4b_mem_normalizer_zpowers_of_inverts (h.involutions z hzZ) hzy
      hcomm := commutator_zpowers_eq_of_inverts_prime (h.involutions z hzZ)
        hyne hzy (hyorder.symm ▸ hp) hyodd
      hWne := hPne
      hfixed := action_two_le_fixedPoints (hPW.trans hWM) (hPW.trans hbeta) hne
      hzZ := hzZ }
  exact ⟨d, rfl, hPW⟩

/-- Finite maximization of the inverted set, within the fixed-prime,
fixed-involution family specified by the source. -/
public theorem exists_actionMaximalCounterexample
    (d : ActionCounterexample Z M) :
    ∃ e : ActionMaximalCounterexample Z M, e.data.p = d.p ∧ e.data.z = d.z := by
  classical
  let F := {e : ActionCounterexample Z M // e.p = d.p ∧ e.z = d.z}
  let score : F → ℕ := fun e => theorem4bInvertedCard e.1.z e.1.W
  let deficit : F → ℕ := fun e => Nat.card G - score e
  have hnonempty : ∃ n, ∃ e : F, n = deficit e :=
    ⟨deficit ⟨d, rfl, rfl⟩, ⟨d, rfl, rfl⟩, rfl⟩
  obtain ⟨e, he⟩ := Nat.find_spec hnonempty
  have hmax : ∀ f : F, score f ≤ score e := by
    intro f
    have hmin := Nat.find_min' hnonempty ⟨f, rfl⟩
    have hbound : ∀ q : F, score q ≤ Nat.card G := by
      intro q
      exact Nat.card_le_card_of_injective
        (fun x : {x : G // x ∈ q.1.W ∧ q.1.z * x * q.1.z⁻¹ = x⁻¹} => x.1)
        Subtype.val_injective
    have hf := hbound f
    have he' := hbound e
    rw [he] at hmin
    dsimp only [deficit] at hmin
    omega
  refine ⟨⟨e.1, ?_⟩, e.2.1, e.2.2⟩
  intro f hfp hfz
  exact hmax ⟨f, hfp.trans e.2.1, hfz.trans e.2.2⟩

/-- Source Theorem 2, restricted to odd primes and distinguished involutions.
Unlike the older SE interface, this does not quantify over the prime two. -/
@[expose] public def ActionTheoremTwo (Z : Set G) (M : Subgroup G) : Prop :=
  ∀ p : ℕ, p.Prime → Odd p →
    (((∃ P : Subgroup G, IsPGroup p P ∧ Nat.card (theorem4bFixedPoints M P) = 2) →
        MulAction.IsMultiplyPretransitive G (G ⧸ M) 2) ∧
      ((¬ ∃ P : Subgroup G, IsPGroup p P ∧ Nat.card (theorem4bFixedPoints M P) = 2) →
        ∀ (beta : G ⧸ M) (P : Subgroup G), IsPGroup p P →
          P ≤ MulAction.stabilizer G beta →
          3 ≤ Nat.card (theorem4bFixedPoints M P) →
          (∀ Q : Subgroup G, IsPGroup p Q → Q ≤ MulAction.stabilizer G beta →
            3 ≤ Nat.card (theorem4bFixedPoints M Q) → P ≤ Q → Q = P) →
          (∀ gamma delta : G ⧸ M,
            gamma ∈ fixedPointsOfSubgroup G (G ⧸ M) P →
            delta ∈ fixedPointsOfSubgroup G (G ⧸ M) P →
            ∃ n : Subgroup.normalizer (P : Set G), (n : G) • gamma = delta) ∧
          ∀ gamma : G ⧸ M, gamma ∈ fixedPointsOfSubgroup G (G ⧸ M) P →
            ∃ s ∈ Z, s ∈ Subgroup.normalizer (P : Set G) ∧ s • gamma = gamma))

/-- The counting inputs for (6B). These are explicit remaining obligations
from Proposition 3.8 and Sections 5--6, not an assumption of Theorem 4.
All involutions here are distinguished members of `Z`. -/
public structure ActionCounting (Z : Set G) (M : Subgroup G) : Prop where
  theorem_two : ActionTheoremTwo Z M
  prime_share : ∃ z ∈ Z, z ∈ M ∧ ∃ p : ℕ,
    p.Prime ∧ Odd p ∧ 2 ≤ theorem4bPrimeShare M z p
  bound : ∀ d : ActionCounterexample Z M,
    theorem4bInvertedCard d.z d.W ≤ theorem4bPrimeShare M d.z d.p
  saturated : ∀ z ∈ Z, z ∈ M → ∀ p : ℕ, p.Prime → Odd p →
    2 ≤ theorem4bPrimeShare M z p →
    ¬ MulAction.IsMultiplyPretransitive G (G ⧸ M) 2 →
    ∃ d : ActionCounterexample Z M, d.z = z ∧ d.p = p ∧
      theorem4bInvertedCard d.z d.W = theorem4bPrimeShare M z p
  invariant_sylow : ∀ z ∈ Z, z ∈ M → ∀ p : ℕ, p.Prime → Odd p →
    ∀ beta : G ⧸ M, beta ≠ QuotientGroup.mk 1 →
      ((∃ Q : Subgroup G,
          theorem4bIsSylowSubgroupOf p Q (M ⊓ MulAction.stabilizer G beta) ∧
          z ∈ Subgroup.normalizer (Q : Set G)) ↔
        ∃ P : Subgroup G, IsPGroup p P ∧ P ≤ M ⊓ MulAction.stabilizer G beta ∧
          z ∈ Subgroup.normalizer (P : Set G) ∧
          theorem4bInvertedCard z P = theorem4bPrimeShare M z p)

/-- In the non-two-transitive branch, the maximal inverted set attains the
source `p`-share. This compares only witnesses with the same `p` and `z`. -/
public theorem ActionMaximalCounterexample.card_eq_primeShare
    (d : ActionMaximalCounterexample Z M) (hc : ActionCounting Z M)
    (hnot : ¬ MulAction.IsMultiplyPretransitive G (G ⧸ M) 2) :
    theorem4bInvertedCard d.data.z d.data.W =
      theorem4bPrimeShare M d.data.z d.data.p := by
  have htwo : 2 ≤ theorem4bInvertedCard d.data.z d.data.W :=
    by
      have hset : d.data.toTheorem4bSixA.invertedSet =
          {x : G | x ∈ d.data.W ∧ d.data.z * x * d.data.z⁻¹ = x⁻¹} :=
        Set.ext (fun x => d.data.toTheorem4bSixA.mem_invertedSet_iff x)
      have h := d.data.toTheorem4bSixA.two_le_card_invertedSet
      rw [hset] at h
      exact h
  obtain ⟨e, hez, hep, hecard⟩ := hc.saturated d.data.z d.data.hzZ d.data.hzM
    d.data.p d.data.hp d.data.hpOdd (htwo.trans (hc.bound d.data)) hnot
  exact le_antisymm (hc.bound d.data) (hecard ▸ d.maximal e hep hez)

end BenderSuzuki.ZD
