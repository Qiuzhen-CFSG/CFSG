module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.Contracts

/-!
# Saturation seeds from the odd-prime Theorem 2

Choose a p-subgroup of M maximal subject to fixing at least two points.
Theorem 2 rules out exactly two fixed points and supplies a distinguished
normalizing involution fixing the base point. Maximality makes the subgroup
Sylow in each pair stabilizer through the base, so Section 3 computes its
inverted cardinality. Conjugation inside M takes this involution to the
specified z, preserving both the prime and the number of fixed points.

This proves the seed construction conditionally on `ActionTheoremTwo`.
It does not establish Theorem 2 or invoke ambient strong embedding.

Source: GLS, Volume 4, Chapter 2, Corollary 5.7 and the conjugation in (6B),
printed pp. 41--43; `refs/KGroup/GLS4/Chapter2.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
/-- Conjugation inside M preserves the centralizer-index prime share. -/
public theorem sectionFive_primeShare_conjugate_in (s : G) (g : M) (p : ℕ) :
    theorem4bPrimeShare M (MulAut.conj (g : G) s) p =
      theorem4bPrimeShare M s p := by
  let C : G → Subgroup M := fun t =>
    (M ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf M
  let e : M ≃* M := MulAut.conj g
  have hmap : (C s).map e.toMonoidHom = C (MulAut.conj (g : G) s) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyc := Subgroup.mem_centralizer_singleton_iff.mp hy.2
      refine ⟨(e y).property, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      change (g : G) * (y : G) * (g : G)⁻¹ *
          ((g : G) * s * (g : G)⁻¹) =
        ((g : G) * s * (g : G)⁻¹) * ((g : G) * (y : G) * (g : G)⁻¹)
      simpa only [map_mul, MulAut.conj_apply, Subgroup.coe_subtype] using congrArg (MulAut.conj (g : G)) hyc
    · intro hx
      refine Subgroup.mem_map.mpr ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      refine ⟨(e.symm x).property, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hxc := Subgroup.mem_centralizer_singleton_iff.mp hx.2
      have hc := congrArg (MulAut.conj (g : G)⁻¹) hxc
      simpa [e, MulAut.conj_apply, mul_assoc] using hc
  have hi := Subgroup.index_map_equiv (C s) e
  change ((C s).map e.toMonoidHom).index = (C s).index at hi
  rw [hmap] at hi
  exact congrArg (fun n : ℕ => p ^ n.factorization p) hi

/-- Conjugation transports the actual fixed-point sets of the coset action. -/
public theorem sectionFive_fixedPoints_card_conj (P : Subgroup G) (g : G) :
    Nat.card (theorem4bFixedPoints M (P.conjBy g)) =
      Nat.card (theorem4bFixedPoints M P) := by
  have hf (Q : Subgroup G) (a : G) :
      Nat.card (theorem4bFixedPoints M Q) ≤
        Nat.card (theorem4bFixedPoints M (Q.conjBy a)) := by
    let f : theorem4bFixedPoints M Q → theorem4bFixedPoints M (Q.conjBy a) :=
      fun b => ⟨a • b.1, by
        intro x hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
        change (a * y * a⁻¹) • (a • b.1) = a • b.1
        simpa [mul_smul] using congrArg (fun c : G ⧸ M => a • c) (b.2 y hy)⟩
    apply Nat.card_le_card_of_injective f
    intro b c hbc
    apply Subtype.ext
    exact MulAction.injective a (congrArg Subtype.val hbc)
  apply le_antisymm
  · simpa only [Subgroup.conjBy_inv] using hf (P.conjBy g) g⁻¹
  · exact hf P g

/-- In the absence of an exactly-two-fixed-points p-subgroup, a maximal
subgroup with three fixed points is Sylow in every pair stabilizer it fixes. -/
public theorem sectionFive_maximal_base_pair_sylow {p : ℕ} (hp : p.Prime)
    (hno : ¬ ∃ P : Subgroup G,
      IsPGroup p P ∧ Nat.card (theorem4bFixedPoints M P) = 2)
    {P : Subgroup G} (hPp : IsPGroup p P) (hPM : P ≤ M)
    (hmax : ∀ Q : Subgroup G, IsPGroup p Q → Q ≤ M →
      3 ≤ Nat.card (theorem4bFixedPoints M Q) → P ≤ Q → Q = P)
    {beta : G ⧸ M} (hb : beta ≠ QuotientGroup.mk 1)
    (hPb : P ≤ MulAction.stabilizer G beta) :
    theorem4bIsSylowSubgroupOf p P (M ⊓ MulAction.stabilizer G beta) := by
  let : Fact p.Prime := ⟨hp⟩
  let D := M ⊓ MulAction.stabilizer G beta
  have hPD : P ≤ D := le_inf hPM hPb
  have hPDp : IsPGroup p (P.subgroupOf D) :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPD).symm
  obtain ⟨S, hPS⟩ := hPDp.exists_le_sylow
  let Q : Subgroup G := (S : Subgroup D).map D.subtype
  have hPQ : P ≤ Q := by
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hPD hx⟩, hPS hx, rfl⟩
  have hQD : Q ≤ D := by
    simpa [Q] using Subgroup.map_le_range D.subtype (S : Subgroup D)
  have hQp : IsPGroup p Q := S.isPGroup'.map D.subtype
  have htwo := action_two_le_fixedPoints (hQD.trans inf_le_left)
    (hQD.trans inf_le_right) hb
  have hne : Nat.card (theorem4bFixedPoints M Q) ≠ 2 :=
    fun heq => hno ⟨Q, hQp, heq⟩
  have hQP := hmax Q hQp (hQD.trans inf_le_left) (by omega) hPQ
  exact ⟨S, hQP.symm⟩

/-- Corollary 5.7's seeds follow from the odd-prime Theorem 2 and Section 3.
The conjugation takes place inside M and preserves the specified prime and z. -/
public theorem actionSaturationSeeds_of_theoremTwo
    (h : IsProductDisconnected Z M)
    (hclass : ∀ x ∈ Z, ∀ z ∈ Z, IsConj x z)
    (h3 : ActionSectionThree Z M) (h2 : ActionTheoremTwo Z M) :
    ActionSaturationSeeds Z M := by
  classical
  intro z hzZ hzM p hp hpOdd hnot
  have hno : ¬ ∃ P : Subgroup G,
      IsPGroup p P ∧ Nat.card (theorem4bFixedPoints M P) = 2 :=
    fun hex => hnot ((h2 p hp hpOdd).1 hex)
  obtain ⟨t, _htZ, htM⟩ := exists_not_mem h
  let beta0 : G ⧸ M := QuotientGroup.mk t
  have hb0 : beta0 ≠ QuotientGroup.mk 1 := by
    intro heq
    apply htM
    simpa [beta0] using M.inv_mem (QuotientGroup.eq.mp heq)
  have hbot : 2 ≤ Nat.card (theorem4bFixedPoints M (⊥ : Subgroup G)) :=
    action_two_le_fixedPoints bot_le bot_le hb0
  let Good : Subgroup G → Prop := fun R =>
    IsPGroup p R ∧ R ≤ M ∧ 2 ≤ Nat.card (theorem4bFixedPoints M R)
  have hgood : Good ⊥ := ⟨IsPGroup.of_bot, bot_le, hbot⟩
  obtain ⟨R, _, hRmax⟩ := Finite.exists_le_maximal hgood
  have hRp : IsPGroup p R := hRmax.1.1
  have hRM : R ≤ M := hRmax.1.2.1
  have hR3 : 3 ≤ Nat.card (theorem4bFixedPoints M R) := by
    have hlo := hRmax.1.2.2
    have hne : Nat.card (theorem4bFixedPoints M R) ≠ 2 :=
      fun heq => hno ⟨R, hRp, heq⟩
    omega
  have hmax : ∀ Q : Subgroup G, IsPGroup p Q → Q ≤ M →
      3 ≤ Nat.card (theorem4bFixedPoints M Q) → R ≤ Q → Q = R := by
    intro Q hQp hQM hQ3 hRQ
    exact (hRmax.eq_of_le ⟨hQp, hQM, by omega⟩ hRQ).symm
  have hRbase : R ≤ MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M) := by
    simpa only [baseCoset_stabilizer] using hRM
  have hmaxBase : ∀ Q : Subgroup G, IsPGroup p Q →
      Q ≤ MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M) →
      3 ≤ Nat.card (theorem4bFixedPoints M Q) → R ≤ Q → Q = R := by
    simpa only [baseCoset_stabilizer] using hmax
  obtain ⟨s, hsZ, hsN, hsFix⟩ := ((h2 p hp hpOdd).2 hno
    (QuotientGroup.mk 1) R hRp hRbase hR3 hmaxBase).2
    (QuotientGroup.mk 1) (theorem4b_baseCoset_mem_fixedPoints hRM)
  have hsM : s ∈ M := by
    simpa only [baseCoset_stabilizer] using MulAction.mem_stabilizer_iff.mpr hsFix
  let base : theorem4bFixedPoints M R :=
    ⟨QuotientGroup.mk 1, theorem4b_baseCoset_mem_fixedPoints hRM⟩
  have hntr : Nontrivial (theorem4bFixedPoints M R) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let := hntr
  obtain ⟨b, hb⟩ := exists_ne base
  have hbne : b.1 ≠ QuotientGroup.mk 1 := fun heq => hb (Subtype.ext heq)
  have hRb : R ≤ MulAction.stabilizer G b.1 := by
    intro x hx
    exact MulAction.mem_stabilizer_iff.mpr (b.2 x hx)
  have hRsyl := sectionFive_maximal_base_pair_sylow hp hno hRp hRM hmax hbne hRb
  have hRcard := (h3.base_bound s hsZ hsM p hp hpOdd b.1 hbne R hRp
    (le_inf hRM hRb) hsN).2 hRsyl
  obtain ⟨g, hsg⟩ := isConj_iff.mp (hclass s hsZ z hzZ)
  have hgM : g ∈ M := (h.conjugate_mem_iff s hsZ hsM g).mp (by
    simpa only [MulAut.conj_apply, hsg] using hzM)
  let P : Subgroup G := R.conjBy g
  have hPp : IsPGroup p P := hRp.map (MulAut.conj g).toMonoidHom
  have hPM : P ≤ M := by
    rintro x ⟨y, hy, rfl⟩
    exact M.mul_mem (M.mul_mem hgM (hRM hy)) (M.inv_mem hgM)
  have hzN : z ∈ Subgroup.normalizer (P : Set G) := by
    apply Subgroup.le_normalizer_map (H := R) (MulAut.conj g).toMonoidHom
    exact Subgroup.mem_map.mpr ⟨s, hsN, hsg⟩
  have hP3 : 3 ≤ Nat.card (theorem4bFixedPoints M P) := by
    rw [show P = R.conjBy g from rfl, sectionFive_fixedPoints_card_conj]
    exact hR3
  refine ⟨P, hPp, hPM, hzN, hP3, ?_⟩
  have hcard := theorem4bInvertedCard_conjBy s g⁻¹ R
  have hconj : rightConjugateElem s g⁻¹ = z := by
    simpa only [rightConjugateElem, inv_inv] using hsg
  have hshare := sectionFive_primeShare_conjugate_in (M := M) s ⟨g, hgM⟩ p
  have hzconj : MulAut.conj g s = z := hsg
  rw [hzconj] at hshare
  simpa only [hconj, inv_inv, ← hshare, P] using hcard.trans hRcard

end BenderSuzuki.ZD
