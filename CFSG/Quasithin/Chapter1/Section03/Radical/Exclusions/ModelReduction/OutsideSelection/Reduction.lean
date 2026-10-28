module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.SieveContract
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# Noncontainment of the selected pushing-up component

A solvable subgroup normalized by K has central image in K/O₂(K) when
that quotient is quasisimple. For the two surviving 1.3.4 alternatives,
the center is trivial or has order dividing three. Thus its intersection
with an odd p-subgroup is trivial for p > 3. The required intersection
P ∩ K has order p in the swapped case and is all of P in the invariant
case. This proves K ≰ M for the actual component candidate.

The resulting construction supplies every C.2.7 input from an overgroup
outside M. The initial choice H₀ = K₀T still requires proving H₀ ≰ M;
that assertion is not supplied by the normal alternative of 1.3.4.
The separate normality criterion below reduces it to cyclicity of the
p-core of H₀/O₂(H₀), if that structural fact is established.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Proposition 1.3.8, printed pp.513–514, and Proposition 1.3.4, pp.509–510.
The SL₃ center count and elementary-matrix perfectness are reused from
the attributed ATLAS ports; see their source modules and LICENSES/ATLAS.txt.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
open XiEmbedding

private theorem solvable_normal_le_center {Q : Type*} [Group Q]
    [IsQuasisimple Q] (B : Subgroup Q) [B.Normal] [Group.IsSolvable B] :
    B ≤ center Q := by
  rcases IsQuasisimple.normal_le_center_or_eq_top B with hc | ht
  · exact hc
  · let _ : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
    let _ : Nontrivial Q := (QuotientGroup.mk'_surjective (center Q)).nontrivial
    have hs : Group.IsSolvable Q := Group.isSolvable_of_surjective
      (f := B.subtype) (by rw [ht]; exact topEquiv.surjective)
    exact (Group.IsPerfect.not_isSolvable Q hs).elim

private theorem intersection_eq_bot {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {X P K : Subgroup G}
    [Group.IsSolvable X] (hPK : P ≤ X) (hpP : IsPGroup p P) (hp : Odd p)
    (hq : IsQuasisimple (XiQuotient K))
    (hcenter : ¬ p ∣ Nat.card (center (XiQuotient K)))
    (hKX : K ≤ normalizer X) : P ⊓ K = ⊥ := by
  let q := QuotientGroup.mk' (pCore 2 K)
  let B := X.subgroupOf K
  let A := (P ⊓ K).subgroupOf K
  let _ := hq
  let _ : B.Normal := normal_subgroupOf_of_le_normalizer hKX
  let f : B →* X :=
    { toFun := fun b => ⟨b.val.val, b.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let _ : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
    (f := f) (by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : X => (x : G)) hab)
  let _ : Group.IsSolvable (B.map q) :=
    Group.isSolvable_of_surjective (q.subgroupMap_surjective B)
  have hb : B.map q ≤ center (XiQuotient K) := solvable_normal_le_center (B.map q)
  have ha : A.map q ≤ center (XiQuotient K) := (map_mono (f := q)
    (comap_mono (inf_le_left.trans hPK))).trans hb
  have hpA : IsPGroup p A := (hpP.to_le inf_le_left).comap_subtype
  have hzero : A.map q = ⊥ := by
    rcases (hpA.map q).card_eq_or_dvd with hc | hd
    · exact Subgroup.card_eq_one.mp hc
    · exact (hcenter (hd.trans (card_dvd_of_le ha))).elim
  have hcore : A ≤ pCore 2 K := by
    simpa only [Subgroup.map_eq_bot_iff, q, QuotientGroup.ker_mk'] using hzero
  have hdis : Disjoint A (pCore 2 K) := hpA.disjoint_of_coprime pCore_isPGroup
    (Nat.coprime_two_right.mpr hp)
  have hA : A = ⊥ := le_bot_iff.mp (fun a ha => hdis.le_bot ⟨ha, hcore ha⟩)
  simpa only [A, map_subgroupOf_eq_of_le inf_le_right, Subgroup.map_bot] using
    congrArg (map K.subtype) hA

private theorem simple_center_bot {Q : Type*} [Group Q] [IsSimpleGroup Q]
    [Group.IsPerfect Q] : center Q = ⊥ := by
  rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative Q (center_eq_top_iff.mp h)).elim

private theorem linear_center {Q : Type*} [Group Q] {p : ℕ}
    (h : LinearThreeModel p Q) : Nat.card (center Q) ∣ 3 := by
  rcases h with ⟨F, _, _, _, ⟨e⟩⟩ | ⟨F, _, _, _, ⟨e⟩⟩
  · rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact Matrix.SL3.card_center_dvd_three F
  · rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    let _ := Atlas.sl_perfect (F := F) 3 (by decide)
    have hz : center PSL(3, F) = ⊥ :=
      Group.IsPerfect.center_quotient_center_eq_bot SL(3, F)
    rw [hz, Subgroup.card_bot]
    exact one_dvd _

/-- The selected component lies outside M. Normalization of X would make
its solvable intersection with K central modulo O₂(K), contradicting the
nontrivial odd intersection in either surviving embedding alternative. -/
theorem ComponentCandidate.not_le_of_configuration {G : Type*} [Group G] [Finite G]
    {κ : GroupClass} {p : ℕ} {T X P L M H K : Subgroup G}
    (h : Configuration p T X P L M) (c : ComponentCandidate κ p T X P M H K) :
    ¬ K ≤ M := by
  intro hKM
  let _ : Fact p.Prime := ⟨h.prime⟩
  let _ := c.quasisimple
  let _ := h.xi.isSolvable
  have hc : ¬ p ∣ Nat.card (center (XiQuotient K)) := by
    rcases c.alternatives.2 with ⟨_, hm⟩ | ⟨_, hm⟩
    · let _ := swappedModel_simple c.quasisimple hm
      rw [simple_center_bot, Subgroup.card_bot]
      exact h.prime.not_dvd_one
    · intro hd
      have hp := Nat.le_of_dvd (by decide : 0 < 3) (hd.trans (linear_center hm))
      have := h.large
      omega
  have hi : P ⊓ K = ⊥ := intersection_eq_bot c.local_input.complement_le
    c.local_input.odd_complement.isPGroup h.odd c.quasisimple hc
      (hKM.trans h.normalizer_radical.le)
  rcases c.alternatives.2 with ⟨hs, _⟩ | ⟨ht, _⟩
  · have hp := swapped_intersection_card c.alternatives.1 hs
    rw [hi, Subgroup.card_bot] at hp
    have := h.large
    omega
  · have hXK : X ≤ K := c.containment.trans
      (iSup_conjugates_le_of_le_normalizer K T K le_rfl ht)
    have hP : P = ⊥ := (inf_eq_left.mpr (c.local_input.complement_le.trans hXK)).symm.trans hi
    have hp : Nat.card P = p ^ 2 :=
      (Nat.card_congr c.alternatives.1.some.toEquiv).trans (plane_card p)
    rw [hP, Subgroup.card_bot] at hp
    have := h.large
    nlinarith

/-- A noncyclic odd quotient prevents relative normality when the overgroup's
corresponding prime core modulo O₂ is cyclic. This supplies an algebraic
route for the initial reduction; cyclicity remains a separate obligation. -/
theorem not_normal_of_cyclic_quotient_pCore {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {X H : Subgroup G}
    (hq : XiOddQuotient p (XiQuotient X)) (hXH : X ≤ H)
    (hcyc : IsCyclic (pCore p (XiQuotient H))) : ¬ (X.subgroupOf H).Normal := by
  intro hn
  let B := X.subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  let _ := hn
  let _ := hcyc
  let e := subgroupOfEquivOfLe hXH
  let eqv := QuotientGroup.congr (pCore 2 B) (pCore 2 X) e (pCore_map_iso 2 e)
  have hk : (q.subgroupMap B).ker = pCore 2 B := by
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2 hn.isSubnormal).symm
  let eqi : XiQuotient X ≃* B.map q := eqv.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (q.subgroupMap B)
        (q.subgroupMap_surjective B)))
  have hi : IsPGroup p (B.map q) := hq.isPGroup.of_equiv eqi
  have hle : B.map q ≤ pCore p (XiQuotient H) := le_sSup ⟨inferInstance, hi⟩
  let _ : IsCyclic (B.map q) := isCyclic_of_injective (inclusion hle) (inclusion_injective hle)
  exact hq.not_isCyclic (isCyclic_of_injective eqi.toMonoidHom eqi.injective)


/-- Once the overgroup lies outside M, its candidate satisfies both remaining
C.2.7 hypotheses. The source-theorem assembly must still construct that
initial overgroup and prove its noncontainment. -/
theorem Configuration.exists_pushingUpComponent_of_outside
    {G : Type*} [Group G] [Finite G]
    {κ : GroupClass} (hG : IsSimpleQTKE κ G) (T : Sylow 2 G)
    {p : ℕ} {X P L₀ M H₀ : Subgroup G}
    (h : Configuration p T X P L₀ M) (h134 : Source134 κ G)
    (h114 : HOver G (T : Set G) ⊆ He G)
    (hH : H₀ ∈ HOver G (T : Set G))
    (hXH : X ⊔ (T : Subgroup G) ≤ H₀) (hout : ¬ H₀ ≤ M) :
    ∃ K, PushingUpComponent κ p T X P M H₀ K := by
  obtain ⟨K, hc⟩ := Configuration.exists_componentCandidate
    hG T h h134 h114 hH hXH hout
  exact ⟨K, hc.toPushingUpComponent (ComponentCandidate.not_le_of_configuration h hc)⟩

end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
