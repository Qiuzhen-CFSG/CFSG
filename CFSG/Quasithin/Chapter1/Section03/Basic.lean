module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import CFSG.Quasithin.Chapter1.Section03.Basic.FrattiniAction
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.Covering
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupAction.SubgroupConjugation
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The solvable uniqueness family Ξ

Definition 1.3.1 and the definition following Lemma 1.3.3 in Aschbacher–Smith,
*The Classification of Quasithin Groups*, combined manuscript of 1 March 2004,
printed pp. 508–509. The odd quotient alternatives below are their intrinsic,
isomorphism-invariant descriptions: an elementary abelian group of order p²,
or an extraspecial group of order p³ and exponent p (Notation A.1.22).
The action is the actual conjugation action on the iterated Frattini quotient.
The star excludes the specified quasisimple local overgroups; it is not maximality.

Lemma 1.3.2 uses Sylow images, Frattini’s argument, the irreducibility
argument in `Basic.FrattiniAction`, and the universal property of O².
The global passage to He is stated separately with the precise earlier source
inputs. It must not be inferred from a merely intrinsic SQTK hypothesis.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter1

variable {G : Type*} [Group G]

/-- The two odd groups in Definition 1.3.1, described by intrinsic group properties.
The exponent condition in the extraspecial alternative is essential. -/
def XiOddQuotient (p : ℕ) (Q : Type*) [Group Q] : Prop :=
  (IsElementaryAbelian p Q ∧ Nat.card Q = p ^ 2) ∨
    (IsExtraspecial p Q ∧ Nat.card Q = p ^ 3 ∧ Monoid.exponent Q = p)

/-- The quotient X/O₂(X) used in Definition 1.3.1. -/
abbrev XiQuotient (X : Subgroup G) := X ⧸ pCore 2 X

/-- The Frattini quotient of X/O₂(X), not the Frattini quotient of X itself. -/
abbrev XiFrattiniQuotient (X : Subgroup G) := XiQuotient X ⧸ frattini (XiQuotient X)

/-- Conjugation by a normalizing subgroup, followed by the two characteristic quotients. -/
def xiFrattiniAction (T X : Subgroup G) (hn : T ≤ normalizer (X : Set G)) :
    T →* MulAut (XiFrattiniQuotient X) :=
  let _ := conjMulDistribMulActionOfLeNormalizer T X hn
  (quotientAut (frattini (XiQuotient X))).comp
    ((quotientAut (pCore 2 X)).comp (MulDistribMulAction.toMulAut T X))

/-- The actual three conditions of Definition 1.3.1. T may be supplied as an
ambient subgroup; the Sylow hypotheses needed by individual lemmas are explicit. -/
structure XiMember (T X : Subgroup G) : Prop where
  perfect : IsPPerfect 2 X
  invariant : T ≤ normalizer (X : Set G)
  join_mem_H : X ⊔ T ∈ H G
  odd_quotient : ∃ p : ℕ, p.Prime ∧ Odd p ∧ XiOddQuotient p (XiQuotient X)
  irreducible : ∀ A : Subgroup (XiFrattiniQuotient X),
    (∀ t : T, ∀ a ∈ A, xiFrattiniAction T X invariant t a ∈ A) → A = ⊥ ∨ A = ⊤

/-- Definition 1.3.1: the solvable uniqueness family Ξ(G,T). -/
def Xi (G : Type*) [Group G] (T : Subgroup G) : Set (Subgroup G) :=
  {X | XiMember T X}

/-- The definition after 1.3.3: exclude containment in quasisimple local overgroups. -/
def XiStar (G : Type*) [Group G] (T : Subgroup G) : Set (Subgroup G) :=
  {X | X ∈ Xi G T ∧ ∀ L₀ ∈ L G T, Theory.GroupTheory.IsQuasisimple (L₀ ⧸ pCore 2 L₀) →
    ¬ X ⊔ T ≤ L₀ ⊔ T}

/-- The star family is contained in Ξ. -/
theorem XiStar_subset_Xi (T : Subgroup G) : XiStar G T ⊆ Xi G T := fun _ h => h.1

/-- Either odd quotient alternative is a p-group. -/
theorem XiOddQuotient.isPGroup {p : ℕ} [Fact p.Prime] {Q : Type*} [Group Q]
    (h : XiOddQuotient p Q) : IsPGroup p Q := by
  rcases h with ⟨_, hc⟩ | ⟨_, hc, _⟩
  · exact IsPGroup.of_card hc
  · exact IsPGroup.of_card hc

/-- Both alternatives have nontrivial underlying groups. -/
theorem XiOddQuotient.one_lt_card {p : ℕ} (hp : p.Prime) {Q : Type*} [Group Q]
    (h : XiOddQuotient p Q) : 1 < Nat.card Q := by
  rcases h with ⟨_, hc⟩ | ⟨_, hc, _⟩
  · rw [hc]
    exact one_lt_pow₀ hp.one_lt (by decide)
  · rw [hc]
    exact one_lt_pow₀ hp.one_lt (by decide)

/-- A member of Ξ is nontrivial, already from its odd quotient. -/
theorem XiMember.ne_bot {T X : Subgroup G} (hX : XiMember T X) : X ≠ ⊥ := by
  obtain ⟨p, hp, _, hq⟩ := hX.odd_quotient
  intro he
  have : Subsingleton X := by rw [he]; infer_instance
  have : Subsingleton (XiQuotient X) := ⟨fun a b => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) b
    exact congrArg (QuotientGroup.mk' (pCore 2 X)) (Subsingleton.elim x y)⟩
  have hc : Nat.card (XiQuotient X) = 1 := Nat.card_eq_one_iff_unique.mpr
    ⟨inferInstance, inferInstance⟩
  have := hq.one_lt_card hp
  omega

/-- Invariance means relative normality in XT. -/
theorem XiMember.normal_in_join {T X : Subgroup G} (hX : XiMember T X) :
    (X.subgroupOf (X ⊔ T)).Normal :=
  normal_subgroupOf_of_le_normalizer (sup_le X.le_normalizer hX.invariant)

/-- The Ξ-to-He bridge, with the exact universal inputs 1.1.3(1) and 1.1.4(6).
The source section's assembly owner discharges these under its global hypotheses. -/
theorem XiMember.mem_He {T X : Subgroup G} (hX : XiMember T X)
    (h113 : ∀ M ∈ He G, ∀ N : Subgroup G, N ≠ ⊥ → N ≤ M →
      (N.subgroupOf M).IsSubnormal → N ∈ He G)
    (h114 : HOver G (T : Set G) ⊆ He G) : X ∈ He G := by
  have hm : X ⊔ T ∈ He G := h114 ⟨hX.join_mem_H, show T ≤ X ⊔ T from le_sup_right⟩
  let _ := hX.normal_in_join
  exact h113 _ hm X hX.ne_bot le_sup_left hX.normal_in_join.isSubnormal

/-- Nontriviality of O₂(X) follows from the global He bridge and X ≠ 1. -/
theorem XiMember.pCoreIn_ne_bot {T X : Subgroup G} (hX : XiMember T X)
    (h113 : ∀ M ∈ He G, ∀ N : Subgroup G, N ≠ ⊥ → N ≤ M →
      (N.subgroupOf M).IsSubnormal → N ∈ He G)
    (h114 : HOver G (T : Set G) ⊆ He G) : X.pCoreIn 2 ≠ ⊥ := by
  intro he
  have hh := hX.mem_He h113 h114
  change X ⊓ centralizer (X.pCoreIn 2 : Set G) ≤ X.pCoreIn 2 at hh
  apply hX.ne_bot
  apply bot_unique
  intro x hx
  apply he ▸ hh
  refine ⟨hx, ?_⟩
  intro y hy
  have hy1 : y = 1 := hy
  simp [hy1]

/-- The source's {2,p}-order statement, with its odd prime made explicit. -/
theorem XiMember.card_prime_divisors [Finite G] {T X : Subgroup G}
    (hX : XiMember T X) : ∃ p : ℕ, p.Prime ∧ Odd p ∧
      XiOddQuotient p (XiQuotient X) ∧
      ∀ q : ℕ, q.Prime → q ∣ Nat.card X → q = 2 ∨ q = p := by
  obtain ⟨p, hp, ho, hq⟩ := hX.odd_quotient
  let _ : Fact p.Prime := ⟨hp⟩
  refine ⟨p, hp, ho, hq, ?_⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).mp (pCore_isPGroup (G := X))
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := p)).mp hq.isPGroup
  have hc : Nat.card X = 2 ^ a * p ^ b := by
    rw [← (pCore 2 X).card_mul_index, ha, Subgroup.index, hb]
  intro q hprime hd
  rw [hc] at hd
  rcases hprime.dvd_mul.mp hd with hd | hd
  · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp (hprime.dvd_of_dvd_pow hd)
      |>.resolve_left hprime.ne_one)
  · exact Or.inr ((Nat.dvd_prime hp).mp (hprime.dvd_of_dvd_pow hd)
      |>.resolve_left hprime.ne_one)

/-- Every Sylow p-subgroup supplements O₂(X) when the quotient is a p-group. -/
theorem XiMember.sylow_sup [Finite G] {T X : Subgroup G} (_hX : XiMember T X)
    {p : ℕ} [Fact p.Prime] (hq : XiOddQuotient p (XiQuotient X)) (P : Sylow p X) :
    X.pCoreIn 2 ⊔ (P : Subgroup X).map X.subtype = X := by
  let q := QuotientGroup.mk' (pCore 2 X)
  have htop : (P : Subgroup X).map q = ⊤ :=
    top_unique ((hq.isPGroup.to_subgroup ⊤).le_sylow_of_normal
      (P.mapSurjective (QuotientGroup.mk'_surjective _)))
  have hsup : pCore 2 X ⊔ (P : Subgroup X) = ⊤ := by
    have hh := congrArg (fun A : Subgroup (XiQuotient X) => A.comap q) htop
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top, sup_comm] using hh
  have hh := congrArg (fun A : Subgroup X => A.map X.subtype) hsup
  simpa only [Subgroup.map_sup, ← MonoidHom.range_eq_map, X.range_subtype, pCoreIn] using hh

/-- The Sylow supplement is a complement, since p is odd. -/
theorem XiMember.sylow_disjoint {T X : Subgroup G} (_hX : XiMember T X)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (P : Sylow p X) :
    Disjoint (X.pCoreIn 2) ((P : Subgroup X).map X.subtype) := by
  exact (isPGroup_pCoreIn 2 X).disjoint_of_coprime (P.isPGroup'.map X.subtype)
    (Nat.coprime_two_left.mpr ho)

/-- Lemma 1.3.2(5), in ambient subgroup notation. The Sylow hypothesis puts
O₂(H) inside T; adjoining that normalizing two-group preserves O²(X). -/
theorem lemma_1_3_2_5 [Finite G] (T : Sylow 2 G) {X H₀ : Subgroup G}
    (hX : XiMember (T : Subgroup G) X)
    (hH : H₀ ∈ HOver G ((X ⊔ (T : Subgroup G) : Subgroup G) : Set G)) :
    (pResidual 2 (H₀.pCoreIn 2 ⊔ X : Subgroup G)).map (H₀.pCoreIn 2 ⊔ X).subtype = X := by
  have hTH : (T : Subgroup G) ≤ H₀ := le_sup_right.trans hH.2
  have hcoreT : H₀.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using
      pCoreIn_le_sylow H₀ (T.subtype hTH)
  rw [sup_comm (H₀.pCoreIn 2) X]
  exact embedded_pResidual_join_pGroup X (H₀.pCoreIn 2)
    hX.perfect (isPGroup_pCoreIn 2 H₀) (hcoreT.trans hX.invariant)


private theorem normalClosure_eq_top_of_twoPerfect_supplement
    {K : Type*} [Group K] (N P : Subgroup K) [N.Normal]
    (hN : IsPGroup 2 N) (hK : IsPPerfect 2 K) (hgen : N ⊔ P = ⊤) :
    normalClosure (P : Set K) = ⊤ := by
  apply hK _ inferInstance
  apply isPGroup_quotient_of_sup_eq_top _ N hN
  apply top_unique
  rw [← hgen]
  exact sup_le le_sup_right (le_normalClosure.trans le_sup_left)

private theorem normalClosure_eq_core_conjugates
    {K : Type*} [Group K] (N P : Subgroup K) [N.Normal] (hgen : N ⊔ P = ⊤) :
    normalClosure (P : Set K) =
      closure {g : K | ∃ n ∈ N, ∃ p ∈ P, n * p * n⁻¹ = g} := by
  apply le_antisymm
  · apply (Subgroup.closure_le (K := _)).mpr
    intro g hg
    obtain ⟨p, hp, hc⟩ := Group.mem_conjugatesOfSet_iff.mp hg
    obtain ⟨k, rfl⟩ := isConj_iff.mp hc
    have hk : k ∈ N ⊔ P := by rw [hgen]; trivial
    obtain ⟨n, hn, b, hb, rfl⟩ := mem_sup_of_normal_left.mp hk
    apply Subgroup.subset_closure
    refine ⟨n, hn, b * p * b⁻¹, P.mul_mem (P.mul_mem hb hp) (P.inv_mem hb), ?_⟩
    simp only [mul_inv_rev, mul_assoc]
  · apply (Subgroup.closure_le (K := _)).mpr
    rintro g ⟨n, _, p, hp, rfl⟩
    exact (inferInstance : (normalClosure (P : Set K)).Normal).conj_mem p
      (le_normalClosure hp) n

private theorem core_eq_commutator_of_twoPerfect_complement
    {K : Type*} [Group K] (N P : Subgroup K) [N.Normal]
    (hN : IsPGroup 2 N) (hK : IsPPerfect 2 K)
    (hgen : N ⊔ P = ⊤) (hdis : Disjoint N P) : N = ⁅N, P⁆ := by
  let D := ⁅N, P⁆
  have hDN : D ≤ N := commutator_le_left N P
  have hDn : D.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    exact sup_le (normalizer_commutator_ge_left N P) (normalizer_commutator_ge_right N P)
  let _ := hDn
  have hEn : (D ⊔ P).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    apply sup_le ?_ (le_sup_right.trans (D ⊔ P).le_normalizer)
    apply le_normalizer_iff.mpr
    intro n hn a ha
    obtain ⟨d, hd, p, hp, rfl⟩ := mem_sup_of_normal_left.mp ha
    have hd' : n * d * n⁻¹ ∈ D := hDn.conj_mem d hd n
    have hp' : n * p * n⁻¹ ∈ D ⊔ P := by
      have hh := (D ⊔ P).mul_mem ((show D ≤ D ⊔ P from le_sup_left) (commutator_mem_commutator hn hp))
        ((show P ≤ D ⊔ P from le_sup_right) hp)
      simpa only [commutatorElement_def, inv_mul_cancel_right] using hh
    have hh := (D ⊔ P).mul_mem ((show D ≤ D ⊔ P from le_sup_left) hd') hp'
    simpa only [mul_assoc, inv_mul_cancel_left] using hh
  let _ := hEn
  have hE : D ⊔ P = ⊤ := by
    apply top_unique
    rw [← normalClosure_eq_top_of_twoPerfect_supplement N P hN hK hgen]
    exact normalClosure_le_normal (show P ≤ D ⊔ P from le_sup_right)
  apply le_antisymm ?_ hDN
  intro n hn
  have hne : n ∈ D ⊔ P := by rw [hE]; trivial
  obtain ⟨d, hd, p, hp, hdp⟩ := mem_sup_of_normal_left.mp hne
  have hpN : p ∈ N := by
    have hh := N.mul_mem (N.inv_mem (hDN hd)) hn
    rw [← hdp] at hh
    simpa only [inv_mul_cancel_left] using hh
  have hp1 : p = 1 := hdis.le_bot ⟨hpN, hp⟩
  have hnd : n = d := by simpa only [hp1, mul_one] using hdp.symm
  exact hnd.symm ▸ hd

/-- Lemma 1.3.2(2), first conjugate-generation equality, in the ambient group. -/
theorem XiMember.normalClosure_sylow [Finite G] {T X : Subgroup G}
    (hX : XiMember T X) {p : ℕ} [Fact p.Prime]
    (hq : XiOddQuotient p (XiQuotient X)) (P : Sylow p X) :
    (normalClosure (P : Set X)).map X.subtype = X := by
  have hgen : pCore 2 X ⊔ (P : Subgroup X) = ⊤ := by
    apply (map_injective X.subtype_injective)
    simpa only [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype, pCoreIn]
      using hX.sylow_sup hq P
  change (normalClosure ((P : Subgroup X) : Set X)).map X.subtype = X
  rw [normalClosure_eq_top_of_twoPerfect_supplement (pCore 2 X) (P : Subgroup X)
    pCore_isPGroup hX.perfect hgen, ← MonoidHom.range_eq_map, range_subtype]

/-- Lemma 1.3.2(2), generation by the O₂(X)-conjugates of P. The displayed
set uses only ambient group elements and the actual embedded Sylow subgroup. -/
theorem XiMember.core_conjugates_sylow [Finite G] {T X : Subgroup G}
    (hX : XiMember T X) {p : ℕ} [Fact p.Prime]
    (hq : XiOddQuotient p (XiQuotient X)) (P : Sylow p X) :
    closure {g : G | ∃ n ∈ X.pCoreIn 2, ∃ a ∈ (P : Subgroup X).map X.subtype,
      n * a * n⁻¹ = g} = X := by
  have hgen : pCore 2 X ⊔ (P : Subgroup X) = ⊤ := by
    apply (map_injective X.subtype_injective)
    simpa only [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype, pCoreIn]
      using hX.sylow_sup hq P
  apply Eq.trans ?_ (hX.normalClosure_sylow hq P)
  change _ = (normalClosure ((P : Subgroup X) : Set X)).map X.subtype
  rw [normalClosure_eq_core_conjugates (pCore 2 X) (P : Subgroup X) hgen,
    MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨n, ⟨n', hn', rfl⟩, a, ⟨a', ha', rfl⟩, rfl⟩
    exact ⟨n' * a' * n'⁻¹, ⟨n', hn', a', ha', rfl⟩, rfl⟩
  · rintro ⟨g', ⟨n, hn, a, ha, rfl⟩, rfl⟩
    exact ⟨n, ⟨n, hn, rfl⟩, a, ⟨a, ha, rfl⟩, rfl⟩

/-- Lemma 1.3.2(2), the commutator identity O₂(X) = [O₂(X),P]. -/
theorem XiMember.pCoreIn_eq_commutator [Finite G] {T X : Subgroup G}
    (hX : XiMember T X) {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hq : XiOddQuotient p (XiQuotient X)) (P : Sylow p X) :
    X.pCoreIn 2 = ⁅X.pCoreIn 2, (P : Subgroup X).map X.subtype⁆ := by
  have hgen : pCore 2 X ⊔ (P : Subgroup X) = ⊤ := by
    apply (map_injective X.subtype_injective)
    simpa only [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype, pCoreIn]
      using hX.sylow_sup hq P
  have hd : Disjoint (pCore 2 X) (P : Subgroup X) :=
    pCore_isPGroup.disjoint_of_coprime P.isPGroup' (Nat.coprime_two_left.mpr ho)
  have hh := congrArg (fun A : Subgroup X => A.map X.subtype)
    (core_eq_commutator_of_twoPerfect_complement (pCore 2 X) (P : Subgroup X)
      pCore_isPGroup hX.perfect hgen hd)
  simpa only [map_commutator, pCoreIn] using hh


/-- O₂(X) lies in T whenever T is Sylow in XT. This is a local assertion. -/
theorem XiMember.pCoreIn_le_of_isSylowIn {T X : Subgroup G} (hX : XiMember T X)
    (hT : IsSylowIn 2 T (X ⊔ T)) : X.pCoreIn 2 ≤ T := by
  obtain ⟨S, hS⟩ := hT
  have hc : X.pCoreIn 2 ≤ (X ⊔ T).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left (sup_le X.le_normalizer hX.invariant)
  exact hc.trans ((pCoreIn_le_sylow (X ⊔ T) S).trans_eq hS)

/-- The Frattini factorization in 1.3.2(3). The weaker local Sylow hypothesis
is sufficient and makes the result available to intrinsic applications. -/
theorem XiMember.normalizer_factor [Finite G] {T X : Subgroup G}
    (hX : XiMember T X) (hT : IsSylowIn 2 T (X ⊔ T))
    {p : ℕ} [Fact p.Prime] (hq : XiOddQuotient p (XiQuotient X)) (P : Sylow p X) :
    T = X.pCoreIn 2 ⊔ (T ⊓ normalizer ((P : Subgroup X).map X.subtype : Set G)) := by
  let W := X ⊔ T
  let N := X.subgroupOf W
  let e : X ≃* N := (subgroupOfEquivOfLe (show X ≤ W from le_sup_left)).symm
  let R : Sylow p N := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let _ : N.Normal := hX.normal_in_join
  have hm : ((R : Subgroup N).map N.subtype).map W.subtype =
      (P : Subgroup X).map X.subtype := by
    change (((P : Subgroup X).map e.toMonoidHom).map N.subtype).map W.subtype = _
    rw [map_map, map_map]
    rfl
  have hfr : N ⊔ normalizer ((R : Subgroup N).map N.subtype : Set W) = ⊤ := by
    rw [sup_comm]
    exact R.normalizer_sup_eq_top
  have hcT := hX.pCoreIn_le_of_isSylowIn hT
  apply le_antisymm ?_ (sup_le hcT inf_le_left)
  intro t ht
  have htW : t ∈ W := (show T ≤ W from le_sup_right) ht
  have htgen : (⟨t, htW⟩ : W) ∈ N ⊔
      normalizer ((R : Subgroup N).map N.subtype : Set W) := by rw [hfr]; trivial
  obtain ⟨x, hx, n, hn, hxn⟩ := mem_sup_of_normal_left.mp htgen
  have hnG : (n : G) ∈ normalizer ((P : Subgroup X).map X.subtype : Set G) := by
    rw [← hm]
    exact (((R : Subgroup N).map N.subtype).le_normalizer_map W.subtype)
      (mem_map_of_mem W.subtype hn)
  have hxX : (x : G) ∈ X := hx
  have hxgen : (⟨x, hxX⟩ : X) ∈ pCore 2 X ⊔ (P : Subgroup X) := by
    have hgen : pCore 2 X ⊔ (P : Subgroup X) = ⊤ := by
      apply (map_injective X.subtype_injective)
      simpa only [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype, pCoreIn]
        using hX.sylow_sup hq P
    rw [hgen]
    trivial
  obtain ⟨c, hc, a, ha, hca⟩ := mem_sup_of_normal_left.mp hxgen
  have hcG : (c : G) ∈ X.pCoreIn 2 := mem_map_of_mem X.subtype hc
  have hprod : (c : G) * ((a : G) * (n : G)) = t := by
    have he := congrArg (fun z : X => (z : G)) hca
    have he' := congrArg (fun z : W => (z : G)) hxn
    change (c : G) * (a : G) = (x : G) at he
    change (x : G) * (n : G) = t at he'
    rw [← mul_assoc, he, he']
  have hanT : (a : G) * (n : G) ∈ T := by
    have hh := T.mul_mem (T.inv_mem (hcT hcG)) ht
    rw [← hprod] at hh
    simpa only [inv_mul_cancel_left] using hh
  have hanN : (a : G) * (n : G) ∈
      normalizer ((P : Subgroup X).map X.subtype : Set G) :=
    (normalizer _).mul_mem (le_normalizer (mem_map_of_mem X.subtype ha)) hnG
  exact hprod ▸ mul_mem_sup hcG ⟨hanT, hanN⟩

/-- The complement identifies P with the actual quotient X/O₂(X). -/
noncomputable def XiMember.sylowQuotientEquiv [Finite G] {T X : Subgroup G}
    (_hX : XiMember T X) {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hq : XiOddQuotient p (XiQuotient X)) (P : Sylow p X) : P ≃* XiQuotient X := by
  let q := QuotientGroup.mk' (pCore 2 X)
  let f : P →* XiQuotient X := q.comp (P : Subgroup X).subtype
  apply MulEquiv.ofBijective f
  constructor
  · apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro a ha
    have hc : (a : X) ∈ pCore 2 X := (QuotientGroup.eq_one_iff _).mp ha
    have hd : Disjoint (pCore 2 X) (P : Subgroup X) :=
      pCore_isPGroup.disjoint_of_coprime P.isPGroup' (Nat.coprime_two_left.mpr ho)
    exact Subtype.ext (hd.le_bot ⟨hc, a.property⟩)
  · apply MonoidHom.range_eq_top.mp
    have htop : (P : Subgroup X).map q = ⊤ :=
      top_unique ((hq.isPGroup.to_subgroup ⊤).le_sylow_of_normal
        (P.mapSurjective (QuotientGroup.mk'_surjective _)))
    simpa only [f, MonoidHom.range_comp, range_subtype] using htop

/-- The complement equivalence is the quotient projection on every element. -/
theorem XiMember.sylowQuotientEquiv_apply [Finite G] {T X : Subgroup G}
    (hX : XiMember T X) {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hq : XiOddQuotient p (XiQuotient X)) (P : Sylow p X) (a : P) :
    hX.sylowQuotientEquiv ho hq P a = QuotientGroup.mk' (pCore 2 X) (a : X) := rfl


private theorem frattini_map_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (frattini A).map e.toMonoidHom = frattini B := by
  apply le_antisymm
  · exact map_le_iff_le_comap.mpr (frattini_le_comap_frattini_of_surjective e.surjective)
  · intro b hb
    refine ⟨e.symm b, frattini_le_comap_frattini_of_surjective (φ := e.symm.toMonoidHom) e.symm.surjective hb, ?_⟩
    exact e.apply_symm_apply b

/-- The same Sylow complement equivalence for its ambient image. -/
noncomputable def XiMember.ambientSylowQuotientEquiv [Finite G] {T X : Subgroup G}
    (hX : XiMember T X) {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hq : XiOddQuotient p (XiQuotient X)) (P : Sylow p X) :
    ((P : Subgroup X).map X.subtype) ≃* XiQuotient X := by
  let P₀ := (P : Subgroup X).map X.subtype
  let i : P₀ →* X := inclusion (map_subtype_le (P : Subgroup X))
  let f := (QuotientGroup.mk' (pCore 2 X)).comp i
  apply MulEquiv.ofBijective f
  constructor
  · apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro a ha
    have hc : i a ∈ pCore 2 X := (QuotientGroup.eq_one_iff _).mp ha
    have hca : (a : G) ∈ X.pCoreIn 2 := mem_map_of_mem X.subtype hc
    exact Subtype.ext ((hX.sylow_disjoint ho P).le_bot ⟨hca, a.property⟩)
  · intro y
    obtain ⟨a, ha⟩ := (hX.sylowQuotientEquiv ho hq P).surjective y
    refine ⟨⟨a, mem_map_of_mem X.subtype a.property⟩, ?_⟩
    exact ha

/-- The induced equivalence of Frattini quotients, retaining the actual quotient maps. -/
noncomputable def XiMember.sylowFrattiniEquiv [Finite G] {T X : Subgroup G}
    (hX : XiMember T X) {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hq : XiOddQuotient p (XiQuotient X)) (P : Sylow p X) :
    (((P : Subgroup X).map X.subtype) ⧸ frattini ((P : Subgroup X).map X.subtype)) ≃*
      XiFrattiniQuotient X := by
  exact QuotientGroup.congr _ _ (hX.ambientSylowQuotientEquiv ho hq P)
    (by exact frattini_map_equiv _)

/-- Naturality of the Frattini equivalence on elements of the ambient Sylow subgroup. -/
theorem XiMember.sylowFrattiniEquiv_apply_mk [Finite G] {T X : Subgroup G}
    (hX : XiMember T X) {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hq : XiOddQuotient p (XiQuotient X)) (P : Sylow p X)
    (a : (P : Subgroup X).map X.subtype) :
    hX.sylowFrattiniEquiv ho hq P (QuotientGroup.mk' _ a) =
      QuotientGroup.mk' (frattini (XiQuotient X))
        (QuotientGroup.mk' (pCore 2 X) (inclusion (map_subtype_le (P : Subgroup X)) a)) := rfl

/-- Members of O₂(X) act trivially on the iterated quotient used to define Ξ. -/
theorem XiMember.core_fixes_frattini {T X : Subgroup G} (hX : XiMember T X)
    (t : T) (ht : (t : G) ∈ X.pCoreIn 2) (v : XiFrattiniQuotient X) :
    xiFrattiniAction T X hX.invariant t v = v := by
  let _ := conjMulDistribMulActionOfLeNormalizer T X hX.invariant
  obtain ⟨n, hn, he⟩ := ht
  change (n : G) = (t : G) at he
  induction v using QuotientGroup.induction_on with | H v =>
    induction v using QuotientGroup.induction_on with | H x =>
      change xiFrattiniAction T X hX.invariant t
        (QuotientGroup.mk' (frattini (XiQuotient X)) (QuotientGroup.mk' (pCore 2 X) x)) =
        QuotientGroup.mk' (frattini (XiQuotient X)) (QuotientGroup.mk' (pCore 2 X) x)
      simp only [xiFrattiniAction, MonoidHom.comp_apply, quotientAut_apply_mk]
      have heq : (MulDistribMulAction.toMulAut T X t) x = n * x * n⁻¹ := by
        apply Subtype.ext
        change (t : G) * (x : G) * (t : G)⁻¹ = (n : G) * (x : G) * (n : G)⁻¹
        rw [he]
      have hnq : QuotientGroup.mk' (pCore 2 X) n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
      rw [heq]
      simp only [map_mul, map_inv, hnq, one_mul, inv_one, mul_one]

/-- The normalizer and the defining T-action agree through the Sylow complement isomorphism. -/
theorem XiMember.sylowFrattiniEquiv_equivariant [Finite G] {T X : Subgroup G}
    (hX : XiMember T X) {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hq : XiOddQuotient p (XiQuotient X)) (P : Sylow p X)
    (s : (T ⊓ normalizer ((P : Subgroup X).map X.subtype : Set G) : Subgroup G))
    (v : ((P : Subgroup X).map X.subtype) ⧸ frattini ((P : Subgroup X).map X.subtype)) :
    hX.sylowFrattiniEquiv ho hq P
      (frattiniConjugationAction _ _ inf_le_right s v) =
      xiFrattiniAction T X hX.invariant ⟨s, s.property.1⟩
        (hX.sylowFrattiniEquiv ho hq P v) := by
  induction v using QuotientGroup.induction_on with | H a =>
    change hX.sylowFrattiniEquiv ho hq P
      (frattiniConjugationAction _ _ inf_le_right s (QuotientGroup.mk' _ a)) =
      xiFrattiniAction T X hX.invariant ⟨s, s.property.1⟩
        (hX.sylowFrattiniEquiv ho hq P (QuotientGroup.mk' _ a))
    simp only [frattiniConjugationAction, MonoidHom.comp_apply, quotientAut_apply_mk,
      XiMember.sylowFrattiniEquiv_apply_mk, xiFrattiniAction]
    rfl

/-- The irreducibility clause of Lemma 1.3.2(3), on the actual P/Φ(P).
Here P is represented by its ambient image, and the Sylow condition is local. -/
theorem XiMember.normalizer_irreducible [Finite G] {T X : Subgroup G}
    (hX : XiMember T X) (hT : IsSylowIn 2 T (X ⊔ T))
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hq : XiOddQuotient p (XiQuotient X))
    (P : Sylow p X) :
    let P₀ := (P : Subgroup X).map X.subtype
    let S := T ⊓ normalizer (P₀ : Set G)
    ∀ A : Subgroup (P₀ ⧸ frattini P₀),
      (∀ s : S, ∀ a ∈ A, frattiniConjugationAction S P₀ inf_le_right s a ∈ A) →
      A = ⊥ ∨ A = ⊤ := by
  dsimp only
  intro A hA
  let e := hX.sylowFrattiniEquiv ho hq P
  let B := A.map e.toMonoidHom
  let S := T ⊓ normalizer ((P : Subgroup X).map X.subtype : Set G)
  have hS : S ≤ normalizer (X.pCoreIn 2 : Set G) :=
    inf_le_left.trans (hX.invariant.trans
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
  have hB : ∀ t : T, ∀ b ∈ B, xiFrattiniAction T X hX.invariant t b ∈ B := by
    intro t b hb
    have ht : (t : G) ∈ X.pCoreIn 2 ⊔ S := hX.normalizer_factor hT hq P ▸ t.property
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hS] at ht
    obtain ⟨c, hc, s, hs, hcs⟩ := ht
    let cT : T := ⟨c, hX.pCoreIn_le_of_isSylowIn hT hc⟩
    let sT : T := ⟨s, hs.1⟩
    have hts : t = cT * sT := Subtype.ext hcs.symm
    rw [hts, map_mul]
    change xiFrattiniAction T X hX.invariant cT
      (xiFrattiniAction T X hX.invariant sT b) ∈ B
    rw [hX.core_fixes_frattini cT hc]
    obtain ⟨a, ha, rfl⟩ := hb
    exact mem_map.mpr ⟨frattiniConjugationAction S _ inf_le_right ⟨s, hs⟩ a,
      hA ⟨s, hs⟩ a ha, hX.sylowFrattiniEquiv_equivariant ho hq P ⟨s, hs⟩ a⟩
  rcases hX.irreducible B hB with hb | hb
  · left
    exact (A.map_eq_bot_iff_of_injective e.injective).mp hb
  · right
    apply (map_injective e.injective)
    change A.map e.toMonoidHom = (⊤ : Subgroup _).map e.toMonoidHom
    rw [map_top_of_surjective e.toMonoidHom e.surjective]
    exact hb


/-- Neither of the odd quotient groups in Definition 1.3.1 is cyclic. -/
theorem XiOddQuotient.not_isCyclic {p : ℕ} [Fact p.Prime] {Q : Type*}
    [Group Q] [Finite Q] (h : XiOddQuotient p Q) : ¬ IsCyclic Q := by
  intro hc
  let _ := hc
  rcases h with ⟨he, hcard⟩ | ⟨he, _, _⟩
  · let _ := he
    exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hcard hc
  · let _ := IsCyclic.isMulCommutative (α := Q)
    exact (QuotientGroup.nontrivial_iff.mp he.quotient_nontrivial) (center_eq_top (G := Q))

/-- The ambient Sylow complement is noncyclic. -/
theorem XiMember.sylow_not_isCyclic [Finite G] {T X : Subgroup G}
    (hX : XiMember T X) {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hq : XiOddQuotient p (XiQuotient X)) (P : Sylow p X) :
    ¬ IsCyclic ((P : Subgroup X).map X.subtype) := by
  intro hc
  let _ := hc
  exact hq.not_isCyclic (isCyclic_of_surjective
    (hX.ambientSylowQuotientEquiv ho hq P).toMonoidHom
    (hX.ambientSylowQuotientEquiv ho hq P).surjective)

/-- Lemma 1.3.2(1): X is a {2,p}-group and every Sylow p-subgroup complements
its two-core. The witness records the same p as the defining quotient. -/
theorem lemma_1_3_2_1 [Finite G] {T X : Subgroup G} (hX : X ∈ Xi G T) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ XiOddQuotient p (XiQuotient X) ∧
      (∀ q : ℕ, q.Prime → q ∣ Nat.card X → q = 2 ∨ q = p) ∧
      ∃ P : Sylow p X, X.pCoreIn 2 ⊔ (P : Subgroup X).map X.subtype = X ∧
        Disjoint (X.pCoreIn 2) ((P : Subgroup X).map X.subtype) := by
  obtain ⟨p, hp, ho, hq, hd⟩ := hX.card_prime_divisors
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := X)
  exact ⟨p, hp, ho, hq, hd, P, hX.sylow_sup hq P, hX.sylow_disjoint ho P⟩

/-- Lemma 1.3.2(2): the two conjugate-generation statements and the core commutator. -/
theorem lemma_1_3_2_2 [Finite G] {T X : Subgroup G} (hX : X ∈ Xi G T)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hq : XiOddQuotient p (XiQuotient X))
    (P : Sylow p X) :
    (normalClosure (P : Set X)).map X.subtype = X ∧
      closure {g : G | ∃ n ∈ X.pCoreIn 2, ∃ a ∈ (P : Subgroup X).map X.subtype,
        n * a * n⁻¹ = g} = X ∧
      X.pCoreIn 2 = ⁅X.pCoreIn 2, (P : Subgroup X).map X.subtype⁆ :=
  ⟨hX.normalClosure_sylow hq P, hX.core_conjugates_sylow hq P,
    hX.pCoreIn_eq_commutator ho hq P⟩

/-- Lemma 1.3.2(3), including the actual Frattini-quotient irreducibility.
The source's ambient Sylow T supplies the displayed local Sylow hypothesis. -/
theorem lemma_1_3_2_3 [Finite G] {T X : Subgroup G} (hX : X ∈ Xi G T)
    (hT : IsSylowIn 2 T (X ⊔ T)) {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hq : XiOddQuotient p (XiQuotient X)) (P : Sylow p X) :
    let P₀ := (P : Subgroup X).map X.subtype
    let S := T ⊓ normalizer (P₀ : Set G)
    T = X.pCoreIn 2 ⊔ S ∧ ∀ A : Subgroup (P₀ ⧸ frattini P₀),
      (∀ s : S, ∀ a ∈ A, frattiniConjugationAction S P₀ inf_le_right s a ∈ A) →
      A = ⊥ ∨ A = ⊤ :=
  ⟨hX.normalizer_factor hT hq P, hX.normalizer_irreducible hT ho hq P⟩


/-- Lemma 1.3.2(4): the Frattini subgroup of the Sylow normalizer generates
P by commutators. The Sylow condition is local to XT. -/
theorem lemma_1_3_2_4 [Finite G] {T X : Subgroup G} (hX : X ∈ Xi G T)
    (hT : IsSylowIn 2 T (X ⊔ T)) {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hq : XiOddQuotient p (XiQuotient X)) (P : Sylow p X) :
    let P₀ := (P : Subgroup X).map X.subtype
    let S := T ⊓ normalizer (P₀ : Set G)
    P₀ = ⁅P₀, (frattini S).map S.subtype⁆ := by
  dsimp only
  apply XiAction.eq_commutator_frattini_of_irreducible _ _ inf_le_right
    ((isSylowIn_iff.mp hT).1.to_le inf_le_left) (P.isPGroup'.map X.subtype)
    (hX.sylow_not_isCyclic ho hq P)
  exact hX.normalizer_irreducible hT ho hq P

/-- The local form of Lemma 1.3.2(5). It suffices that T be Sylow in the
chosen overgroup; no Sylow condition on the external ambient group is needed. -/
theorem lemma_1_3_2_5_local [Finite G] {T X H₀ : Subgroup G}
    (hX : X ∈ Xi G T) (hT : IsSylowIn 2 T H₀) :
    (pResidual 2 (H₀.pCoreIn 2 ⊔ X : Subgroup G)).map (H₀.pCoreIn 2 ⊔ X).subtype = X := by
  obtain ⟨S, hS⟩ := hT
  have hc : H₀.pCoreIn 2 ≤ T := (pCoreIn_le_sylow H₀ S).trans_eq hS
  rw [sup_comm (H₀.pCoreIn 2) X]
  exact embedded_pResidual_join_pGroup X (H₀.pCoreIn 2)
    hX.perfect (isPGroup_pCoreIn 2 H₀) (hc.trans hX.invariant)

/-- The source inclusion Ξ(G,T) ⊆ He, with its two earlier universal inputs explicit. -/
theorem Xi_subset_He (T : Subgroup G)
    (h113 : ∀ M ∈ He G, ∀ N : Subgroup G, N ≠ ⊥ → N ≤ M →
      (N.subgroupOf M).IsSubnormal → N ∈ He G)
    (h114 : HOver G (T : Set G) ⊆ He G) : Xi G T ⊆ He G :=
  fun _ hX => hX.mem_He h113 h114

/-- Members of Ξ are solvable: both the normal two-core and the odd quotient
are finite prime-power groups. This uses no global characteristic-two assumption. -/
theorem XiMember.isSolvable [Finite G] {T X : Subgroup G} (hX : XiMember T X) :
    Group.IsSolvable X := by
  obtain ⟨p, hp, _, hq⟩ := hX.odd_quotient
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : Group.IsNilpotent (pCore 2 X) :=
    (pCore_isPGroup (p := 2) (G := X)).isNilpotent
  let _ : Group.IsNilpotent (XiQuotient X) := hq.isPGroup.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 X)).mpr
    ⟨inferInstance, inferInstance⟩

variable {G' : Type*} [Group G']

/-- The source quotient alternatives are invariant under actual group isomorphisms. -/
theorem XiOddQuotient.of_mulEquiv {p : ℕ} {A B : Type*} [Group A] [Group B]
    (h : XiOddQuotient p A) (e : A ≃* B) : XiOddQuotient p B := by
  rcases h with ⟨he, hc⟩ | ⟨he, hc, hp⟩
  · let _ := he
    exact Or.inl ⟨IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective,
      (Nat.card_congr e.toEquiv).symm.trans hc⟩
  · exact Or.inr ⟨he.of_mulEquiv e, (Nat.card_congr e.toEquiv).symm.trans hc,
      (Monoid.exponent_eq_of_mulEquiv e).symm.trans hp⟩

/-- An embedding induces an isomorphism of the actual iterated quotients defining Ξ. -/
noncomputable def xiFrattiniMapEquiv (f : G →* G') (hf : Function.Injective f)
    (X : Subgroup G) : XiFrattiniQuotient X ≃* XiFrattiniQuotient (X.map f) := by
  let e := X.equivMapOfInjective f hf
  let q := QuotientGroup.congr (pCore 2 X) (pCore 2 (X.map f)) e (pCore_map_iso 2 e)
  exact QuotientGroup.congr _ _ q (by exact frattini_map_equiv q)

/-- The iterated quotient equivalence is induced by the original embedding. -/
theorem xiFrattiniMapEquiv_mk (f : G →* G') (hf : Function.Injective f)
    (X : Subgroup G) (x : X) :
    xiFrattiniMapEquiv f hf X
      (QuotientGroup.mk' (frattini (XiQuotient X)) (QuotientGroup.mk' (pCore 2 X) x)) =
    QuotientGroup.mk' (frattini (XiQuotient (X.map f)))
      (QuotientGroup.mk' (pCore 2 (X.map f)) ((X.equivMapOfInjective f hf) x)) := rfl

/-- The iterated quotient equivalence intertwines the two conjugation actions. -/
theorem xiFrattiniMapEquiv_equivariant (f : G →* G') (hf : Function.Injective f)
    (T X : Subgroup G) (hn : T ≤ normalizer (X : Set G))
    (hm : T.map f ≤ normalizer (X.map f : Set G'))
    (t : T) (v : XiFrattiniQuotient X) :
    xiFrattiniMapEquiv f hf X (xiFrattiniAction T X hn t v) =
      xiFrattiniAction (T.map f) (X.map f) hm ((T.equivMapOfInjective f hf) t)
        (xiFrattiniMapEquiv f hf X v) := by
  induction v using QuotientGroup.induction_on with | H v =>
    induction v using QuotientGroup.induction_on with | H x =>
      change xiFrattiniMapEquiv f hf X (xiFrattiniAction T X hn t
        (QuotientGroup.mk' _ (QuotientGroup.mk' _ x))) =
          xiFrattiniAction (T.map f) (X.map f) hm ((T.equivMapOfInjective f hf) t)
            (xiFrattiniMapEquiv f hf X (QuotientGroup.mk' _ (QuotientGroup.mk' _ x)))
      simp only [xiFrattiniAction, MonoidHom.comp_apply, quotientAut_apply_mk,
        xiFrattiniMapEquiv_mk]
      congr 2
      apply Subtype.ext
      change f ((t : G) * (x : G) * (t : G)⁻¹) =
        f (t : G) * f (x : G) * (f (t : G))⁻¹
      simp only [map_mul, map_inv]

private theorem irreducible_transport {A B V W : Type*} [Group A] [Group B]
    [Group V] [Group W] (a : A ≃* B) (e : V ≃* W)
    (f : A →* MulAut V) (g : B →* MulAut W)
    (he : ∀ s v, e (f s v) = g (a s) (e v))
    (hirr : ∀ U : Subgroup V, (∀ s : A, ∀ u ∈ U, f s u ∈ U) → U = ⊥ ∨ U = ⊤) :
    ∀ U : Subgroup W, (∀ s : B, ∀ u ∈ U, g s u ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro U hU
  have hpre : ∀ s : A, ∀ u ∈ U.comap e.toMonoidHom, f s u ∈ U.comap e.toMonoidHom := by
    intro s u hu
    change e (f s u) ∈ U
    rw [he]
    exact hU _ _ hu
  rcases hirr (U.comap e.toMonoidHom) hpre with hb | ht
  · left
    have hm := congrArg (Subgroup.map e.toMonoidHom) hb
    simpa only [map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective, Subgroup.map_bot] using hm
  · right
    have hm := congrArg (Subgroup.map e.toMonoidHom) ht
    simpa only [map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective,
      map_top_of_surjective e.toMonoidHom e.surjective] using hm

private theorem normalizes_map_iff (f : G →* G') (hf : Function.Injective f)
    (T X : Subgroup G) :
    T.map f ≤ normalizer (X.map f : Set G') ↔ T ≤ normalizer (X : Set G) := by
  constructor
  · intro hm
    apply le_normalizer_iff.mpr
    intro t ht x hx
    have hh := (mem_normalizer_iff.mp (hm (mem_map_of_mem f ht)) (f x)).mp
      (mem_map_of_mem f hx)
    have hh' : f (t * x * t⁻¹) ∈ X.map f := by simpa only [map_mul, map_inv] using hh
    exact (mem_map_iff_mem hf).mp hh'
  · intro hn
    exact (map_mono hn).trans (X.le_normalizer_map f)

/-- Faithful embeddings preserve and reflect membership in Ξ. -/
theorem mem_Xi_map_iff (f : G →* G') (hf : Function.Injective f)
    {T X : Subgroup G} : X.map f ∈ Xi G' (T.map f) ↔ X ∈ Xi G T := by
  let e := X.equivMapOfInjective f hf
  let eq := QuotientGroup.congr (pCore 2 X) (pCore 2 (X.map f)) e (pCore_map_iso 2 e)
  have hH : X.map f ⊔ T.map f ∈ H G' ↔ X ⊔ T ∈ H G := by
    change (X.map f ⊔ T.map f).pCoreIn 2 ≠ ⊥ ↔ (X ⊔ T).pCoreIn 2 ≠ ⊥
    rw [← Subgroup.map_sup, ← map_pCoreIn_of_injective 2 (X ⊔ T) f hf]
    exact not_congr (((X ⊔ T).pCoreIn 2).map_eq_bot_iff_of_injective hf)
  constructor
  · intro h
    have hn := (normalizes_map_iff f hf T X).mp h.invariant
    refine ⟨h.perfect.of_surjective e.symm.toMonoidHom e.symm.surjective, hn,
      hH.mp h.join_mem_H, ?_, ?_⟩
    · obtain ⟨p, hp, ho, hq⟩ := h.odd_quotient
      exact ⟨p, hp, ho, hq.of_mulEquiv eq.symm⟩
    · apply irreducible_transport (T.equivMapOfInjective f hf).symm
        (xiFrattiniMapEquiv f hf X).symm
        (xiFrattiniAction (T.map f) (X.map f) h.invariant)
        (xiFrattiniAction T X hn) _ h.irreducible
      intro s v
      apply (xiFrattiniMapEquiv f hf X).injective
      simp only [MulEquiv.apply_symm_apply]
      rw [xiFrattiniMapEquiv_equivariant f hf T X hn h.invariant]
      simp only [MulEquiv.apply_symm_apply]
  · intro h
    have hn := (normalizes_map_iff f hf T X).mpr h.invariant
    refine ⟨h.perfect.of_surjective e.toMonoidHom e.surjective, hn,
      hH.mpr h.join_mem_H, ?_, ?_⟩
    · obtain ⟨p, hp, ho, hq⟩ := h.odd_quotient
      exact ⟨p, hp, ho, hq.of_mulEquiv eq⟩
    · exact irreducible_transport (T.equivMapOfInjective f hf) (xiFrattiniMapEquiv f hf X)
        (xiFrattiniAction T X h.invariant) (xiFrattiniAction (T.map f) (X.map f) hn)
        (xiFrattiniMapEquiv_equivariant f hf T X h.invariant hn) h.irreducible

/-- The members of Ξ contained in an overgroup, represented in the ambient group. -/
def XiIn (H T : Subgroup G) : Set (Subgroup G) := {X | X ≤ H ∧ X ∈ Xi G T}

/-- The intrinsic star family of an overgroup. The excluded local components
are taken inside that overgroup, not in the whole ambient group. -/
def XiStarIn (H T : Subgroup G) : Set (Subgroup G) :=
  {X | X ∈ XiIn H T ∧ ∀ L₀ ∈ LIn H T,
    Theory.GroupTheory.IsQuasisimple (L₀ ⧸ pCore 2 L₀) → ¬ X ⊔ T ≤ L₀ ⊔ T}

/-- Ambient and intrinsic membership in Ξ agree under subgroup restriction. -/
theorem mem_XiIn_iff_subgroupOf {H T X : Subgroup G} (hTH : T ≤ H) (hXH : X ≤ H) :
    X ∈ XiIn H T ↔ X.subgroupOf H ∈ Xi H (T.subgroupOf H) := by
  rw [← mem_Xi_map_iff H.subtype H.subtype_injective,
    map_subgroupOf_eq_of_le hTH, map_subgroupOf_eq_of_le hXH]
  exact and_iff_right hXH

private theorem quasisimple_two_quotient_iff {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) : Theory.GroupTheory.IsQuasisimple (A ⧸ pCore 2 A) ↔
      Theory.GroupTheory.IsQuasisimple (B ⧸ pCore 2 B) := by
  let q := QuotientGroup.congr (pCore 2 A) (pCore 2 B) e (pCore_map_iso 2 e)
  constructor
  · intro h
    let _ := h
    exact Theory.GroupTheory.IsQuasisimple.of_mulEquiv q
  · intro h
    let _ := h
    exact Theory.GroupTheory.IsQuasisimple.of_mulEquiv q.symm

/-- The local star condition transports with its genuine local-component family. -/
theorem mem_XiStarIn_iff_subgroupOf {H T X : Subgroup G} (hTH : T ≤ H) (hXH : X ≤ H) :
    X ∈ XiStarIn H T ↔ X.subgroupOf H ∈ XiStar H (T.subgroupOf H) := by
  constructor
  · rintro ⟨hX, hstar⟩
    refine ⟨(mem_XiIn_iff_subgroupOf hTH hXH).mp hX, ?_⟩
    intro D hD hQ hle
    have hDm : D.map H.subtype ∈ LIn H T := by
      refine ⟨map_subtype_le D, ?_⟩
      simpa only [map_subgroupOf_eq_of_le hTH] using
        (mem_L_map_iff H.subtype H.subtype_injective).mpr hD
    apply hstar (D.map H.subtype) hDm
      ((quasisimple_two_quotient_iff (D.equivMapOfInjective H.subtype H.subtype_injective)).mp hQ)
    simpa only [Subgroup.map_sup, map_subgroupOf_eq_of_le hTH,
      map_subgroupOf_eq_of_le hXH] using map_mono (f := H.subtype) hle
  · rintro ⟨hX, hstar⟩
    refine ⟨(mem_XiIn_iff_subgroupOf hTH hXH).mpr hX, ?_⟩
    intro D hD hQ hle
    apply hstar (D.subgroupOf H) ((mem_LIn_iff_subgroupOf hTH hD.1).mp hD)
      ((quasisimple_two_quotient_iff (subgroupOfEquivOfLe hD.1)).mpr hQ)
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    simpa only [Subgroup.map_sup, map_subgroupOf_eq_of_le hTH,
      map_subgroupOf_eq_of_le hXH, map_subgroupOf_eq_of_le hD.1] using hle

/-- Global star membership restricts to any overgroup containing X and T. -/
theorem mem_XiStarIn_of_mem_XiStar {H T X : Subgroup G} (hX : X ∈ XiStar G T)
    (hXH : X ≤ H) : X ∈ XiStarIn H T :=
  ⟨⟨hXH, hX.1⟩, fun D hD => hX.2 D hD.2⟩

/-- The residual condition in the ambient subgroup lattice. -/
theorem XiMember.pResidual_eq {T X : Subgroup G} (hX : XiMember T X) :
    (pResidual 2 X).map X.subtype = X := by
  rw [(pResidual_eq_top_iff 2 X).mpr hX.perfect, ← MonoidHom.range_eq_map, range_subtype]

/-- The literal product factorization X = O₂(X)P of Lemma 1.3.2(1). -/
theorem XiMember.sylow_mul [Finite G] {T X : Subgroup G}
    (hX : XiMember T X) {p : ℕ} [Fact p.Prime]
    (hq : XiOddQuotient p (XiQuotient X)) (P : Sylow p X) :
    (X.pCoreIn 2 : Set G) * ((P : Subgroup X).map X.subtype : Set G) = X := by
  have hn : (P : Subgroup X).map X.subtype ≤ normalizer (X.pCoreIn 2 : Set G) :=
    (map_subtype_le _).trans (X.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
  rw [← coe_mul_of_right_le_normalizer_left _ _ hn, hX.sylow_sup hq P]

/-- The literal product factorization T = O₂(X)N_T(P) of Lemma 1.3.2(3). -/
theorem XiMember.normalizer_mul [Finite G] {T X : Subgroup G}
    (hX : XiMember T X) (hT : IsSylowIn 2 T (X ⊔ T))
    {p : ℕ} [Fact p.Prime] (hq : XiOddQuotient p (XiQuotient X)) (P : Sylow p X) :
    (X.pCoreIn 2 : Set G) *
      ((T ⊓ normalizer ((P : Subgroup X).map X.subtype : Set G) : Subgroup G) : Set G) = T := by
  have hn : T ⊓ normalizer ((P : Subgroup X).map X.subtype : Set G) ≤
      normalizer (X.pCoreIn 2 : Set G) :=
    inf_le_left.trans (hX.invariant.trans
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
  rw [← coe_mul_of_right_le_normalizer_left _ _ hn, ← hX.normalizer_factor hT hq P]

end CFSG.Quasithin.Chapter1
