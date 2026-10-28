module

public import CFSG.Quasithin.ChapterE.Section01.Basic
public import Theory.GroupAction.HyperplaneCommutatorLocal
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Hyperplane factors on the quotient side of E.1.10(6)

For a normal odd-prime subgroup X=[X,A], the hyperplane commutator factors
generate X. Each nontrivial factor D, joined with the actual τ(G,T,A),
is an E₁-member. The generic local calculation supplies all of E1, including
the intrinsic two-core quotient and rank one. Coprime factor orders make
tau Sylow in D tau; maximality identifies the source intersection T ∩ D tau.
Discarding trivial factors gives X ≤ ⟨E₁(G,T,A)⟩.

The final theorem applies this to the literal images in G/Y, transporting
X/Y through the subgroup quotient-range isomorphism. It supplies the
quotient-side generation step of E.1.10(6). Transporting these E-members
back upstairs is the separate E.1.10(7) obligation of QuotientLifting.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
Lemma E.1.10(6) and its proof, printed pp.211--212.
-/

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]

/-- A nontrivial hyperplane factor joined with the literal tau is an E1 member. -/
public theorem hyperplane_tau_isEMemberAt
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (T : Sylow 2 G) (X A : Subgroup G) [X.Normal] (hX : IsPGroup p X)
    [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    (B : Subgroup A) (hB : B.index = 2)
    (hne : ⁅X ⊓ centralizer (B.map A.subtype : Set G), A⁆ ≠ ⊥) :
    IsEMemberAt 1 (T : Subgroup G) A
      (⁅X ⊓ centralizer (B.map A.subtype : Set G), A⁆ ⊔ tau (T : Subgroup G) A) := by
  let D := ⁅X ⊓ centralizer (B.map A.subtype : Set G), A⁆
  let R := tau (T : Subgroup G) A
  let K := D ⊔ R
  have hsup := sup_pCore_le_tau T A hAT
  have hAR : A ≤ R := le_sup_left.trans hsup
  have hNR : pCore 2 G ≤ R := le_sup_right.trans hsup
  have hRT : R ≤ (T : Subgroup G) := tau_le _ _
  have hR : IsPGroup 2 R := T.isPGroup'.to_le hRT
  have hcomm : ⁅A,R⁆ ≤ pCore 2 G := by
    apply commutator_le.mpr
    intro a ha r hr
    exact (mem_centralizerModulo_iff.mp hr).2 a ha
  obtain ⟨hRD, -, hquot, hncore, hc, hrank⟩ :=
    hyperplane_commutator_local_odd_data hp X A R hX hR hAR hNR hcomm B hB hne
  have hDX : D ≤ X := (commutator_mono inf_le_left le_rfl).trans (commutator_le_left X A)
  have hD : IsPGroup p D := hX.to_le hDX
  have hdisj : Disjoint D R := IsPGroup.disjoint_of_ne p 2 hp D R hD hR
  have hcard : Nat.card K = Nat.card D * Nat.card R := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes D R hRD
    simpa only [hdisj.eq_bot, card_bot, one_mul] using hh.symm
  have hRcard : Nat.card (R.subgroupOf K) = Nat.card R :=
    Nat.card_congr (subgroupOfEquivOfLe (show R ≤ K from le_sup_right)).toEquiv
  have hindex : (R.subgroupOf K).index = Nat.card D := by
    have hh := (R.subgroupOf K).card_mul_index
    rw [hRcard, hcard] at hh
    have hpos : 0 < Nat.card R := Nat.card_pos
    nlinarith
  have hDodd : ¬ 2 ∣ Nat.card D := by
    obtain ⟨n, hn⟩ := hD.exists_card_eq
    rw [hn]
    exact Nat.prime_two.coprime_iff_not_dvd.mp
      (((Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).mpr hp.symm).pow_right n)
  let S : Sylow 2 K := hR.comap_subtype.toSylow (by change ¬ 2 ∣ (R.subgroupOf K).index; rwa [hindex])
  have hTS : T.subgroupOf K = (S : Subgroup K) :=
    S.is_maximal' T.isPGroup'.comap_subtype (by intro x hx; exact hRT hx)
  have ho : ECaseOdd A K :=
    ⟨p, Fact.out, (Fact.out : p.Prime).odd_of_ne_two hp, hquot, hncore, hc, hrank⟩
  refine ⟨⟨inferInstance, hAT, hAR.trans le_sup_right, ?_, ⟨S, hTS.symm⟩, Or.inl ho⟩,
    Or.inl ⟨ho, hrank.le⟩⟩
  exact le_inf hRT le_sup_right

/-- The odd normal subgroup in the quotient-side proof of E.1.10(6) lies in E1. -/
public theorem odd_normal_le_eSubgroup_one
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (T : Sylow 2 G) (X A : Subgroup G) [X.Normal] (hX : IsPGroup p X)
    [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    (hcomm : X = ⁅X,A⁆) : X ≤ eSubgroup 1 (T : Subgroup G) A := by
  rw [eq_iSup_hyperplane_centralizer_commutator hp X A hX
    (by rw [normalizer_eq_top]; exact le_top) hcomm]
  apply iSup₂_le
  intro B hB
  by_cases he : ⁅X ⊓ centralizer (B.map A.subtype : Set G), A⁆ = ⊥
  · rw [he]; exact bot_le
  · exact le_sup_left.trans (le_sSup (hyperplane_tau_isEMemberAt hp T X A hX hAT B hB he))

/-- The literal quotient-map application; lifting E1 members upstairs is E.1.10(7). -/
public theorem quotient_odd_normal_le_eSubgroup_one
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (T : Sylow 2 G) (X Y A : Subgroup G) [X.Normal] [Y.Normal]
    (_hYX : Y ≤ X) (hX : IsPGroup p (X ⧸ Y.subgroupOf X))
    [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    (hcomm : X.map (QuotientGroup.mk' Y) =
      ⁅X.map (QuotientGroup.mk' Y), A.map (QuotientGroup.mk' Y)⁆) :
    X.map (QuotientGroup.mk' Y) ≤
      eSubgroup 1 ((T : Subgroup G).map (QuotientGroup.mk' Y))
        (A.map (QuotientGroup.mk' Y)) := by
  let q := QuotientGroup.mk' Y
  let _ : (X.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective Y)
  let _ : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map q
  exact odd_normal_le_eSubgroup_one hp
    (T.mapSurjective (f := q) (QuotientGroup.mk'_surjective Y)) (X.map q) (A.map q)
    (hX.of_equiv (quotientSubgroupRangeEquiv X Y)) (map_mono hAT) hcomm

end CFSG.Quasithin.ChapterE
