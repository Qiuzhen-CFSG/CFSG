module
public import Glauberman.Signalizer.PermutableProduct
public import Theory.GroupTheory.Signalizer.LocalCompleteness
public import Theory.GroupTheory.Signalizer.PrimeSupport
public import Theory.GroupTheory.Signalizer.LocalQPrimeFactorization
public import FeitThompson.GroupAction.NoncyclicAbelianPGroup
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Completeness from value core factorizations

Let theta be locally complete for a finite elementary binary actor of order
at least eight. Suppose Q is a nontrivial prime signalizer subgroup and
L is the actual generated subgroup inside its normalizer. If every value
C_a is the join of its mapped q-prime core and C_a intersect L, then theta
is complete. Q need not be abelian, and the supplied action is retained.

The completed q-prime subfamily generates K. For each actor subgroup B with
cyclic quotient, B has order at least four. Let T_B be the actual supremum
of the q-prime cores indexed by nonidentity actors in B. The binary fixed
factorization theorem gives the ordered product K=T_B(K intersect L).
Both the B-fixed subgroup of Q and the B-fixed subgroup of L normalize
T_B, since they lie in every indexed value. Coprime fixed generation of Q
then gives QK=KQ, so their join is an odd solvable signalizer subgroup by
the proved permutable-product theorem.

Set R=[Q,K] joined with Q. It is invariant, nontrivial, and contained in
that signalizer subgroup. Elementary commutator identities show that K
normalizes R and that R=[Q,T_B] joined with Q for every B. Consequently each
B-fixed subgroup of L normalizes R. Full coprime fixed generation of L
places L in its normalizer as well. Local completeness inside N(R), together
with the original value factorizations, now contains every family value.
Downward closure gives completeness of their actual generated subgroup.

Source: Kurzweil–Stellmacher, *The Theory of Finite Groups*, Lemma 11.2.7,
steps (3)–(6), printed pp.322–323. We use all cyclic-quotient actor subgroups;
the printed restriction to those with nontrivial C_Q(B) does not justify
generation of L (independent sign actions on C3 times C5 give a counterexample).
No step above requires that restriction. Adjoining Q throughout also removes
the source's unnecessary abelianness assumption from this reduction.
-/

open scoped Pointwise IsMulCommutative commutatorElement

namespace Glauberman

private theorem normalizes_commutator_sup {G : Type*} [Group G] (Q X : Subgroup G) :
    X ≤ Subgroup.normalizer ((⁅Q, X⁆ ⊔ Q : Subgroup G) : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro x hx g hg
  let f : G →* G := MulAut.conj x
  have hC : (⁅Q, X⁆ : Subgroup G).map f ≤ ⁅Q, X⁆ :=
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.normalizer_commutator_ge_right Q X hx)).le
  have hQ : Q.map f ≤ ⁅Q, X⁆ ⊔ Q := by
    rintro y ⟨q, hq, rfl⟩
    have hc : ⁅x, q⁆ ∈ ⁅Q, X⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hx hq
    change x * q * x⁻¹ ∈ ⁅Q, X⁆ ⊔ Q
    have hh := Subgroup.mul_mem_sup hc hq
    simpa only [f, MulAut.conj_apply, commutatorElement_def, mul_assoc,
      inv_mul_cancel, mul_one] using hh
  have hm : (⁅Q, X⁆ ⊔ Q : Subgroup G).map f ≤ ⁅Q, X⁆ ⊔ Q := by
    rw [Subgroup.map_sup]
    exact sup_le (hC.trans le_sup_left) hQ
  exact hm (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)

private theorem commutator_sup_eq_of_product
    {G : Type*} [Group G] (Q K X Y : Subgroup G)
    (hXK : X ≤ K) (hprod : (K : Set G) = (X : Set G) * (Y : Set G))
    (hY : Y ≤ Subgroup.normalizer (Q : Set G)) :
    ⁅Q, K⁆ ⊔ Q = ⁅Q, X⁆ ⊔ Q := by
  apply le_antisymm
  · apply sup_le ?_ le_sup_right
    apply Subgroup.commutator_le.mpr
    intro q hq k hk
    have hk' : k ∈ (X : Set G) * (Y : Set G) := hprod ▸ hk
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hk'
    have hqy : ⁅q, y⁆ ∈ Q :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp hY
        (Subgroup.commutator_mem_commutator hq hy)
    have hn := Subgroup.le_normalizer_iff.mp (normalizes_commutator_sup Q X) x hx
      ⁅q, y⁆ ((show Q ≤ ⁅Q, X⁆ ⊔ Q from le_sup_right) hqy)
    have hh := (⁅Q, X⁆ ⊔ Q : Subgroup G).mul_mem
      ((show ⁅Q, X⁆ ≤ ⁅Q, X⁆ ⊔ Q from le_sup_left)
        (Subgroup.commutator_mem_commutator hq hx)) hn
    simpa only [commutatorElement_mul_right_eq_mul_conj, mul_assoc] using hh
  · exact sup_le_sup (Subgroup.commutator_mono le_rfl hXK) le_rfl

private theorem cyclicQuotient_card_ge_four
    {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (hA : 8 ≤ Nat.card A) (B : Subgroup A) (hB : IsCyclic (A ⧸ B)) :
    4 ≤ Nat.card B := by
  have hdiv : Nat.card (A ⧸ B) ∣ 2 := by
    rw [← hB.exponent_eq_card]
    exact (Group.exponent_quotient_dvd B).trans (IsElementaryAbelian.exponent_dvd_p 2 A)
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hdiv
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup B
  nlinarith

private theorem fixed_cyclicQuotient_iSup
    {A G : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    [Group G] [Finite G] [MulDistribMulAction A G]
    (hA : 8 ≤ Nat.card A) (U : Subgroup G) [IsInvariant A G U]
    (hodd : Odd (Nat.card U)) :
    (⨆ B : {B : Subgroup A // IsCyclic (A ⧸ B)},
      U ⊓ FixedPoints.subgroup B.val G) = U := by
  have hncyc : ¬ IsCyclic A := by
    intro hc
    have hdiv : Nat.card A ∣ 2 := by
      rw [← hc.exponent_eq_card]
      exact IsElementaryAbelian.exponent_dvd_p 2 A
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hdiv
    omega
  let _ : Fact (IsPGroup 2 A) := ⟨IsElementaryAbelian.isPGroup 2 A⟩
  have hgen := iSup_fixedPointSubgroup_cyclicQuot_eq_top_of_noncyclic_abelian_pGroup_action
    (G := U) (A := A) 2 hodd.coprime_two_left hncyc
  have hfixed (B : Subgroup A) :
      (FixedPoints.subgroup B U).map U.subtype = U ⊓ FixedPoints.subgroup B G := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, fun b => congrArg Subtype.val (hy b)⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, fun b => Subtype.ext (hx.2 b), rfl⟩
  have hm := congrArg (fun V : Subgroup U => V.map U.subtype) hgen
  simpa only [Subgroup.map_iSup, hfixed, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    iSup_subtype] using hm

private theorem permutable_of_generated_local_products
    {G : Type*} [Group G] {I : Type*} (Q K L : Subgroup G)
    (F T : I → Subgroup G) (hFQ : ∀ i, F i ≤ Q)
    (hgen : iSup F = Q) (hTK : ∀ i, T i ≤ K)
    (hFN : ∀ i, F i ≤ Subgroup.normalizer (T i : Set G))
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hprod : ∀ i, (K : Set G) = (T i : Set G) * ((K ⊓ L : Subgroup G) : Set G)) :
    (Q : Set G) * (K : Set G) = (K : Set G) * (Q : Set G) := by
  have hleft : (Q : Set G) * (K : Set G) ⊆ (K : Set G) * (Q : Set G) := by
    rintro z ⟨q, hq, k, hk, rfl⟩
    have hq' : q ∈ iSup F := hgen.symm ▸ hq
    have hp : ∀ k ∈ K, q * k ∈ (K : Set G) * (Q : Set G) := by
      refine Subgroup.iSup_induction F (C := fun q =>
        ∀ k ∈ K, q * k ∈ (K : Set G) * (Q : Set G)) hq' ?_ ?_ ?_
      · intro i q hq k hk
        have hk' : k ∈ (T i : Set G) * ((K ⊓ L : Subgroup G) : Set G) := hprod i ▸ hk
        obtain ⟨t, ht, l, hl, rfl⟩ := Set.mem_mul.mp hk'
        have ht' : q * t * q⁻¹ ∈ T i := Subgroup.le_normalizer_iff.mp (hFN i) q hq t ht
        have hq' : l⁻¹ * q * (l⁻¹)⁻¹ ∈ Q :=
          Subgroup.le_normalizer_iff.mp hLQ l⁻¹ (L.inv_mem hl.2) q (hFQ i hq)
        refine Set.mem_mul.mpr ⟨(q * t * q⁻¹) * l,
          K.mul_mem (hTK i ht') hl.1, l⁻¹ * q * (l⁻¹)⁻¹, hq', ?_⟩
        group
      · intro k hk
        exact Set.mem_mul.mpr ⟨k, hk, 1, Q.one_mem, by simp⟩
      · intro x y hx hy k hk
        obtain ⟨k₁, hk₁, q₁, hq₁, heq₁⟩ := Set.mem_mul.mp (hy k hk)
        obtain ⟨k₂, hk₂, q₂, hq₂, heq₂⟩ := Set.mem_mul.mp (hx k₁ hk₁)
        refine Set.mem_mul.mpr ⟨k₂, hk₂, q₂ * q₁, Q.mul_mem hq₂ hq₁, ?_⟩
        calc
          k₂ * (q₂ * q₁) = (k₂ * q₂) * q₁ := (mul_assoc _ _ _).symm
          _ = (x * k₁) * q₁ := by rw [heq₂]
          _ = x * (y * k) := by rw [mul_assoc, heq₁]
          _ = (x * y) * k := (mul_assoc _ _ _).symm
    exact hp k hk
  apply Set.Subset.antisymm hleft
  have hi := Set.inv_subset_inv.mpr hleft
  simpa only [mul_inv_rev, inv_coe_set] using hi

private theorem normalizes_commutator_of_normalizes
    {G : Type*} [Group G] (V Q X : Subgroup G)
    (hQ : V ≤ Subgroup.normalizer (Q : Set G))
    (hX : V ≤ Subgroup.normalizer (X : Set G)) :
    V ≤ Subgroup.normalizer ((⁅Q, X⁆ : Subgroup G) : Set G) := by
  intro v hv
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  rw [Subgroup.map_commutator, Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQ hv),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hX hv)]

open Theory.GroupTheory Theory.GroupTheory.TwoSignalizerFamily

private theorem complete_of_fixed_local_products
    {A G : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    [Group G] [Finite G] [MulDistribMulAction A G]
    (θ : TwoSignalizerFamily A G) (hA : 8 ≤ Nat.card A) (hl : θ.IsLocallyComplete)
    (Q K L : Subgroup G) (hQ : θ.IsSignalizerSubgroup Q) (hQn : Q ≠ ⊥)
    (hK : θ.IsSignalizerSubgroup K) (hL : θ.IsSignalizerSubgroup L)
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (T : {B : Subgroup A // IsCyclic (A ⧸ B)} → Subgroup G)
    (hTK : ∀ B, T B ≤ K)
    (hQN : ∀ B, Q ⊓ FixedPoints.subgroup B.val G ≤ Subgroup.normalizer (T B : Set G))
    (hLN : ∀ B, L ⊓ FixedPoints.subgroup B.val G ≤ Subgroup.normalizer (T B : Set G))
    (hprod : ∀ B, (K : Set G) = (T B : Set G) * ((K ⊓ L : Subgroup G) : Set G))
    (hcover : θ.closure ≤ K ⊔ L) : θ.IsComplete := by
  let _ := hQ.2.2.1
  let _ := hK.2.2.1
  let _ := hL.2.2.1
  have hgenQ := fixed_cyclicQuotient_iSup hA Q hQ.1
  have hperm := permutable_of_generated_local_products Q K L
    (fun B : {B : Subgroup A // IsCyclic (A ⧸ B)} => Q ⊓ FixedPoints.subgroup B.val G)
    T (fun _ => inf_le_left) hgenQ hTK hQN hLQ hprod
  have hG0 : θ.IsSignalizerSubgroup (Q ⊔ K) := hQ.sup_of_permutable hK hperm
  let R : Subgroup G := ⁅Q, K⁆ ⊔ Q
  have hRle : R ≤ Q ⊔ K := sup_le (Subgroup.commutator_le_sup Q K) le_sup_left
  let _ := isInvariant_commutator (A := A) Q K
  let hRI : IsInvariant A G R := isInvariant_sup ⁅Q, K⁆ Q
  let _ := hRI
  have hR : θ.IsSignalizerSubgroup R := hG0.mono hRle hRI
  have hRn : R ≠ ⊥ := by
    intro heq
    apply hQn
    exact bot_unique (heq ▸ (show Q ≤ R from le_sup_right))
  have hKN : K ≤ Subgroup.normalizer (R : Set G) := normalizes_commutator_sup Q K
  have hLN' : L ≤ Subgroup.normalizer (R : Set G) := by
    rw [← fixed_cyclicQuotient_iSup hA L hL.1]
    apply iSup_le
    intro B
    change L ⊓ FixedPoints.subgroup B.val G ≤ Subgroup.normalizer (R : Set G)
    dsimp only [R]
    rw [commutator_sup_eq_of_product Q K (T B) (K ⊓ L) (hTK B) (hprod B)
      (inf_le_right.trans hLQ)]
    have hfixQ : L ⊓ FixedPoints.subgroup B.val G ≤ Subgroup.normalizer (Q : Set G) :=
      inf_le_left.trans hLQ
    exact (le_inf (normalizes_commutator_of_normalizes _ Q (T B) hfixQ (hLN B)) hfixQ).trans
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup ⁅Q, T B⁆ Q)
  let _ := isInvariant_normalizer (A := A) R
  have hlocal : θ.IsSignalizerSubgroup (θ.closureWithin (Subgroup.normalizer (R : Set G))) :=
    hl.normalizer R hR hRn
  have hkle := hK.le_closureWithin (by omega : 4 ≤ Nat.card A) hKN
  have hlle := hL.le_closureWithin (by omega : 4 ≤ Nat.card A) hLN'
  exact hlocal.mono (hcover.trans (sup_le hkle hlle)) θ.closure_invariant

private theorem fixed_le_normalizer_local_cores
    {A G : Type*} [Group A] [Group G] [MulDistribMulAction A G]
    (θ : TwoSignalizerFamily A G) (q : ℕ) (B : Subgroup A)
    (U : Subgroup G) (hU : θ.IsSignalizerSubgroup U) :
    U ⊓ FixedPoints.subgroup B G ≤ Subgroup.normalizer
      ((⨆ (a : {a : A // a ≠ 1}) (_ : a.val ∈ B),
        (pPrimeCore q (θ.subgroup a)).map (θ.subgroup a).subtype : Subgroup G) : Set G) := by
  intro x hx
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  simp only [Subgroup.map_iSup]
  apply iSup_congr
  intro a
  apply iSup_congr
  intro ha
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mp
  apply θ.value_le_normalizer_core q a
  apply hU.2.2.2 a
  refine ⟨hx.1, ?_⟩
  intro z
  exact hx.2 ⟨z, (Subgroup.zpowers_le.mpr ha) z.property⟩

public theorem complete_of_value_core_factorizations
    {A G : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    [Group G] [Finite G] [MulDistribMulAction A G]
    (θ : TwoSignalizerFamily A G) (hA : 8 ≤ Nat.card A) (hl : θ.IsLocallyComplete)
    (q : ℕ) [Fact q.Prime] (Q : Subgroup G) (hQ : θ.IsSignalizerSubgroup Q)
    (hQp : IsPGroup q Q) (hQn : Q ≠ ⊥)
    (hvalues : ∀ a, θ.subgroup a =
      (pPrimeCore q (θ.subgroup a)).map (θ.subgroup a).subtype ⊔
        (θ.subgroup a ⊓ θ.closureWithin (Subgroup.normalizer (Q : Set G)))) :
    θ.IsComplete := by
  classical
  have hdiv : ∃ a, q ∣ Nat.card (θ.subgroup a) := by
    by_contra hn
    have hcop := hQ.coprime_of_values_coprime (by omega : 4 ≤ Nat.card A) q (fun a =>
      ((Fact.out : q.Prime).coprime_iff_not_dvd.mpr (fun ha => hn ⟨a, ha⟩)).symm)
    have hcard := hQp.card_eq_or_dvd.resolve_right
      ((Fact.out : q.Prime).coprime_iff_not_dvd.mp hcop.symm)
    exact hQn (Subgroup.card_eq_one.mp hcard)
  have hqc := hl.qPrime q hdiv
  let K := (θ.qPrime q).closure
  let L := θ.closureWithin (Subgroup.normalizer (Q : Set G))
  have hK : θ.IsSignalizerSubgroup K := IsSignalizerSubgroup.of_qPrime q hqc
  have hL : θ.IsSignalizerSubgroup L := hl.normalizer Q hQ hQn
  let T : {B : Subgroup A // IsCyclic (A ⧸ B)} → Subgroup G := fun B =>
    ⨆ (a : {a : A // a ≠ 1}) (_ : a.val ∈ B.val),
      (pPrimeCore q (θ.subgroup a)).map (θ.subgroup a).subtype
  have hcoreK (a : {a : A // a ≠ 1}) :
      (pPrimeCore q (θ.subgroup a)).map (θ.subgroup a).subtype ≤ K :=
    (θ.core_le_qPrime_subgroup q a).trans ((θ.qPrime q).le_closure a)
  apply complete_of_fixed_local_products θ hA hl Q K L hQ hQn hK hL
    (θ.closureWithin_le _) T
  · intro B
    exact iSup₂_le fun a _ => hcoreK a
  · intro B
    exact fixed_le_normalizer_local_cores θ q B.val Q hQ
  · intro B
    exact fixed_le_normalizer_local_cores θ q B.val L hL
  · intro B
    exact θ.qPrime_closure_set_mul_eq q L hL hqc B.val
      (cyclicQuotient_card_ge_four hA B.val B.property) (fun a _ => hvalues a)
  · apply θ.closure_le.mpr
    intro a
    rw [hvalues a]
    exact sup_le ((hcoreK a).trans le_sup_left) (inf_le_right.trans le_sup_right)

end Glauberman
