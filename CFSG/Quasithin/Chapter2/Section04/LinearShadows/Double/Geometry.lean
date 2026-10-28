module

public import CFSG.Quasithin.Chapter2.Section04.CoreNormalizers
public import Stellmacher.ElementaryAbelianMaxJ
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Mathlib.GroupTheory.Nilpotent
public import Theory.GroupTheory.PrimeRankHom
public import Theory.ElementaryAbelian.Quotient
public import Stellmacher.ElementaryAbelianMaxOrder
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# Normalizer deductions in the two-block shadow

The outside element normalizing a normal subgroup contradicts the literal
normalizer equality 2.4.4. This eliminates the torus fixed subgroup before
proving directness. A maximum elementary subgroup outside S has order at
most 2^(2n+3), contrary to the actual witness of order 2^(4n). Thus the
Thompson subgroup does not grow. Its normalizer controls the larger 2-group.

In the larger-normalizer alternative, construct the local pairs for N and
H₁ = ⟨S₂,L₂⟩. The Γₑ₀ maximality theorem keeps the original Sylow image;
2.3.7(2) then contradicts the larger subgroup in N_T(R₁).

Source: Aschbacher–Smith, §2.4, printed pp.540–541. The preceding block,
fixed-space and four-member permutation calculations remain explicit inputs.
-/

public section

open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2.LinearDouble
variable {G : Type*} [Group G] [Finite G]
/-- The actual 2.4.4 normalizer equality eliminates the invariant fixed subgroup. -/
theorem centralizer_eq_bot_of_outside_normalizer {M H U L : Subgroup G}
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hpair : (U,L) ∈ localPairsIn (Chapter1.He G) M H)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (T : Sylow 2 G) (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (R D : Subgroup G) (hRS : R ≤ (S : Subgroup H).map H.subtype)
    (hn : ((R ⊓ centralizer (D : Set G)).subgroupOf H).Normal)
    (x : G) (hxT : x ∈ (T : Subgroup G))
    (hxS : x ∉ (S : Subgroup H).map H.subtype)
    (hxR : x ∈ normalizer (R : Set G)) (hxD : x ∈ normalizer (D : Set G)) :
    R ⊓ centralizer (D : Set G) = ⊥ := by
  by_contra hne
  have he := lemma_2_4_4 hH hpair S hUS T hST _ hne (inf_le_left.trans hRS) hn
  have hxC := normalizer_le_normalizer_centralizer D hxD
  have hxN := inf_normalizer_le_normalizer_inf ⟨hxR, hxC⟩
  exact hxS (he ▸ (show x ∈ (T : Subgroup G) ⊓
    normalizer ((R ⊓ centralizer (D : Set G) : Subgroup G) : Set G) from ⟨hxT,hxN⟩))

/-- The p-group normalizer condition makes a self-normalizing Thompson normalizer Sylow. -/
theorem sylow_eq_of_thompson_self_normalizer (T : Sylow 2 G) (P R : Subgroup G)
    (hPT : P ≤ (T : Subgroup G)) (hR : R = elementaryAbelianMaxJ P)
    (hN : (T : Subgroup G) ⊓ normalizer (R : Set G) = P) : P = (T : Subgroup G) := by
  have ht : normalizer (P : Set G) ≤ normalizer (R : Set G) := by
    rw [hR]
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq] at hx ⊢
    change P.map (MulAut.conj x).toMonoidHom = P at hx
    change (elementaryAbelianMaxJ P).map (MulAut.conj x).toMonoidHom = _
    rw [← elementaryAbelianMaxJ_map_equiv (MulAut.conj x) P, hx]
  have he : normalizer (P.subgroupOf (T : Subgroup G) : Set (T : Subgroup G)) =
      P.subgroupOf (T : Subgroup G) := by
    apply le_antisymm _ le_normalizer
    rw [← subgroupOf_normalizer_eq hPT]
    intro x hx
    exact hN ▸ (show (x : G) ∈ (T : Subgroup G) ⊓ normalizer (R : Set G) from
      ⟨x.property, ht hx⟩)
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  have hfull := normalizerCondition_iff_only_full_group_self_normalizing.mp
    (Group.normalizerCondition_of_isNilpotent (G := (T : Subgroup G))) _ he
  exact le_antisymm hPT (subgroupOf_eq_top.mp hfull)
end CFSG.Quasithin.Chapter2.LinearDouble

open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2.LinearDouble
variable {G : Type*} [Group G] [Finite G]
/-- The source rank inequality excludes every maximum elementary subgroup outside S. -/
theorem thompson_eq_of_rank_bounds (P S R : Subgroup G) (hSP : S ≤ P)
    [(R.subgroupOf P).Normal] {n : ℕ} (hn : 2 ≤ n)
    (hquot : primeRank 2 (P ⧸ R.subgroupOf P) ≤ 3)
    (hfix : ∀ a ∈ P, a ∉ S → a ^ 2 = 1 →
      primeRank 2 (R ⊓ centralizer ({a} : Set G) : Subgroup G) ≤ 2 * n)
    (E : Subgroup G) (hES : E ≤ S) (hE : IsElementaryAbelian 2 E)
    (hEc : Nat.card E = 2 ^ (4 * n)) :
    elementaryAbelianMaxJ P = elementaryAbelianMaxJ S := by
  have hJS : elementaryAbelianMaxJ P ≤ S := by
    apply sSup_le
    intro A hA
    by_contra hAS
    obtain ⟨a, haA, haS⟩ := Set.not_subset.mp hAS
    let := hA.2.1
    let : CommGroup A := IsMulCommutative.instCommGroup
    have ha2 : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (A := A) a haA
    let f : A →* (P ⧸ R.subgroupOf P) :=
      (QuotientGroup.mk' (R.subgroupOf P)).comp (inclusion hA.1)
    have hk : primeRank 2 f.ker ≤ 2 * n := by
      let j : f.ker →* (R ⊓ centralizer ({a} : Set G) : Subgroup G) :=
        { toFun := fun y => ⟨y.val.val, by
            have hy : (⟨y.val.val, hA.1 y.val.property⟩ : P) ∈ R.subgroupOf P :=
              (QuotientGroup.eq_one_iff _).mp y.property
            refine ⟨hy, mem_centralizer_singleton_iff.mpr ?_⟩
            exact congrArg Subtype.val (mul_comm y.val (⟨a,haA⟩ : A))⟩
          map_one' := rfl
          map_mul' _ _ := rfl }
      have hj : Function.Injective j := by
        intro x y he
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : (R ⊓ centralizer ({a} : Set G) : Subgroup G) => (z : G)) he
      exact (Theory.GroupTheory.primeRank_le_of_injective 2 j hj).trans
        (hfix a (hA.1 haA) haS ha2)
    have hr : primeRank 2 A ≤ 2 * n + 3 :=
      (Theory.GroupTheory.primeRank_le_ker_add f).trans (Nat.add_le_add hk hquot)
    have hc : Nat.card A ≤ 2 ^ (2 * n + 3) := by
      have hh := (primeRank_le_iff_elementary_card_le A).mp hr (⊤ : Subgroup A)
        (IsElementaryAbelian.of_surjective
          (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A).symm.toMonoidHom
          (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A).symm.surjective)
      simpa only [Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A).toEquiv] using hh
    have hlarge : 2 ^ (4 * n) ≤ Nat.card A := hEc ▸ hA.2.2 E (hES.trans hSP) hE
    have hpow := hlarge.trans hc
    have hi := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hpow
    omega
  have h₁ := elementaryAbelianMaxOrder_le_and_j_le_of_eq S P hSP
  have h₂ := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le P S hJS
  have he := le_antisymm h₁.1 h₂.1
  exact le_antisymm (h₂.2 he.symm) (h₁.2 he)
end CFSG.Quasithin.Chapter2.LinearDouble

open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearDouble
variable {G : Type*} [Group G] [Finite G]
/-- The larger-normalizer case contradicts the actual Γ maximality and Sylow transport. -/
theorem false_of_larger_normalizer {M H : Subgroup G} (hH : H ∈ gammaEvenZero (Chapter1.He G) M)
    (N S₂ L₂ R₁ : Subgroup G) (T : Sylow 2 G)
    (hN : N ∈ Chapter1.He G) (hNcore : twoCore N ≠ ⊥)
    (hS₂ : S₂ ∈ beta M) (hSN : S₂ ≤ N) (hLN : L₂ ≤ N) (hout : ¬ L₂ ≤ M)
    (hcard : Nat.card S₂ = twoPart H)
    (hRN : S₂ ⊔ L₂ ≤ normalizer (R₁ : Set G))
    (hR : IsPGroup 2 R₁) (hRne : R₁ ≠ ⊥)
    (hST : S₂ ≤ (T : Subgroup G))
    (hlarge : Nat.card S₂ < Nat.card ((T : Subgroup G) ⊓ normalizer (R₁ : Set G) : Subgroup G)) : False := by
  have hp : (S₂,N) ∈ localPairsIn (Chapter1.He G) M N :=
    ⟨⟨hS₂,hN,hNcore,hSN,fun h => hout (hLN.trans h)⟩,le_rfl⟩
  have hNg := localPair_snd_mem_gamma hp.1
  have hb := beta_card_le_twoPart hS₂ hSN
  rw [hcard] at hb
  obtain ⟨hc,_⟩ := lemma_2_4_3_2 hH ⟨hNg,hN⟩ hb
  obtain ⟨P,hP⟩ := exists_sylow_of_card hSN (hcard.trans hc.symm)
  let H₁ := S₂ ⊔ L₂
  have hH₁N : H₁ ≤ N := sup_le hSN hLN
  have hQN : twoCore N ≤ H₁ :=
    (pCoreIn_le_sylow N P).trans (hP.le.trans le_sup_left)
  have hH₁ne : H₁ ≠ ⊥ := fun he => hS₂.1.1 (bot_unique (he ▸ le_sup_left))
  have hH₁e : H₁ ∈ Chapter1.He G :=
    Chapter1.lemma_1_1_4_4 hH₁ne hH₁N hN (inf_le_left.trans hQN)
  have hQH : twoCore N ≤ twoCore H₁ :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 N) hQN
      (hH₁N.trans (le_normalizer_twoCore N))
  have hH₁core : twoCore H₁ ≠ ⊥ := fun he => hNcore (bot_unique (he ▸ hQH))
  have hp₁ : (S₂,H₁) ∈ localPairsIn (Chapter1.He G) M H₁ :=
    ⟨⟨hS₂,hH₁e,hH₁core,le_sup_left,fun hm => hout (le_sup_right.trans hm)⟩,le_rfl⟩
  have hb₁ := beta_card_le_twoPart hS₂ (show S₂ ≤ H₁ from le_sup_left)
  rw [hcard] at hb₁
  obtain ⟨hc₁,hH₁z⟩ := lemma_2_4_3_2 hH ⟨localPair_snd_mem_gamma hp₁.1,hH₁e⟩ hb₁
  obtain ⟨P₁,hP₁⟩ := exists_sylow_of_card (show S₂ ≤ H₁ from le_sup_left)
    (hcard.trans hc₁.symm)
  have hQ : R₁ ≤ twoCore (normalizer (R₁ : Set G)) :=
    le_pCoreIn_of_normalizes hR R₁.le_normalizer le_rfl
  have hQne : twoCore (normalizer (R₁ : Set G)) ≠ ⊥ :=
    fun he => hRne (bot_unique (he ▸ hQ))
  obtain ⟨P₂,hP₂⟩ := (lemma_2_3_7_2 hH₁z.1 hp₁ P₁ hP₁.ge ⟨hQne,hRN⟩).2.1
  have he := inf_eq_sylow_map P₂ T.isPGroup' (hP₂.le.trans (hP₁.le.trans hST))
  rw [hP₂,hP₁] at he
  rw [he] at hlarge
  exact Nat.lt_irrefl _ hlarge
end CFSG.Quasithin.Chapter2.LinearDouble

open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearDouble
variable {G : Type*} [Group G] [Finite G]
/-- The source generation equality proves normality of the fixed subgroup before applying 2.4.4. -/
theorem centralizer_eq_bot_of_source_generation {M H U L : Subgroup G}
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hpair : (U,L) ∈ localPairsIn (Chapter1.He G) M H)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (T : Sylow 2 G) (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (R D L₀ N : Subgroup G) (hRS : R ≤ (S : Subgroup H).map H.subtype)
    (hgen : H = L₀ ⊔ N) (hNR : N ≤ normalizer (R : Set G))
    (hND : N ≤ normalizer (D : Set G))
    (hfixed : R ⊓ centralizer (D : Set G) ≤ centralizer (L₀ : Set G))
    (x : G) (hxT : x ∈ (T : Subgroup G))
    (hxS : x ∉ (S : Subgroup H).map H.subtype)
    (hxR : x ∈ normalizer (R : Set G)) (hxD : x ∈ normalizer (D : Set G)) :
    R ⊓ centralizer (D : Set G) = ⊥ := by
  let C := R ⊓ centralizer (D : Set G)
  have hCH : C ≤ H := (inf_le_left.trans hRS).trans (map_subtype_le _)
  have hn : H ≤ normalizer (C : Set G) := by
    rw [hgen]
    apply sup_le
    · apply le_trans ?_ (centralizer_le_normalizer (C : Set G))
      exact le_centralizer_iff.mp hfixed
    · intro y hy
      exact inf_normalizer_le_normalizer_inf
        ⟨hNR hy, normalizer_le_normalizer_centralizer D (hND hy)⟩
  have hnormal : (C.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hCH).mpr hn
  by_contra hne
  have he := lemma_2_4_4 hH hpair S hUS T hST C hne (inf_le_left.trans hRS) hnormal
  have hxN := inf_normalizer_le_normalizer_inf
    ⟨hxR, normalizer_le_normalizer_centralizer D hxD⟩
  exact hxS (he ▸ (show x ∈ (T : Subgroup G) ⊓ normalizer (C : Set G) from ⟨hxT,hxN⟩))

omit [Finite G] in
/-- The product becomes direct only after its intersection is killed by the torus fixed subgroup. -/
theorem direct_product_of_trivial_fixed_group (A B R D : Subgroup G)
    (hcomm : A ≤ centralizer (B : Set G))
    (hmeet : A ⊓ B ≤ R) (hD : D ≤ A ⊔ B)
    (hC : R ⊓ centralizer (D : Set G) = ⊥) :
    ∃ e : A × B ≃* (A ⊔ B : Subgroup G),
      ∀ a b, (e (a,b) : G) = (a : G) * (b : G) := by
  have hc : A ⊔ B ≤ centralizer ((A ⊓ B : Subgroup G) : Set G) := by
    apply sup_le
    · exact hcomm.trans (centralizer_le (show (A ⊓ B : Subgroup G) ≤ B from inf_le_right))
    · exact (le_centralizer_iff.mp hcomm).trans
        (centralizer_le (show (A ⊓ B : Subgroup G) ≤ A from inf_le_left))
  have hd : Disjoint A B := by
    rw [disjoint_iff]
    apply bot_unique
    rw [← hC]
    exact le_inf hmeet (le_centralizer_iff.mp (hD.trans hc))
  exact exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hd hcomm
end CFSG.Quasithin.Chapter2.LinearDouble