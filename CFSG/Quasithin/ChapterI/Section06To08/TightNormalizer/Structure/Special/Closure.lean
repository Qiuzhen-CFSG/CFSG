module

public import CFSG.Quasithin.ChapterI.Section06To08.TightNormalizer.Structure.Special.Construction

/-!
# Index two and exhaustion of the special normal closure in I.7.7

Write `N = N_S(R)`, `B = Rʸ`, `U = N B`, and `P = S₁ B`. This module is
conditional on precisely two local-structure facts: `P` is elementary abelian,
and every elementary abelian two-subgroup of `U` lies in `N` or `P`.
The source-theorem assembly must supply these facts.

Equal cardinalities show that `N_S(U)` permutes `N` and `P`. The stabilizer
of `N` is `U`, and the two-group normalizer condition supplies an element
swapping them. This gives `|N_S(U) : U| = 2` and `N_S(P) = U`.

If the normal closure `W = ⟨Rˢ⟩` properly contains `U`, the next normalizer
in the tower supplies a conjugate `Rˢ ≤ N_S(U)` escaping `U`. Its order is
greater than two, so it meets `U` in a nonidentity involution. The local
cover puts this involution in `N` or `P`. Apply I.7.6 to `R` in the first
case, and to the transported tight setup for `B` in the second, to contradict
escape. Thus `U = W`, and normality inside `S` gives `|S : W| = 2`.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, I.7.7, printed p.428 (PDF p.439).
Conjugation is left conjugation; all normalizers and indices are relative to `S`.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]

-- Equal-sized elementary subgroups exhaust the possible images.
private theorem closure_pair_image {N P U : Subgroup G}
    [IsElementaryAbelian 2 N] [IsElementaryAbelian 2 P]
    (hNU : N ≤ U) (hPU : P ≤ U) (hcard : Nat.card N = Nat.card P)
    (hcover : ∀ A : Subgroup G, IsElementaryAbelian 2 A → A ≤ U → A ≤ N ∨ A ≤ P)
    {s : G} (hs : s ∈ normalizer (U : Set G)) :
    (conjSubgroup N s = N ∨ conjSubgroup N s = P) ∧
    (conjSubgroup P s = N ∨ conjSubgroup P s = P) := by
  have images (A : Subgroup G) [IsElementaryAbelian 2 A]
      (hAU : A ≤ U) (hc : Nat.card A = Nat.card N) :
      conjSubgroup A s = N ∨ conjSubgroup A s = P := by
    have hi : IsElementaryAbelian 2 (conjSubgroup A s) :=
      IsElementaryAbelian.map (MulAut.conj s).toMonoidHom
    have hiU := (conjSubgroup_mono hAU s).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp hs)
    rcases hcover _ hi hiU with hn | hp
    · exact Or.inl (eq_of_le_of_card_ge hn (by rw [card_conjSubgroup, hc]))
    · exact Or.inr (eq_of_le_of_card_ge hp (by rw [card_conjSubgroup, hc, hcard]))
  exact ⟨images N hNU rfl, images P hPU hcard.symm⟩

-- The nontrivial permutation is obtained from the normalizer condition.
private theorem closure_pair_normalizers {N P U S : Subgroup G}
    [IsElementaryAbelian 2 N] [IsElementaryAbelian 2 P]
    (hSp : IsPGroup 2 S) (hUS : U < S)
    (hNU : N ≤ U) (hPU : P ≤ U) (hNP : N ≠ P)
    (hcard : Nat.card N = Nat.card P)
    (hcover : ∀ A : Subgroup G, IsElementaryAbelian 2 A → A ≤ U → A ≤ N ∨ A ≤ P)
    (hUN : U = S ⊓ normalizer (N : Set G)) :
    U.relIndex (S ⊓ normalizer (U : Set G)) = 2 ∧
      S ⊓ normalizer (P : Set G) = U ∧
      ∃ t ∈ S ⊓ normalizer (U : Set G), conjSubgroup N t = P := by
  let T := S ⊓ normalizer (U : Set G)
  have hUT : U ≤ T := le_inf hUS.le U.le_normalizer
  have hproper : U.subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top]
    exact fun he => hUS.not_ge (subgroupOf_eq_top.mp he)
  let : Group.IsNilpotent S := hSp.isNilpotent
  obtain ⟨t, ht, htn⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (U.subgroupOf S) hproper)
  have htT : (t : G) ∈ T := by
    rw [← subgroupOf_normalizer_eq hUS.le] at ht
    exact ⟨t.property, ht⟩
  have htnU : (t : G) ∉ U := htn
  have htN : conjSubgroup N (t : G) = P := by
    rcases (closure_pair_image hNU hPU hcard hcover htT.2).1 with hn | hp
    · exact (htnU (hUN ▸ ⟨t.property, mem_normalizer_iff_map_conj_eq.mpr hn⟩)).elim
    · exact hp
  have hinj (A B : Subgroup G) (s : G) (he : conjSubgroup A s = conjSubgroup B s) : A = B := by
    have hh := congrArg (fun X => conjSubgroup X s⁻¹) he
    simpa only [conjSubgroup_inv] using hh
  have htP : conjSubgroup P (t : G) = N := by
    rcases (closure_pair_image hNU hPU hcard hcover htT.2).2 with hn | hp
    · exact hn
    · exact (hNP (hinj N P t (htN.trans hp.symm))).elim
  have hidx : U.relIndex T = 2 := by
    apply relIndex_eq_two_iff_exists_notMem_and.mpr
    refine ⟨t, htT, htnU, ?_⟩
    intro b hb
    rcases (closure_pair_image hNU hPU hcard hcover hb.2).1 with hn | hp
    · exact Or.inr (hUN ▸ ⟨hb.1, mem_normalizer_iff_map_conj_eq.mpr hn⟩)
    · left
      rw [hUN]
      refine ⟨S.mul_mem hb.1 t.property, mem_normalizer_iff_map_conj_eq.mpr ?_⟩
      change conjSubgroup N (b * (t : G)) = N
      rw [← conjSubgroup_conjSubgroup, htN]
      rcases (closure_pair_image hNU hPU hcard hcover hb.2).2 with hn' | hp'
      · exact hn'
      · exact (hNP (hinj N P b (hp.trans hp'.symm))).elim
  have hPN : S ⊓ normalizer (P : Set G) = U := by
    rw [← htN, ← TightNormalizerSetup.conjugate_normalizer t.property, ← hUN]
    exact mem_normalizer_iff_map_conj_eq.mp htT.2
  exact ⟨hidx, hPN, t, htT, htN⟩


namespace TightNormalizerSetup
variable {K : Subgroup G} {g : G} {R S : Subgroup G}
variable (h : TightNormalizerSetup K g R S)
variable [IsElementaryAbelian 2 R]
include h
local notation "S₁" => ((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G))
local notation "N" => (S ⊓ normalizer (R : Set G))

/-- The two elementary subgroups give index two in the next normalizer and
identify the stabilizer of the second subgroup. The local cover is an explicit
premise, to be discharged by the source-theorem assembly. -/
theorem specialJoin_pair_data
    (e : ↥S₁ ≃* R) {y : G} (hy : y ∈ S)
    (hyN : conjSubgroup R y ≤ S ⊓ normalizer (N : Set G))
    (htriv : conjSubgroup R y ⊓ normalizer (R : Set G) = ⊥)
    (hP : IsElementaryAbelian 2 ↥(S₁ ⊔ conjSubgroup R y))
    (hcover : ∀ A : Subgroup G, IsElementaryAbelian 2 A →
      A ≤ N ⊔ conjSubgroup R y → A ≤ N ∨ A ≤ S₁ ⊔ conjSubgroup R y) :
    (N ⊔ conjSubgroup R y).relIndex
        (S ⊓ normalizer (↑(N ⊔ conjSubgroup R y) : Set G)) = 2 ∧
      S ⊓ normalizer (↑(S₁ ⊔ conjSubgroup R y) : Set G) = N ⊔ conjSubgroup R y := by
  let B := conjSubgroup R y
  let U := N ⊔ B
  let P := S₁ ⊔ B
  have hS1N : S₁ ≤ N := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hBS : B ≤ S := hyN.trans inf_le_left
  have hUS : U ≤ S := sup_le inf_le_left hBS
  have hNU : N ≤ U := le_sup_left
  have hPU : P ≤ U := sup_le (hS1N.trans hNU) le_sup_right
  have hBN : ¬ B ≤ N := by
    intro hb
    have hb0 : B = ⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      have hm : x ∈ B ⊓ normalizer (R : Set G) := ⟨hx, (hb hx).2⟩
      change x ∈ conjSubgroup R y ⊓ normalizer (R : Set G) at hm
      simpa only [htriv] using hm
    have hc := card_conjSubgroup R y
    have hr : Nat.card R ≤ 1 := by
      rw [← hc]
      change Nat.card B ≤ 1
      rw [hb0]
      simp
    exact h.hRne ((R.card_le_one_iff_eq_bot).mp hr)
  have hproper : U < S := by
    refine lt_of_le_of_ne hUS ?_
    intro he
    have hSN : S ≤ normalizer (N : Set G) := by
      calc
        S = U := he.symm
        _ = S ⊓ normalizer (N : Set G) := h.specialJoin_eq_secondNormalizer e hyN htriv
        _ ≤ normalizer (N : Set G) := inf_le_right
    have hconj : B ≤ N :=
      (conjSubgroup_mono (le_inf h.hRS R.le_normalizer) y).trans_eq
        (mem_normalizer_iff_map_conj_eq.mp (hSN hy))
    exact hBN hconj
  have hneq : N ≠ P := by
    intro he
    exact hBN (le_sup_right.trans_eq he.symm)
  let : IsElementaryAbelian 2 P := hP
  let : IsElementaryAbelian 2 ↥N := h.special_normalizer_elementary e
  have hnorm : B ≤ normalizer (S₁ : Set G) :=
    le_sup_right.trans (h.specialJoin_normalizes_intersection hyN)
  have hd : Disjoint S₁ B :=
    (disjoint_iff.mpr htriv).symm.mono inf_le_right le_rfl
  have hcard : Nat.card ↥N = Nat.card P := by
    rw [h.special_normalizer_card e,
      show Nat.card P = Nat.card ↥S₁ * Nat.card B from
        card_sup_eq_mul_of_normalizes_of_disjoint S₁ B hnorm hd,
      Nat.card_congr e.toEquiv, card_conjSubgroup, pow_two]
  obtain ⟨hi, hn, _⟩ := closure_pair_normalizers h.hSp hproper hNU hPU hneq hcard hcover
    (h.specialJoin_eq_secondNormalizer e hyN htriv)
  exact ⟨hi, hn⟩

omit [IsElementaryAbelian 2 R] in
/-- The elementary subgroup `P = S₁ Rʸ` is exactly `N_S(Rʸ)`: it centralizes
`Rʸ` and has the same order as its normalizer, the conjugate of `N_S(R)`. -/
theorem specialJoin_other_normalizer
    (e : ↥S₁ ≃* R) {y : G} (hy : y ∈ S)
    (hyN : conjSubgroup R y ≤ S ⊓ normalizer (N : Set G))
    (htriv : conjSubgroup R y ⊓ normalizer (R : Set G) = ⊥)
    (hP : IsElementaryAbelian 2 ↥(S₁ ⊔ conjSubgroup R y)) :
    S ⊓ normalizer (conjSubgroup R y : Set G) = S₁ ⊔ conjSubgroup R y := by
  let B := conjSubgroup R y
  let P := S₁ ⊔ B
  let : IsElementaryAbelian 2 P := hP
  have hPS : P ≤ S := sup_le (inf_le_left.trans inf_le_left) (hyN.trans inf_le_left)
  have hle : P ≤ S ⊓ normalizer (B : Set G) := by
    refine le_inf hPS (le_trans ?_ (centralizer_le_normalizer _))
    intro x hx b hb
    exact setLike_mul_comm (s := P) ((le_sup_right : B ≤ P) hb) hx
  have hnorm : B ≤ normalizer (S₁ : Set G) :=
    le_sup_right.trans (h.specialJoin_normalizes_intersection hyN)
  have hd : Disjoint S₁ B :=
    (disjoint_iff.mpr htriv).symm.mono inf_le_right le_rfl
  have hcard : Nat.card P = Nat.card ↥N := by
    rw [show Nat.card P = Nat.card ↥S₁ * Nat.card B from
      card_sup_eq_mul_of_normalizes_of_disjoint S₁ B hnorm hd,
      Nat.card_congr e.toEquiv, card_conjSubgroup, h.special_normalizer_card e, pow_two]
  apply (eq_of_le_of_card_ge hle ?_).symm
  rw [← conjugate_normalizer hy, card_conjSubgroup, hcard]

/-- Exhaustion of the normal closure, conditional on the two local-structure
premises. The escaping conjugate and its involution are constructed in the proof.
The non-product assumption is retained as part of the branch interface; the
supplied conjugate with trivial relative normalizer already excludes that case. -/
theorem specialJoin_eq_normalClosure
    (e : ↥S₁ ≃* R)
    (hp : S₁ < S ⊓ conjSubgroup K g)
    (hR2 : Nat.card R ≠ 2)
    (_hW : tightNormalClosure R S ≠ R ⊔ S₁)
    {y : G} (hy : y ∈ S)
    (hyN : conjSubgroup R y ≤ S ⊓ normalizer (N : Set G))
    (htriv : conjSubgroup R y ⊓ normalizer (R : Set G) = ⊥)
    (hP : IsElementaryAbelian 2 ↥(S₁ ⊔ conjSubgroup R y))
    (hcover : ∀ A : Subgroup G, IsElementaryAbelian 2 A →
      A ≤ N ⊔ conjSubgroup R y → A ≤ N ∨ A ≤ S₁ ⊔ conjSubgroup R y) :
    N ⊔ conjSubgroup R y = tightNormalClosure R S := by
  let B := conjSubgroup R y
  let U := N ⊔ B
  let P := S₁ ⊔ B
  let T := S ⊓ normalizer (U : Set G)
  have hBS : B ≤ S := hyN.trans inf_le_left
  have hUS : U ≤ S := sup_le inf_le_left hBS
  have hRN : R ≤ N := le_inf h.hRS R.le_normalizer
  have hRU : R ≤ U := hRN.trans le_sup_left
  have hUT : U ≤ T := le_inf hUS U.le_normalizer
  have hPU : P ≤ U := sup_le
    ((le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans le_sup_left) le_sup_right
  have hUN : U = S ⊓ normalizer (N : Set G) :=
    h.specialJoin_eq_secondNormalizer e hyN htriv
  obtain ⟨hindex, hPN⟩ := h.specialJoin_pair_data e hy hyN htriv hP hcover
  change U.relIndex T = 2 at hindex
  change S ⊓ normalizer (P : Set G) = U at hPN
  have hNB : S ⊓ normalizer (B : Set G) = P :=
    h.specialJoin_other_normalizer e hy hyN htriv hP
  have hcardP : Nat.card P = Nat.card ↥N := by
    rw [← hNB, ← conjugate_normalizer hy, card_conjSubgroup]
  let : IsElementaryAbelian 2 ↥N := h.special_normalizer_elementary e
  let : IsElementaryAbelian 2 P := hP
  have hUW : U ≤ tightNormalClosure R S := h.specialJoin_le_normalClosure e hp hy
  apply le_antisymm hUW
  by_contra hWU
  -- If the next normalizer were all of `S`, normal closure would give `W ≤ U`.
  have hTproper : T.subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have hn : (U.subgroupOf S).Normal :=
      (normal_subgroupOf_iff_le_normalizer hUS).mpr
        ((subgroupOf_eq_top.mp htop).trans inf_le_right)
    exact hWU (normalClosure_min hn hRU)
  let : Group.IsNilpotent S := h.hSp.isNilpotent
  obtain ⟨s, hsT, hsnot⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (T.subgroupOf S) hTproper)
  have hsNorm : (s : G) ∈ normalizer (T : Set G) := by
    rw [← subgroupOf_normalizer_eq (show T ≤ S from inf_le_left)] at hsT
    exact hsT
  let C := conjSubgroup R (s : G)
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.map (MulAut.conj (s : G)).toMonoidHom
  have hCS : C ≤ S :=
    (conjSubgroup_mono h.hRS s).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer s.property))
  have hCT : C ≤ T := (conjSubgroup_mono (hRU.trans hUT) s).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp hsNorm)
  have hCN : conjSubgroup N (s : G) = S ⊓ normalizer (C : Set G) :=
    conjugate_normalizer s.property
  -- Containment in either elementary subgroup would force `s` back into `T`.
  have hCU : ¬ C ≤ U := by
    intro hle
    rcases hcover C inferInstance hle with hCNle | hCPle
    · have hn : N ≤ S ⊓ normalizer (C : Set G) := by
        refine le_inf inf_le_left (le_trans ?_ (centralizer_le_normalizer _))
        intro x hx c hc
        exact setLike_mul_comm (s := N) (hCNle hc) hx
      have heq : N = conjSubgroup N (s : G) :=
        eq_of_le_of_card_ge (hn.trans_eq hCN.symm) (card_conjSubgroup N s).le
      have hsU : (s : G) ∈ U := hUN ▸
        ⟨s.property, mem_normalizer_iff_map_conj_eq.mpr heq.symm⟩
      exact hsnot (hUT hsU)
    · have hn : P ≤ S ⊓ normalizer (C : Set G) := by
        refine le_inf (hPU.trans hUS) (le_trans ?_ (centralizer_le_normalizer _))
        intro x hx c hc
        exact setLike_mul_comm (s := P) (hCPle hc) hx
      have heq : P = conjSubgroup N (s : G) :=
        eq_of_le_of_card_ge (hn.trans_eq hCN.symm) (by rw [card_conjSubgroup, hcardP])
      have hconjU : conjSubgroup U (s : G) = U := by
        calc
          conjSubgroup U (s : G) = conjSubgroup (S ⊓ normalizer (N : Set G)) (s : G) :=
            congrArg (fun A => conjSubgroup A (s : G)) hUN
          _ = S ⊓ normalizer (conjSubgroup N (s : G) : Set G) :=
            conjugate_normalizer (R := N) s.property
          _ = U := by rw [← heq, hPN]
      exact hsnot ⟨s.property, mem_normalizer_iff_map_conj_eq.mpr hconjU⟩
  have hcardR : 2 < Nat.card R := by
    have hone := (one_lt_card_iff_ne_bot R).mpr h.hRne
    omega
  have hmeet : C ⊓ U ≠ ⊥ := by
    intro heq
    have hi : U.relIndex C ≤ 2 := by
      simpa only [hindex] using relIndex_le_of_le_right hCT (by omega : U.relIndex T ≠ 0)
    rw [← inf_relIndex_left, heq, relIndex_bot_left] at hi
    have hc : Nat.card C = Nat.card R := card_conjSubgroup R s
    omega
  obtain ⟨i, hine⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hmeet
  have hival : (i : G) ≠ 1 := fun he => hine (Subtype.ext he)
  have hipow : (i : G) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ i.property.1
  have hiE : IsElementaryAbelian 2 (zpowers (i : G)) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hipow
  have hiU : zpowers (i : G) ≤ U := zpowers_le.mpr i.property.2
  have hiN : (i : G) ∈ N ∨ (i : G) ∈ P :=
    (hcover _ hiE hiU).imp (fun hn => hn (mem_zpowers _)) (fun hp => hp (mem_zpowers _))
  rcases hiN with hiN | hiP
  · have hne : C ≠ R := fun he => hCU (he ▸ hRU)
    have hn : C ⊓ normalizer (R : Set G) ≠ ⊥ := by
      intro he
      exact hival (mem_bot.mp (he ▸ (show (i : G) ∈ C ⊓ normalizer (R : Set G) from
        ⟨i.property.1, hiN.2⟩)))
    obtain ⟨_, hc⟩ := lemma_I_7_6_commuting h.pgroupSetup (h.hSle s.property) hne hCS hn
    exact hCU ((le_inf hCS ((le_centralizer_iff.mp hc).trans
      (centralizer_le_normalizer _))).trans le_sup_left)
  -- The second case uses I.7.6 for `B`, with conjugating element `s * y⁻¹`.
  · have hsetup : TightPGroupSetup (conjSubgroup K y) (conjSubgroup K g ⊔ R) B S :=
      h.pgroupSetup.conjugate (h.hSle hy) h.hSp h.hSle hBS
    have hconj : conjSubgroup B ((s : G) * y⁻¹) = C := by
      change conjSubgroup (conjSubgroup R y) ((s : G) * y⁻¹) = conjSubgroup R (s : G)
      rw [conjSubgroup_conjSubgroup, inv_mul_cancel_right]
    have hne : conjSubgroup B ((s : G) * y⁻¹) ≠ B := by
      rw [hconj]
      exact fun he => hCU (he ▸ le_sup_right)
    have hn : conjSubgroup B ((s : G) * y⁻¹) ⊓ normalizer (B : Set G) ≠ ⊥ := by
      rw [hconj]
      intro he
      have hiB : (i : G) ∈ normalizer (B : Set G) := ((hNB.symm ▸ hiP) :
        (i : G) ∈ S ⊓ normalizer (B : Set G)).2
      exact hival (mem_bot.mp (he ▸ (show (i : G) ∈ C ⊓ normalizer (B : Set G) from
        ⟨i.property.1, hiB⟩)))
    obtain ⟨_, hc⟩ := lemma_I_7_6_commuting hsetup
      ((conjSubgroup K g ⊔ R).mul_mem (h.hSle s.property)
        ((conjSubgroup K g ⊔ R).inv_mem (h.hSle hy))) hne (hconj ▸ hCS) hn
    rw [hconj] at hc
    have hCP : C ≤ P := by
      rw [← hNB]
      exact le_inf hCS ((le_centralizer_iff.mp hc).trans (centralizer_le_normalizer _))
    exact hCU (hCP.trans hPU)

/-- The complete conditional closure helper for the special branch of I.7.7:
`U` has index two in its relative normalizer, equals the normal closure inside
`S`, and that normal closure has index two in `S`. Only `hP` and `hcover` are
additional local-structure premises. -/
theorem specialJoin_closure_exhaustion
    (e : ↥S₁ ≃* R)
    (hp : S₁ < S ⊓ conjSubgroup K g)
    (hR2 : Nat.card R ≠ 2)
    (hW : tightNormalClosure R S ≠ R ⊔ S₁)
    {y : G} (hy : y ∈ S)
    (hyN : conjSubgroup R y ≤ S ⊓ normalizer (N : Set G))
    (htriv : conjSubgroup R y ⊓ normalizer (R : Set G) = ⊥)
    (hP : IsElementaryAbelian 2 ↥(S₁ ⊔ conjSubgroup R y))
    (hcover : ∀ A : Subgroup G, IsElementaryAbelian 2 A →
      A ≤ N ⊔ conjSubgroup R y → A ≤ N ∨ A ≤ S₁ ⊔ conjSubgroup R y) :
    (N ⊔ conjSubgroup R y).relIndex
        (S ⊓ normalizer (↑(N ⊔ conjSubgroup R y) : Set G)) = 2 ∧
      N ⊔ conjSubgroup R y = tightNormalClosure R S ∧
      (tightNormalClosure R S).relIndex S = 2 := by
  have hi := (h.specialJoin_pair_data e hy hyN htriv hP hcover).1
  have he := h.specialJoin_eq_normalClosure e hp hR2 hW hy hyN htriv hP hcover
  refine ⟨hi, he, ?_⟩
  rw [he] at hi
  have hn : S ≤ normalizer (tightNormalClosure R S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (normalClosure_le R S)).mp
      (normalClosure_normal R S)
  simpa only [inf_eq_left.mpr hn] using hi

end TightNormalizerSetup
end CFSG.Quasithin.ChapterI.Section06To08
