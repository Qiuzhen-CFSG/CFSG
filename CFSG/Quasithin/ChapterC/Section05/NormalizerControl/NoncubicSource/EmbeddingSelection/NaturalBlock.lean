module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2CoverOrders
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.SmallModels
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Alternatives.Models
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension
public import Theory.Mathieu.M24.Properties.Order
public import Theory.ElementaryAbelian.Injective

/-!
# The odd-degree natural-block row in A.3.12

A centerless natural block with its full elementary two-core has order
`2^(3*n) * (2^(2*n)-1)`. The two-part and odd part exclude the small
solvable-kernel extensions when n is odd. Extraspecial and cyclic-four
kernels cannot embed in its elementary two-core. Whole quasisimple smaller
models are excluded by the nontrivial two-core and trivial center, while
the literal two-core quotient excludes the remaining small quotient models.
The odd-core rows are impossible in a quasisimple containing group.

Consequently the actual twenty-two embedding alternatives for a proper
natural block reduce to the maximal rank-two parabolic case. This proves a
row reduction, retaining the genuine A.3.12 embedding as an explicit input;
it does not assert the universal embedding theorem or identify the remaining
rank-two model as PSL₃. The moving-Hall owner supplies those remaining steps.
Source: Aschbacher–Smith A.3.12, printed pp.47–48, applied in 10.2.3(4), p.747.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter1.Section02.LocalModels
open CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.Alternatives
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection.NaturalBlock
variable {B : Type*} [Group B] [Finite B] {n : ℕ}

theorem card (h : IsL2EvenBlock B n) (hc : pCore 2 B = blockU B)
    (hz : center B = ⊥) : Nat.card B = 2^(3*n)*((2^n)^2-1) := by
  have hh := h.center_quotient_card hc
  rw [hz] at hh
  exact (Nat.card_congr QuotientGroup.quotientBot.toEquiv).symm.trans hh

theorem two_valuation (h : IsL2EvenBlock B n) (hc : pCore 2 B = blockU B)
    (hz : center B = ⊥) : (Nat.card B).factorization 2 = 3*n := by
  have hn := h.1
  have hq : 1 < 2^n := Nat.one_lt_pow (by omega) (by decide)
  have hs : 1 < (2^n)^2 := by nlinarith
  have ho : Odd ((2^n)^2-1) := by
    apply Nat.Even.sub_odd (by nlinarith)
    · exact (even_two.pow_of_ne_zero (by have := h.1; omega)).pow_of_ne_zero (by decide)
    · exact odd_one
  rw [card h hc hz, Nat.factorization_mul (by positivity) (by omega),
    Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by simpa only [← even_iff_two_dvd] using Nat.not_even_iff_odd.mpr ho),add_zero]

private theorem not_order (h : IsL2EvenBlock B n) (hc : pCore 2 B = blockU B)
    (hz : center B = ⊥) (ho : Odd n) (k m : ℕ) (hm : Odd m)
    (hne : ∀ a : ℕ, 1 < a → Odd a → 3*a=k →
      2^(3*a)*((2^a)^2-1) ≠ 2^k*m) : Nat.card B ≠ 2^k*m := by
  intro he
  have hv := two_valuation h hc hz
  have hmn : m ≠ 0 := by intro he; rw [he] at hm; norm_num at hm
  rw [he,Nat.factorization_mul (by positivity) hmn,Finsupp.add_apply,
    Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by simpa only [← even_iff_two_dvd] using Nat.not_even_iff_odd.mpr hm),add_zero] at hv
  exact hne n h.1 ho hv.symm ((card h hc hz).symm.trans he)

private theorem not_quasisimple (h : IsL2EvenBlock B n) (hz : center B = ⊥) :
    ¬ IsQuasisimple B := by
  intro hq
  let := hq
  exact h.2.1.core_ne_bot (le_bot_iff.mp ((IsQuasisimple.pCore_le_center 2).trans hz.le))

private theorem solvable_normal_le_core [Group.IsPerfect B] (h : IsL2EvenBlock B n)
    (N : Subgroup B) [N.Normal] [Group.IsSolvable N] : N ≤ pCore 2 B := by
  let : IsSimpleGroup (B ⧸ pCore 2 B) := binary_simple h.1 h.2.2.choose_spec.choose_spec.choose_spec.2.1
  rw [← PerfectCoreTwoExtension.radical_eq_core]
  exact le_solvableRadical N inferInstance inferInstance

private theorem alternating_card {X : Type*} [Group X] {d : ℕ} (h : IsAlternating X d) (hd : 2 ≤ d) :
    Nat.card X = Nat.factorial d / 2 := by
  have : NeZero d := ⟨by omega⟩
  have : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
  obtain ⟨e⟩ := h
  simpa using (Nat.card_congr e.toEquiv).trans (nat_card_alternatingGroup (α := Fin d))

private theorem alternating_cover_card {X : Type*} [Group X] {d : ℕ}
    (h : IsAlternatingCover X d) (hd : 2 ≤ d) : Nat.card X = (Nat.factorial d / 2)*3 := by
  have : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
  obtain ⟨_,⟨z⟩,⟨e⟩⟩ := h
  rw [card_eq_card_quotient_mul_card_subgroup (center X),
    Nat.card_congr e.toEquiv,Nat.card_congr z.toEquiv,nat_card_alternatingGroup]
  simp

private theorem elementary_card {X : Type*} [Group X] {r : ℕ}
    (h : ElementaryModel 2 r X) : Nat.card X = 2^r := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  simp

private theorem psl32_card {X : Type*} [Group X]
    (h : ClassicalGroup.IsPSL X 3 2) : Nat.card X = 168 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  have hh := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  rw [hF] at hh
  norm_num [Fin.prod_univ_succ] at hh ⊢
  exact hh

private theorem psl42_card {X : Type*} [Group X]
    (h : ClassicalGroup.IsPSL X 4 2) : Nat.card X = 20160 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  have hh := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
  rw [hF] at hh
  norm_num [Fin.prod_univ_succ] at hh ⊢
  exact hh

private theorem not_elementary_alternating_extension
    (h : IsL2EvenBlock B n) (hc : pCore 2 B = blockU B) (hz : center B = ⊥)
    (ho : Odd n) {r d : ℕ} (hr : r=3 ∨ r=4 ∨ r=6)
    (hd : d=5 ∨ d=6 ∨ d=7) :
    ¬ HasExtension B (ElementaryModel 2 r) (fun X _ => IsAlternating X d) := by
  rintro ⟨N,_,hk,hq⟩
  have hh := card_eq_card_quotient_mul_card_subgroup N
  rw [elementary_card hk,alternating_card hq (by rcases hd with rfl | rfl | rfl <;> omega)] at hh
  rcases hr with rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl
  all_goals norm_num at hh
  all_goals first
    | exact not_order h hc hz ho 5 15 (by decide)
        (by rintro a ha ⟨t,ht⟩ he; omega) (by norm_num; exact hh)
    | exact not_order h hc hz ho 6 15 (by decide)
        (by rintro a ha ⟨t,ht⟩ he; omega)
        (by norm_num; exact hh)
    | exact not_order h hc hz ho 6 45 (by decide)
        (by rintro a ha ⟨t,ht⟩ he; omega)
        (by norm_num; exact hh)
    | exact not_order h hc hz ho 6 315 (by decide)
        (by rintro a ha ⟨t,ht⟩ he; omega)
        (by norm_num; exact hh)
    | exact not_order h hc hz ho 7 45 (by decide)
        (by rintro a ha ⟨t,ht⟩ he; omega) (by norm_num; exact hh)
    | exact not_order h hc hz ho 7 315 (by decide)
        (by rintro a ha ⟨t,ht⟩ he; omega) (by norm_num; exact hh)
    | exact not_order h hc hz ho 8 15 (by decide)
        (by rintro a ha ⟨t,ht⟩ he; omega) (by norm_num; exact hh)
    | exact not_order h hc hz ho 9 45 (by decide)
        (by
          intro a ha hoa he
          have heq : a=3 := by omega
          simpa only [heq] using (by decide : 2^(3*3)*((2^3)^2-1) ≠ 2^9*45))
        (by norm_num; exact hh)
    | exact not_order h hc hz ho 9 315 (by decide)
        (by
          intro a ha hoa he
          have heq : a=3 := by omega
          simpa only [heq] using (by decide : 2^(3*3)*((2^3)^2-1) ≠ 2^9*315))
        (by norm_num; exact hh)


omit [Finite B] in
private theorem normal_two_elementary (h : IsL2EvenBlock B n)
    (hc : pCore 2 B = blockU B) (N : Subgroup B) [N.Normal]
    (hp : IsPGroup 2 N) : IsElementaryAbelian 2 N := by
  have he : IsElementaryAbelian 2 (pCore 2 B) := hc ▸ h.2.1.elementary
  have hN : N ≤ pCore 2 B := le_sSup ⟨inferInstance,hp⟩
  exact IsElementaryAbelian.of_injective (inclusion hN) (inclusion_injective hN)

omit [Finite B] in
private theorem not_extraspecial_extension (h : IsL2EvenBlock B n)
    (hc : pCore 2 B = blockU B) {r : ℕ} (ψ : GroupClass) :
    ¬ HasExtension B (ExtraspecialModel 2 r) ψ := by
  rintro ⟨N,_,hk,_⟩
  have he := normal_two_elementary h hc N (extraspecial_twoGroup hk)
  have ht : center N = ⊤ := center_eq_top_iff.mpr inferInstance
  have hn : Nontrivial (N ⧸ center N) := hk.1.quotient_nontrivial
  exact QuotientGroup.nontrivial_iff.mp hn ht

omit [Finite B] in
private theorem not_cyclic_extraspecial_extension (h : IsL2EvenBlock B n)
    (hc : pCore 2 B = blockU B) {r : ℕ} (ψ : GroupClass) :
    ¬ HasExtension B (CyclicFourCentralProduct r) ψ := by
  rintro ⟨N,_,hk,_⟩
  have he := normal_two_elementary h hc N (cyclicFourProduct_twoGroup hk)
  obtain ⟨C,E,⟨e⟩,_⟩ := hk
  have hC : IsElementaryAbelian 2 C :=
    IsElementaryAbelian.of_injective C.subtype C.subtype_injective
  have h4 : IsElementaryAbelian 2 (Multiplicative (ZMod 4)) :=
    IsElementaryAbelian.of_injective e.symm.toMonoidHom e.symm.injective
  have hh := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 (Multiplicative (ZMod 4)))
      (Multiplicative.ofAdd (1 : ZMod 4))
  have hf := congrArg Multiplicative.toAdd hh
  change (2 : ZMod 4) = 0 at hf
  exact (by decide : (2 : ZMod 4) ≠ 0) hf

omit [Finite B] in
private theorem not_homocyclic_extension (h : IsL2EvenBlock B n)
    (hc : pCore 2 B = blockU B) (ψ : GroupClass) :
    ¬ HasExtension B (fun X _ => Nonempty (X ≃* Multiplicative (Fin 3 → ZMod 4))) ψ := by
  rintro ⟨N,_,hk,_⟩
  have he := normal_two_elementary h hc N (fourCube_twoGroup hk)
  have h4 : IsElementaryAbelian 2 (Multiplicative (Fin 3 → ZMod 4)) :=
    IsElementaryAbelian.of_injective hk.some.symm.toMonoidHom hk.some.symm.injective
  have hh := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 (Multiplicative (Fin 3 → ZMod 4)))
      (Multiplicative.ofAdd (fun _ => (1 : ZMod 4)))
  have hf := congrArg (fun x : Multiplicative (Fin 3 → ZMod 4) => Multiplicative.toAdd x 0) hh
  change (2 : ZMod 4) = 0 at hf
  exact (by decide : (2 : ZMod 4) ≠ 0) hf


omit [Finite B] in
private theorem extension_card {r q : ℕ} {ψ : GroupClass}
    (h : HasExtension B (ElementaryModel 2 r) ψ)
    (hq : ∀ (X : Type _) [Group X], ψ X → Nat.card X = q) :
    Nat.card B = 2^r*q := by
  obtain ⟨N,_,hk,hmod⟩ := h
  rw [card_eq_card_quotient_mul_card_subgroup N,elementary_card hk,hq _ hmod,mul_comm]

private theorem not_elementary_psl32_extension
    (h : IsL2EvenBlock B n) (hc : pCore 2 B = blockU B) (hz : center B = ⊥)
    (ho : Odd n) {r : ℕ} (hr : r=3 ∨ r=4 ∨ r=6) :
    ¬ HasExtension B (ElementaryModel 2 r) (fun X _ => ClassicalGroup.IsPSL X 3 2) := by
  intro he
  have hh := extension_card he (fun _ _ => psl32_card)
  rcases hr with rfl | rfl | rfl
  · exact not_order h hc hz ho 6 21 (by decide)
      (by rintro a ha ⟨t,ht⟩ he; omega) (by norm_num; exact hh)
  · exact not_order h hc hz ho 7 21 (by decide)
      (by rintro a ha ⟨t,ht⟩ he; omega) (by norm_num; exact hh)
  · apply not_order h hc hz ho 9 21 (by decide) _ (by norm_num; exact hh)
    intro a ha hoa he
    have heq : a=3 := by omega
    rw [heq]
    decide

private theorem not_elementary_cover_extension
    (h : IsL2EvenBlock B n) (hc : pCore 2 B = blockU B) (hz : center B = ⊥)
    (ho : Odd n) {r : ℕ} (hr : r=4 ∨ r=6) :
    ¬ HasExtension B (ElementaryModel 2 r) (fun X _ => IsAlternatingCover X 6) := by
  intro he
  have hh := extension_card he (fun _ _ hq => alternating_cover_card hq (by decide))
  norm_num at hh
  rcases hr with rfl | rfl
  · exact not_order h hc hz ho 7 135 (by decide)
      (by rintro a ha ⟨t,ht⟩ he; omega) (by norm_num; exact hh)
  · apply not_order h hc hz ho 9 135 (by decide) _ (by norm_num; exact hh)
    intro a ha hoa he
    have heq : a=3 := by omega
    rw [heq]
    decide

private theorem not_elementary_psl42_extension
    (h : IsL2EvenBlock B n) (hc : pCore 2 B = blockU B) (hz : center B = ⊥)
    (ho : Odd n) :
    ¬ HasExtension B (ElementaryModel 2 4) (fun X _ => ClassicalGroup.IsPSL X 4 2) := by
  intro he
  have hh := extension_card he (fun _ _ => psl42_card)
  exact not_order h hc hz ho 10 315 (by decide)
    (by rintro a ha ⟨t,ht⟩ he; omega) (by norm_num; exact hh)

private theorem not_elementary_m24_extension
    (h : IsL2EvenBlock B n) (hc : pCore 2 B = blockU B) (hz : center B = ⊥)
    (ho : Odd n) :
    ¬ HasExtension B (ElementaryModel 2 11) (fun X _ => Nonempty (X ≃* Sporadic.Mathieu.M24)) := by
  intro he
  have hh := extension_card he (fun X _ he =>
    (Nat.card_congr he.some.toEquiv).trans Sporadic.Mathieu.m24_order)
  apply not_order h hc hz ho 21 239085 (by decide) _ (by norm_num; exact hh)
  intro a ha hoa he
  have heq : a=7 := by omega
  rw [heq]
  decide


private theorem not_odd_elementary_extension [Group.IsPerfect B] (h : IsL2EvenBlock B n)
    {p : ℕ} (ho : Odd p) (hp : 1 < p) (ψ : GroupClass) :
    ¬ HasExtension B (ElementaryModel p 2) ψ := by
  rintro ⟨N,_,⟨e⟩,_⟩
  have hs : Group.IsSolvable N := Group.isSolvable_of_comm (fun a b => e.injective (by
    simp only [map_mul,mul_comm]))
  have hN := solvable_normal_le_core h N
  have hpN : IsPGroup 2 N := pCore_isPGroup.of_injective
    (inclusion hN) (inclusion_injective hN)
  have hcN : Nat.card N = p^2 := by
    rw [Nat.card_congr e.toEquiv]
    have : NeZero p := ⟨by omega⟩
    simp
  obtain ⟨a,ha⟩ := IsPGroup.iff_card.mp hpN
  have heven : Odd (Nat.card N) := by rw [hcN]; exact ho.pow
  have hcop := (Nat.coprime_two_left.mpr heven).pow_left a
  rw [←ha] at hcop
  have hone := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl dvd_rfl
  have hlt : 1 < p^2 := Nat.one_lt_pow (by decide) hp
  omega

open CFSG.Quasithin.Chapter1.Section02 in
/-- The two exceptional odd-core rows are impossible in a quasisimple
containing group which contains the nontrivial natural two-core. -/
private theorem odd_core_commutator {G : Type*} [Group G] [Finite G]
    (J K : Subgroup G) [IsQuasisimple K] {n : ℕ}
    (h : IsL2EvenBlock J n) (hc : pCore 2 J = blockU J)
    (hz : center J = ⊥) (hJK : J ≤ K) :
    ⁅pPrimeCore 2 K,(⊤ : Subgroup K)⁆ = ⊥ := by
  have heJ : 2 ∣ Nat.card J := by
    rw [card h hc hz]
    apply dvd_mul_of_dvd_left
    exact dvd_pow_self 2 (by have := h.1; omega)
  have heK : 2 ∣ Nat.card K := heJ.trans
    (card_dvd_of_injective (inclusion hJK) (inclusion_injective hJK))
  have hO : pPrimeCore 2 K ≤ center K := by
    rcases IsQuasisimple.normal_le_center_or_eq_top (pPrimeCore 2 K) with hO | ht
    · exact hO
    · have hcop := pPrimeCore_coprime_card (p := 2) (G := K)
      rw [ht,Nat.card_congr (topEquiv (G := K)).toEquiv] at hcop
      exact (Nat.prime_two.coprime_iff_not_dvd.mp hcop heK).elim
  exact commutator_eq_bot_iff_le_centralizer.mpr (by
    simpa only [coe_top,centralizer_univ] using hO)

open CFSG.Quasithin.Chapter1.Section02
/-- For a proper centerless natural block of odd degree, the twenty-two
embedding alternatives reduce to the maximal rank-two parabolic row. -/
theorem select_rank_two {G : Type*} [Group G] [Finite G]
    (J K : Subgroup G) [Group.IsPerfect J] [IsQuasisimple K] {n : ℕ}
    (h : IsL2EvenBlock J n) (hc : pCore 2 J = blockU J)
    (hz : center J = ⊥) (ho : Odd n) (hJK : J < K)
    (hrows : A312Embedding J K) :
    RankTwoTheoremC K ∧ IsParabolicResidual J K true := by
  have hm : ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 2 (2^n) :=
    h.2.2.choose_spec.choose_spec.choose_spec.2.1
  have nq := not_quasisimple h hz
  have noA (d : ℕ) (hd : 5 ≤ d) (ha : IsAlternating J d) : False :=
    nq (alternating_quasisimple ha hd)
  have noP (d q : ℕ) (hd : 3 ≤ d ∨ d=2 ∧ 4≤q)
      (ha : ClassicalGroup.IsPSL J d q) : False := nq (psl_quasisimple ha hd)
  have no5 (ha : IsAlternating (J ⧸ pCore 2 J) 5) : False := by
    have he := binary_parameter_of_alternating_five (by have := h.1; omega) hm ha
    rw [he] at ho
    exact (by decide : ¬ Odd 2) ho
  have hn : 0 < n := by have := h.1; omega
  cases hrows with
  | one he => exact (hJK.ne he).elim
  | two m hm' hsmall hlarge hres => exact ⟨hlarge,hres⟩
  | three m hm' hsmall _ _ => exact (binary_not_suzuki hm m (by omega) hsmall).elim
  | four hsmall _ _ => exact (binary_not_linear_three_two hn hm hsmall).elim
  | five hsmall _ _ => exact (binary_not_linear_four_two hn hm hsmall).elim
  | six hs _ =>
      rcases hs with hs | hs
      · exact (noA 5 (by decide) hs).elim
      · exact (noP 3 2 (.inl (by decide)) hs).elim
  | seven hs =>
      rcases hs with ⟨hs,_⟩ | ⟨hs,_⟩
      · exact (noA 6 (by decide) hs).elim
      · exact (nq hs.1).elim
  | eight hs =>
      rcases hs with ⟨p,_,_,hp,hs,_⟩ | ⟨p,_,hs,_⟩
      · exact (noP 2 p (.inr ⟨rfl,by omega⟩) hs).elim
      · exact (noA 5 (by decide) hs).elim
  | nine hs =>
      rcases hs with ⟨p,_,_,_,hp,hs,_⟩ | ⟨hs,_⟩ | ⟨hs,_⟩
      · exact (nq (slTwo_quasisimple hs (by omega))).elim
      · exact (noA 6 (by decide) hs).elim
      · exact (nq hs.1).elim
  | ten p _ hp hlarge hs _ =>
      exact (not_odd_elementary_extension h hp (by omega) _ hs).elim
  | eleven hs _ => exact (noA 6 (by decide) hs).elim
  | twelve hs =>
      rcases hs with ⟨⟨N,hN,hk,hq⟩,_⟩ | ⟨⟨N,hN,hk,hq⟩,_⟩
      · rcases hq with hq | hq
        · exact (not_elementary_alternating_extension h hc hz ho (.inr (.inl rfl)) (.inl rfl) ⟨N,hN,hk,hq⟩).elim
        · exact (not_elementary_alternating_extension h hc hz ho (.inr (.inl rfl)) (.inr (.inl rfl)) ⟨N,hN,hk,hq⟩).elim
      · rcases hq with hq | hq
        · exact (not_elementary_alternating_extension h hc hz ho (.inr (.inl rfl)) (.inl rfl) ⟨N,hN,hk,hq⟩).elim
        · exact (not_elementary_cover_extension h hc hz ho (.inl rfl) ⟨N,hN,hk,hq⟩).elim
  | thirteen _ hs =>
      rcases hs with hs | hs | ⟨N,hN,hk,hq⟩ | hs
      · exact (nq (m22_quasisimple hs)).elim
      · exact (noP 3 4 (.inl (by decide)) hs).elim
      · rcases hq with hq | hq | hq | hq
        · exact (not_elementary_alternating_extension h hc hz ho (.inr (.inl rfl)) (.inr (.inr rfl)) ⟨N,hN,hk,hq⟩).elim
        · exact (not_elementary_psl32_extension h hc hz ho (.inr (.inl rfl)) ⟨N,hN,hk,hq⟩).elim
        · exact (not_elementary_alternating_extension h hc hz ho (.inr (.inl rfl)) (.inr (.inl rfl)) ⟨N,hN,hk,hq⟩).elim
        · exact (not_elementary_alternating_extension h hc hz ho (.inr (.inl rfl)) (.inl rfl) ⟨N,hN,hk,hq⟩).elim
      · exact (not_elementary_psl32_extension h hc hz ho (.inl rfl) hs).elim
  | fourteen _ hs =>
      rcases hs with hs | ⟨N,hN,hk,hq⟩ | hs
      · exact (not_elementary_psl42_extension h hc hz ho hs).elim
      · rcases hq with hq | hq
        · exact (not_elementary_psl32_extension h hc hz ho (.inr (.inr rfl)) ⟨N,hN,hk,hq⟩).elim
        · exact (not_elementary_cover_extension h hc hz ho (.inr rfl) ⟨N,hN,hk,hq⟩).elim
      · exact (not_extraspecial_extension h hc _ hs).elim
  | fifteen hs _ => exact (noA 5 (by decide) hs).elim
  | sixteen hs _ => exact (not_extraspecial_extension h hc _ hs).elim
  | seventeen _ hs =>
      rcases hs with hs | hs | hs | hs | hs | hs
      · exact (not_extraspecial_extension h hc _ hs).elim
      · exact (not_elementary_m24_extension h hc hz ho hs).elim
      · exact (no5 hs).elim
      · exact (binary_not_alternating_cover_six hn hm hs).elim
      · exact (binary_not_linear_four_two hn hm hs).elim
      · exact (binary_not_linear_three_two hn hm hs).elim
  | eighteen _ hs =>
      rcases hs with hs | hs
      · exact (not_cyclic_extraspecial_extension h hc _ hs).elim
      · exact (not_homocyclic_extension h hc _ hs).elim
  | nineteen _ hs =>
      rcases hs with hs | hs
      · exact (not_extraspecial_extension h hc _ hs).elim
      · exact (not_elementary_cover_extension h hc hz ho (.inr rfl) hs).elim
  | twenty _ hs _ =>
      rcases hs with hs | hs
      · exact (no5 hs).elim
      · exact (binary_not_linear_three_two hn hm hs).elim
  | twenty_one _ _ _ hnon _ _ =>
      exact (hnon (odd_core_commutator J K h hc hz hJK.le)).elim
  | twenty_two _ _ hnon _ _ =>
      exact (hnon (odd_core_commutator J K h hc hz hJK.le)).elim

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection.NaturalBlock
