module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd.SevenThompsonImage
public import Theory.SpecificGroups.AlternatingSix.SmallIndex
public import Theory.GroupTheory.PermutingSupCard

/-!
# A cubic obstruction for the deleted seven-point Thompson group

The normalizer of three disjoint transpositions fixes the remaining letter.
A nontrivial cubic in that normalizer fixes no other letter: a single
three-cycle cannot permute the three pairs, so its cycle type is (3,3).
A commuting elementary nine-group would therefore fix the same letter.
If it permutes with the full Sylow, their join has order 144, impossible
inside a point stabilizer by simplicity of A₆ and the index bound.

Finite checks use pairs and triples of letters, not enumeration of S₇.
Source: Aschbacher–Smith B.3.2(4) and 5.1.13, pp.83–84,637.
-/

public noncomputable section
open Subgroup Equiv MulAction
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterB.Offenders.SevenNormalizer
local notation "S7" => Equiv.Perm (Fin 7)
local notation "A7" => alternatingGroup (Fin 7)

private theorem no_fixed_144 (S : Subgroup S7) (hS : Nat.card S = 144)
    (i : Fin 7) : ¬ S ≤ stabilizer S7 i := by
  intro hfix
  let R := (alternatingGroup (Fin 7)).subgroupOf S
  let E := S.subgroupOf A7
  have hR : R.index ≤ 2 := by
    change (A7 : Subgroup S7).relIndex S ≤ 2
    have hh := relIndex_le_of_le_right (H := A7) (show S ≤ ⊤ from le_top)
      (by simp)
    simpa only [relIndex_top_right,alternatingGroup.index_eq_two] using hh
  have hRE : Nat.card R = Nat.card E := by
    rw [←card_map_of_injective S.subtype_injective (K := R),
      ←card_map_of_injective (alternatingGroup (Fin 7)).subtype_injective (K := E),
      subgroupOf_map_subtype,subgroupOf_map_subtype,inf_comm]
  have hprod := R.card_mul_index
  rw [hS,hRE] at hprod
  have hlo : 72 ≤ Nat.card E := by nlinarith
  have hhi : Nat.card E ≤ 144 := by
    rw [←hRE]
    exact (Nat.card_le_card_of_injective R.subtype R.subtype_injective).trans_eq hS
  let K := stabilizer A7 i
  have hEK : E ≤ K := fun g hg => hfix hg
  let J := E.subgroupOf K
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup K := (AlternatingSix.SmallIndex.pointEquiv i).isSimpleGroup
  have hK : Nat.card K = 360 := by
    rw [Nat.card_congr (AlternatingSix.SmallIndex.pointEquiv i).toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hJ : Nat.card J = Nat.card E := Nat.card_congr (subgroupOfEquivOfLe hEK).toEquiv
  have hindex : J.index ≤ 5 := by
    have hh := J.card_mul_index
    rw [hJ,hK] at hh
    nlinarith
  have he := Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt J (by
    have hh := Nat.factorial_le hindex
    rw [hK]
    norm_num [Nat.factorial] at hh ⊢
    omega)
  rw [he,card_top,hK] at hJ
  omega

private theorem D_fixes_last : D 7 ≤ stabilizer S7 (6 : Fin 7) := by
  apply (closure_le _).mpr
  rintro s ⟨i,hi,rfl⟩
  change pairSwap 7 i 6 = 6
  fin_cases i <;> decide

private theorem fixed_D {x : Fin 7} (hx : ∀ s ∈ D 7, s x = x) : x = 6 := by
  have h0 := hx _ (pairSwap_mem (n := 7) (m := 3) 0 (by decide))
  have h1 := hx _ (pairSwap_mem (n := 7) (m := 3) 1 (by decide))
  have h2 := hx _ (pairSwap_mem (n := 7) (m := 3) 2 (by decide))
  fin_cases x <;> simp_all [pairSwap,Equiv.swap_apply_def]

private theorem normalizer_fixes_last {g : S7} (hg : g ∈ normalizer (D 7 : Set S7)) :
    g 6 = 6 := by
  apply fixed_D
  intro s hs
  have ht := (mem_normalizer_iff''.mp hg s).mp hs
  have he := D_fixes_last ht
  change (g⁻¹ * s * g) 6 = 6 at he
  have hh := congrArg g he
  change g (g.symm (s (g 6))) = g 6 at hh
  simpa only [g.apply_symm_apply] using hh

private theorem swap_of_D {s : S7} (hs : s.IsSwap) (hD : s ∈ D 7) :
    ∃ i : Fin 3, s = pairSwap 7 i := by
  obtain ⟨x,y,hxy,rfl⟩ := hs
  have he := Odd.elementary_disjointTranspositions (Or.inr rfl : 7 = 5 ∨ 7 = 7) le_rfl
  let := he
  have hcomm : ∀ i : Fin 3, swap x y * pairSwap 7 i = pairSwap 7 i * swap x y := by
    intro i
    exact congrArg Subtype.val (mul_comm (⟨_,hD⟩ : D 7) ⟨_,pairSwap_mem i i.isLt⟩)
  have cert : ∀ x y : Fin 7, x ≠ y →
      (∀ i : Fin 3, swap x y * pairSwap 7 i = pairSwap 7 i * swap x y) →
      ∃ i : Fin 3, swap x y = pairSwap 7 i := by decide +kernel
  exact cert x y hxy hcomm

private theorem normalizer_pairs {g : S7} (hg : g ∈ normalizer (D 7 : Set S7)) :
    ∀ i : Fin 3, ∃ j : Fin 3, g * pairSwap 7 i * g⁻¹ = pairSwap 7 j := by
  intro i
  apply swap_of_D
  · let x : Fin 7 := ⟨2*i.val,by omega⟩
    let y : Fin 7 := ⟨2*i.val+1,by omega⟩
    exact ⟨g x,g y,g.injective.ne (by intro h; have := congrArg Fin.val h; dsimp [x,y] at this; omega),
      Equiv.symm_trans_swap_trans x y g⟩
  · exact (mem_normalizer_iff.mp hg _).mp (pairSwap_mem (n := 7) (m := 3) i i.isLt)

private theorem cubic_fixed {g : S7} (hg : g ∈ normalizer (D 7 : Set S7))
    (h3 : g ^ 3 = 1) (hne : g ≠ 1) : ∀ x, g x = x ↔ x = 6 := by
  have hnot3 : ¬ g.IsThreeCycle := by
    intro hc
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (by rw [hc.card_support]; decide)
    have he := hc.eq_swap_mul_swap_iff_mem_support.mpr hx
    have hp := normalizer_pairs hg
    rw [he] at hp
    have cert : ∀ x y z : Fin 7, x ≠ y → y ≠ z → x ≠ z →
        ¬ (∀ i : Fin 3, ∃ j : Fin 3,
          (swap x y * swap y z) * pairSwap 7 i * (swap x y * swap y z)⁻¹ = pairSwap 7 j) := by
      decide +kernel
    have hn := hc.nodup_iff_mem_support.mpr hx
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,
      List.nodup_nil,not_false_eq_true,and_true,not_or] at hn
    exact cert x (g x) (g (g x)) hn.1.1 hn.2 hn.1.2 hp
  have he : g.cycleType = Multiset.replicate g.cycleType.card 3 :=
    Multiset.eq_replicate_card.mpr (Perm.pow_prime_eq_one_iff.mp h3)
  have hb := g.sum_cycleType_le
  rw [he,Multiset.sum_replicate] at hb
  simp only [nsmul_eq_mul,Fintype.card_fin,Nat.cast_id] at hb
  have hc : g.cycleType.card = 2 := by
    have hzero : g.cycleType.card ≠ 0 := by
      intro hz
      apply hne
      apply Perm.cycleType_eq_zero.mp
      rw [he,hz,Multiset.replicate_zero]
    have hone : g.cycleType.card ≠ 1 := by
      intro ho
      apply hnot3
      change g.cycleType = {3}
      simpa only [ho,Multiset.replicate_one] using he
    omega
  have hfixed : Nat.card (Function.fixedPoints g) = 1 := by
    rw [Nat.card_eq_fintype_card,g.card_fixedPoints,he,hc]
    decide
  let := (Nat.card_eq_one_iff_unique.mp hfixed).1
  intro x
  constructor
  · intro hx
    exact congrArg Subtype.val (Subsingleton.elim
      (⟨x,hx⟩ : Function.fixedPoints g) ⟨6,normalizer_fixes_last hg⟩)
  · rintro rfl
    exact normalizer_fixes_last hg

/-- A cubic inside an elementary nine-group permuting with the full Sylow
cannot normalize the three-pair group normalized by that Sylow. -/
theorem plane_cubic_not_normalizes
    (P : Sylow 2 S7) (E C J : Subgroup S7) [IsElementaryAbelian 3 E]
    (hE : Nat.card E = 9) (hC : Nat.card C = 3) (hCE : C ≤ E)
    (hperm : (E : Set S7) * (P : Set S7) = (P : Set S7) * (E : Set S7))
    (g : S7) (hJ : J = (D 7).map (MulAut.conj g).toMonoidHom)
    (hPJ : (P : Subgroup S7) ≤ normalizer (J : Set S7)) :
    ¬ C ≤ normalizer (J : Set S7) := by
  have hcP : Nat.card P = 16 := by
    rw [P.card_eq_multiplicity,Nat.card_perm,Nat.card_fin]
    norm_num [Nat.factorial]
    rw [show (5040 : ℕ).factorization 2 = 4 by
      rw [show 5040 = 2^4*315 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),Nat.factorization_pow]
      simp [Nat.prime_two.factorization_self,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 315)]]
    norm_num
  have hdis := (IsElementaryAbelian.isPGroup 3 E).disjoint_of_coprime P.isPGroup' (by decide)
  have hEP : Nat.card (E ⊔ (P : Subgroup S7) : Subgroup S7) = 144 := by
    rw [card_sup_eq_mul_of_permutes_of_disjoint E (P : Subgroup S7) hperm hdis,hE,hcP]
  have hn (p : S7) (hp : p ∈ normalizer (J : Set S7)) :
      (MulAut.conj g⁻¹) p ∈ normalizer (D 7 : Set S7) := by
    rw [hJ,←map_equiv_normalizer_eq] at hp
    obtain ⟨x,hx,hxp⟩ := hp
    rw [←hxp]
    simpa [MulAut.conj_apply,mul_assoc] using hx
  have hfix (p : S7) (hp : p ∈ normalizer (J : Set S7)) : p (g 6) = g 6 := by
    have hh := congrArg g (normalizer_fixes_last (hn p hp))
    change g (g.symm (p (g 6))) = g 6 at hh
    simpa only [g.apply_symm_apply] using hh
  intro hCJ
  obtain ⟨c,hcne⟩ := ne_bot_iff_exists_ne_one.mp (show C ≠ ⊥ by
    intro he; rw [he,card_bot] at hC; omega)
  have hc := c.property
  have hcne : (c : S7) ≠ 1 := fun he => hcne (Subtype.ext he)
  have hcube : (c : S7) ^ 3 = 1 := by
    have hh := congrArg Subtype.val (pow_card_eq_one' (x := (⟨c.val,hc⟩ : C)))
    change c.val ^ Nat.card C = 1 at hh
    rwa [hC] at hh
  have hcfix : ∀ x, c.val x = x ↔ x = g 6 := by
    have hh := cubic_fixed (hn c.val (hCJ hc))
      (by rw [←map_pow,hcube,map_one])
      (fun he => hcne ((MulAut.conj g⁻¹).injective (he.trans (map_one _).symm)))
    intro x
    have he := hh (g.symm x)
    have hcancel : ((MulAut.conj g⁻¹) c.val) (g.symm x) = g.symm (c.val x) := by
      change g.symm (c.val (g (g.symm x))) = _
      rw [g.apply_symm_apply]
    rw [hcancel] at he
    constructor
    · intro hcx
      exact (g.apply_symm_apply x).symm.trans (congrArg g (he.mp (congrArg g.symm hcx)))
    · rintro rfl
      exact hfix c.val (hCJ hc)
  apply no_fixed_144 (E ⊔ (P : Subgroup S7)) hEP (g 6)
  apply sup_le
  · intro e he
    change e (g 6) = g 6
    apply (hcfix (e (g 6))).mp
    have hcomm := congrArg (fun z : E => (z : S7))
      (mul_comm (⟨c.val,hCE hc⟩ : E) ⟨e,he⟩)
    have hh := congrArg (fun z : S7 => z (g 6)) hcomm
    change c.val (e (g 6)) = e (c.val (g 6)) at hh
    rwa [hfix c.val (hCJ hc)] at hh
  · exact fun p hp => hfix p (hPJ hp)
end CFSG.Quasithin.ChapterB.Offenders.SevenNormalizer
