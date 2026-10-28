module

public import Theory.GroupTheory.PGroup.AbelianIndexThreeCount
public import Theory.GroupTheory.PGroup.AbelianIndexThreeAction
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.FinCases

/-!
# Exact cardinality of the abelian index-three family

If a nonabelian finite three-group has two distinct abelian subgroups of index
three, their intersection is the center, of index nine. Choose noncentral
elements `a` and `b` in these two subgroups. Adjoining `a * b` and `a * b⁻¹`
to the center gives two further abelian subgroups of index three. All four
are distinct, so the existing upper bound gives exactly four members.
The family can also be empty or have just one member.

This finite-group lemma supplies the cardinality premise in the SL₃ three-core
argument supporting GLS4, Chapter 4, Lemma 3.11(a)
(`refs/KGroup/GLS4/Chapter4.tex`, lines 585–603). The related degree-three
automizer assertion is Aschbacher–Smith, A.3.21(c), printed pp.55–56
of `refs/quasithin.pdf`; the counting lemma does not assert that full result.
-/

namespace Subgroup

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem isMulCommutative_center_sup_zpowers (x : G) :
    IsMulCommutative (center G ⊔ zpowers x : Subgroup G) := by
  have hzx : zpowers x ≤ centralizer (center G : Set G) := by
    apply le_centralizer_iff.mpr
    exact center_le_centralizer _
  apply le_centralizer_iff_isMulCommutative.mp
  apply sup_le
  · exact center_le_centralizer _
  · apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp hzx) (zpowers x).le_centralizer

private theorem index_three_center_sup_zpowers
    (hn : ¬ IsMulCommutative G)
    (hzi : (center G).index = 9) {x : G} (hx : x ∉ center G) :
    (center G ⊔ zpowers x : Subgroup G).index = 3 := by
  let C : Subgroup G := center G ⊔ zpowers x
  have hCcomm : IsMulCommutative C := by
    simpa only [C] using isMulCommutative_center_sup_zpowers x
  have hCtop : C ≠ ⊤ := by
    intro htop
    apply hn
    refine ⟨⟨fun a b => ?_⟩⟩
    let aa : C := ⟨a, by rw [htop]; exact mem_top _⟩
    let bb : C := ⟨b, by rw [htop]; exact mem_top _⟩
    exact congrArg Subtype.val (hCcomm.is_comm.comm aa bb)
  have hCcenter : center G ≤ C := le_sup_left
  have hCcenter_ne : center G ≠ C := by
    intro he
    apply hx
    exact he ▸ (le_sup_right : zpowers x ≤ C) (mem_zpowers x)
  have hCcenter_lt : center G < C := lt_of_le_of_ne hCcenter hCcenter_ne
  have hCgt : 1 < C.index := one_lt_index_of_ne_top hCtop
  have hClt : C.index < (center G).index := index_strictAnti hCcenter_lt
  have hCdiv : C.index ∣ (center G).index := index_dvd_of_le hCcenter
  have hCdiv9 : C.index ∣ 9 := hzi ▸ hCdiv
  have hCdivpow : C.index ∣ 3 ^ 2 := by norm_num at hCdiv9 ⊢; exact hCdiv9
  obtain ⟨k, hk, hkC⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hCdivpow
  change C.index = 3
  rw [hkC]
  interval_cases k <;> omega

/-- The abelian index-three family of a nonabelian finite three-group has at
most one member or exactly four members; nonemptiness is not required. -/
public theorem card_abelianIndexThree_le_one_or_eq_four
    (hG : IsPGroup 3 G) (hn : ¬ IsMulCommutative G) :
    Nat.card (AbelianIndexThree G) ≤ 1 ∨
      Nat.card (AbelianIndexThree G) = 4 := by
  classical
  let F := AbelianIndexThree G
  by_cases hs : Subsingleton F
  · left
    let : Subsingleton F := hs
    have hle : Nat.card F ≤ 1 := by
      simpa using Nat.card_le_card_of_injective (fun _ : F => ())
        (fun x y _ => Subsingleton.elim x y)
    exact hle
  · right
    have hupper : Nat.card F ≤ 4 := by
      simpa [F, AbelianIndexThree] using card_abelian_index_three_le_four hG hn
    have : Nontrivial F := not_subsingleton_iff_nontrivial.mp hs
    obtain ⟨A, B, hAB⟩ := exists_pair_ne F
    have hABval : A.val ≠ B.val := fun h => hAB (Subtype.ext h)
    have hzi := center_index_eq_nine_of_distinct_abelian_index_three hG hn
      A.val B.val A.property.1 B.property.1 A.property.2 B.property.2 hABval
    have hZA : center G < A.val := by
      apply lt_of_le_of_ne
        (center_le_of_abelian_index_three hG hn A.val A.property.1 A.property.2)
      intro he
      have := congrArg Subgroup.index he
      rw [hzi, A.property.2] at this
      omega
    have hZB : center G < B.val := by
      apply lt_of_le_of_ne
        (center_le_of_abelian_index_three hG hn B.val B.property.1 B.property.2)
      intro he
      have := congrArg Subgroup.index he
      rw [hzi, B.property.2] at this
      omega
    obtain ⟨a, haA, haZ⟩ := SetLike.exists_of_lt hZA
    obtain ⟨b, hbB, hbZ⟩ := SetLike.exists_of_lt hZB
    have hbA : b ∉ A.val := by
      intro hbA
      apply hbZ
      have hab : b ∈ A.val ⊓ B.val := ⟨hbA, hbB⟩
      rw [inf_eq_center_of_distinct_abelian_index_three hG hn A.val B.val
        A.property.1 B.property.1 A.property.2 B.property.2 hABval] at hab
      exact hab
    have haB : a ∉ B.val := by
      intro haB
      apply haZ
      have hab : a ∈ A.val ⊓ B.val := ⟨haA, haB⟩
      rw [inf_eq_center_of_distinct_abelian_index_three hG hn A.val B.val
        A.property.1 B.property.1 A.property.2 B.property.2 hABval] at hab
      exact hab
    let xplus : G := a * b
    let xminus : G := a * b⁻¹
    have hxplusZ : xplus ∉ center G := by
      intro hx
      apply hbA
      have hxa : xplus ∈ A.val := (center_le_of_abelian_index_three hG hn A.val
        A.property.1 A.property.2) hx
      exact by simpa [xplus, mul_assoc] using A.val.mul_mem (A.val.inv_mem haA) hxa
    have hxminusZ : xminus ∉ center G := by
      intro hx
      apply hbA
      have hxa : xminus ∈ A.val := (center_le_of_abelian_index_three hG hn A.val
        A.property.1 A.property.2) hx
      have hbinvA : b⁻¹ ∈ A.val := by
        simpa [xminus, mul_assoc] using A.val.mul_mem (A.val.inv_mem haA) hxa
      simpa only [inv_inv] using A.val.inv_mem hbinvA
    have hxplusB : xplus ∉ B.val := by
      intro hx
      apply haB
      simpa [xplus] using B.val.mul_mem hx (B.val.inv_mem hbB)
    have hxminusB : xminus ∉ B.val := by
      intro hx
      apply haB
      simpa [xminus] using B.val.mul_mem hx hbB
    have hxplusA : xplus ∉ A.val := by
      intro hx
      apply hbA
      simpa [xplus, mul_assoc] using A.val.mul_mem (A.val.inv_mem haA) hx
    have hxminusA : xminus ∉ A.val := by
      intro hx
      apply hbA
      have hbinvA : b⁻¹ ∈ A.val := by
        simpa [xminus, mul_assoc] using A.val.mul_mem (A.val.inv_mem haA) hx
      simpa only [inv_inv] using A.val.inv_mem hbinvA
    let C : Subgroup G := center G ⊔ zpowers xplus
    let D : Subgroup G := center G ⊔ zpowers xminus
    have hCi : C.index = 3 := by
      simpa only [C] using index_three_center_sup_zpowers hn hzi hxplusZ
    have hDi : D.index = 3 := by
      simpa only [D] using index_three_center_sup_zpowers hn hzi hxminusZ
    have hCc : IsMulCommutative C := by
      simpa only [C] using isMulCommutative_center_sup_zpowers xplus
    have hDc : IsMulCommutative D := by
      simpa only [D] using isMulCommutative_center_sup_zpowers xminus
    have hCA : C ≠ A.val := by
      intro he
      apply hxplusA
      rw [← he]
      exact (le_sup_right : zpowers xplus ≤ C) (mem_zpowers xplus)
    have hCB : C ≠ B.val := by
      intro he
      apply hxplusB
      rw [← he]
      exact (le_sup_right : zpowers xplus ≤ C) (mem_zpowers xplus)
    have hDA : D ≠ A.val := by
      intro he
      apply hxminusA
      rw [← he]
      exact (le_sup_right : zpowers xminus ≤ D) (mem_zpowers xminus)
    have hDB : D ≠ B.val := by
      intro he
      apply hxminusB
      rw [← he]
      exact (le_sup_right : zpowers xminus ≤ D) (mem_zpowers xminus)
    let A' : F := A
    let B' : F := B
    let C' : F := ⟨C, hCc, hCi⟩
    let D' : F := ⟨D, hDc, hDi⟩
    have hAB' : A' ≠ B' := by simpa [A', B'] using hAB
    have hAC' : A' ≠ C' := by
      intro h
      exact hCA (congrArg Subtype.val h).symm
    have hAD' : A' ≠ D' := by
      intro h
      exact hDA (congrArg Subtype.val h).symm
    have hBC' : B' ≠ C' := by
      intro h
      exact hCB (congrArg Subtype.val h).symm
    have hBD' : B' ≠ D' := by
      intro h
      exact hDB (congrArg Subtype.val h).symm
    have hCD : C ≠ D := by
      intro hCD
      let : D.Normal := normal_of_index_three_of_isPGroup hG D hDi
      let r : G →* (G ⧸ D) := QuotientGroup.mk' D
      have hxplusD : xplus ∈ D := by
        rw [← hCD]
        exact (le_sup_right : zpowers xplus ≤ C) (mem_zpowers xplus)
      have hrplus : r xplus = 1 := by
        apply (QuotientGroup.eq_one_iff xplus).2
        exact hxplusD
      have hrminus : r xminus = 1 := by
        apply (QuotientGroup.eq_one_iff xminus).2
        exact (le_sup_right : zpowers xminus ≤ D) (mem_zpowers xminus)
      have h1 : r a * r b = 1 := by
        calc
          r a * r b = r (a * b) := (map_mul r a b).symm
          _ = 1 := by simpa [xplus] using hrplus
      have h2 : r a * (r b)⁻¹ = 1 := by
        calc
          r a * (r b)⁻¹ = r (a * b⁻¹) := by rw [map_mul, map_inv]
          _ = 1 := by simpa [xminus] using hrminus
      have hra1 : r a = (r b)⁻¹ := eq_inv_of_mul_eq_one_left h1
      have hra2 : r a = r b := by
        simpa using (eq_inv_of_mul_eq_one_left h2)
      have hrbinv : (r b)⁻¹ = r b := hra1.symm.trans hra2
      have hrb2 : (r b) ^ 2 = 1 := by
        calc
          (r b) ^ 2 = (r b) * (r b) := pow_two _
          _ = (r b)⁻¹ * (r b) := by rw [hrbinv]
          _ = 1 := inv_mul_cancel _
      have hcardQ : Nat.card (G ⧸ D) = 3 := by
        rw [← D.index_eq_card, hDi]
      have ho2 : orderOf (r b) ∣ 2 := orderOf_dvd_of_pow_eq_one hrb2
      have ho3 : orderOf (r b) ∣ 3 := by
        have h := _root_.orderOf_dvd_natCard (r b)
        rw [hcardQ] at h
        exact h
      have ho1 : orderOf (r b) = 1 :=
        Nat.eq_one_of_dvd_coprimes (by decide) ho2 ho3
      have hrb : r b = 1 := orderOf_eq_one_iff.mp ho1
      have hra : r a = 1 := by rw [hra2, hrb]
      have haD : a ∈ D := (QuotientGroup.eq_one_iff a).1 hra
      have hAD := inf_eq_center_of_distinct_abelian_index_three hG hn A.val D
        A.property.1 hDc A.property.2 hDi hDA.symm
      apply haZ
      rw [← hAD]
      exact ⟨haA, haD⟩
    have hCD' : C' ≠ D' := by
      intro h
      exact hCD (congrArg Subtype.val h)
    let f : Fin 4 → F := fun i =>
      if i.val = 0 then A' else if i.val = 1 then B' else if i.val = 2 then C' else D'
    have hf : Function.Injective f := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> dsimp [f] at hij ⊢
      all_goals first
        | rfl
        | exact (hAB' hij).elim
        | exact (hAB' hij.symm).elim
        | exact (hAC' hij).elim
        | exact (hAC' hij.symm).elim
        | exact (hAD' hij).elim
        | exact (hAD' hij.symm).elim
        | exact (hBC' hij).elim
        | exact (hBC' hij.symm).elim
        | exact (hBD' hij).elim
        | exact (hBD' hij.symm).elim
        | exact (hCD' hij).elim
        | exact (hCD' hij.symm).elim
    have hlow : 4 ≤ Nat.card F := by
      simpa using Nat.card_le_card_of_injective f hf
    have hlow' : 4 ≤ Nat.card (AbelianIndexThree G) := by simpa [F] using hlow
    have hupper' : Nat.card (AbelianIndexThree G) ≤ 4 := by simpa [F] using hupper
    omega

end Subgroup
