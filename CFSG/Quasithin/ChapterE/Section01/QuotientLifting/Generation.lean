module

public import CFSG.Quasithin.ChapterE.Section01.QuotientLifting.OddSections
public import Theory.GroupTheory.SolvableMinimalNormal
public import FeitThompson.FinalTheorem

/-!
# Generation across a two-closed normal kernel

We prove E.1.10(8) by induction on the group order. An abelian minimal normal
p-subgroup of the solvable kernel gives a smaller quotient. E.1.10(7), together
with the Sylow supplement to each two-residual, lifts quotient generation.
For odd p, the hyperplane argument of E.1.10(6) puts [U,A] in E1. If this is
nontrivial, minimal normality absorbs U. If A centralizes U and G=JU, then
[G,A] lies in J, so the full residual action and the Sylow supplement give
G=J. For p=2, U already lies in the prescribed Sylow subgroup.

The induction only requires a solvable kernel and O²(G)=[O²(G),A]. The source
hypotheses supply these: a finite two-closed group is solvable by the odd-order
theorem, and O²(G)=G∞=[G∞,A] supplies the residual identity. The final theorem
retains all of the source hypotheses and the literal E1 family.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.10(8), printed pp.211--212.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]

private theorem minimal_normal_supplement_eq_top
    (T : Sylow 2 G) (A H U : Subgroup G) [U.Normal]
    [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    (hTH : (T : Subgroup G) ≤ H) (hEH : eSubgroup 1 (T : Subgroup G) A ≤ H)
    (hcomm : pResidual 2 G = ⁅pResidual 2 G,A⁆)
    (hcover : H ⊔ U = ⊤) {p : ℕ} [Fact p.Prime]
    (hpU : IsPGroup p U) [IsMulCommutative U]
    (hmin : ∀ V : Subgroup G, V.Normal → V ≤ U → V = ⊥ ∨ V = U) : H = ⊤ := by
  have hfinish (hUH : U ≤ H) : H = ⊤ := by simpa only [sup_eq_left.mpr hUH] using hcover
  by_cases hp : p = 2
  · subst p
    exact hfinish ((hpU.le_sylow_of_normal T).trans hTH)
  have hcH : ⁅U,A⁆ ≤ H :=
    (odd_normal_commutator_le_eSubgroup_one hp T U A hpU hAT).trans hEH
  by_cases hc : ⁅U,A⁆ = ⊥
  · have hUA : U ≤ centralizer (A : Set G) := commutator_eq_bot_iff_le_centralizer.mp hc
    have hAH : A ≤ H := hAT.trans hTH
    have hR : pResidual 2 G ≤ H := by
      rw [hcomm]
      apply commutator_le.mpr
      intro g _ a ha
      obtain ⟨h, hh, u, hu, rfl⟩ := mem_sup_of_normal_right.mp
        (show g ∈ H ⊔ U by rw [hcover]; trivial)
      have he : ⁅u,a⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr ((hUA hu) a ha).symm
      rw [commutatorElement_mul_left_eq_conj_mul, he, mul_one, mul_inv_cancel, one_mul]
      exact H.mul_mem (H.mul_mem (H.mul_mem hh (hAH ha))
        (H.inv_mem hh)) (H.inv_mem (hAH ha))
    apply top_unique
    rw [← pResidual_sup_sylow_eq_top T]
    exact sup_le hR hTH
  · have hn : (U ⊓ H).Normal := by
      apply normalizer_eq_top_iff.mp
      apply top_unique
      rw [← hcover]
      apply sup_le
      · exact (le_inf (by rw [normalizer_eq_top]; exact le_top) H.le_normalizer).trans
          inf_normalizer_le_normalizer_inf
      · exact ((le_centralizer_iff_isMulCommutative.mpr (inferInstance : IsMulCommutative U)).trans
          (centralizer_le inf_le_left)).trans (centralizer_le_normalizer _)
    rcases hmin (U ⊓ H) hn inf_le_left with he | he
    · exact False.elim (hc (le_bot_iff.mp
        ((le_inf (commutator_le_left U A) hcH).trans he.le)))
    · exact hfinish (he.symm.le.trans inf_le_right)
/-- Generation across a solvable normal kernel under the full residual action. -/
theorem sup_eSubgroup_eq_top_of_solvable_normal_supplement
    (T : Sylow 2 G) (A Y J : Subgroup G) [Y.Normal] [Group.IsSolvable Y]
    [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    (hTJ : (T : Subgroup G) ≤ J) (hcover : J ⊔ Y = ⊤)
    (hcomm : pResidual 2 G = ⁅pResidual 2 G,A⁆) :
    J ⊔ eSubgroup 1 (T : Subgroup G) A = ⊤ := by
  classical
  induction hn : Nat.card G using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases hY : Y = ⊥
    · rw [hY, sup_bot_eq] at hcover
      rw [hcover, top_sup_eq]
    obtain ⟨U, p, hUn, hUne, _hUY, hp, hUcomm, hpU, hmin⟩ :=
      exists_minimal_normal_abelian_pGroup Y hY
    let _ := hUn
    let _ := hUcomm
    let _ : Fact p.Prime := ⟨hp⟩
    let _ : Nontrivial U := (nontrivial_iff_ne_bot U).mpr hUne
    let q := QuotientGroup.mk' U
    have hq := QuotientGroup.mk'_surjective U
    let Tbar := T.mapSurjective (f := q) hq
    let _ : (Y.map q).Normal := Normal.map inferInstance q hq
    let _ : Group.IsSolvable (Y.map q) :=
      Group.isSolvable_of_surjective (q.subgroupMap_surjective Y)
    let _ : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map q
    have hlt : Nat.card (G ⧸ U) < n := by
      have hc : Nat.card U * Nat.card (G ⧸ U) = Nat.card G := U.card_mul_index
      have hUbig : 1 < Nat.card U := Finite.one_lt_card
      have hQpos : 0 < Nat.card (G ⧸ U) := Nat.card_pos
      nlinarith
    have hcoverbar : J.map q ⊔ Y.map q = ⊤ := by
      rw [← Subgroup.map_sup, hcover, map_top_of_surjective q hq]
    have hcommbar : pResidual 2 (G ⧸ U) = ⁅pResidual 2 (G ⧸ U),A.map q⁆ := by
      simpa only [map_commutator, map_pResidual_of_surjective 2 q hq] using
        congrArg (map q) hcomm
    have hind := ih _ hlt Tbar (A.map q) (Y.map q) (J.map q)
      (map_mono hAT) (map_mono hTJ) hcoverbar hcommbar rfl
    let H := J ⊔ eSubgroup 1 (T : Subgroup G) A
    have hEH : eSubgroup 1 (T : Subgroup G) A ≤ H := le_sup_right
    have hTH : (T : Subgroup G) ≤ H := hTJ.trans le_sup_left
    have hmap : H.map q = ⊤ := by
      apply top_unique
      rw [← hind]
      exact sup_le (map_mono le_sup_left)
        ((quotient_eSubgroup_le_map_sup_sylow T A U hAT).trans
          (map_mono (sup_le hEH hTH)))
    have hHU : H ⊔ U = ⊤ := by
      have he := congrArg (comap q) hmap
      simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using he
    exact minimal_normal_supplement_eq_top T A H U hAT hTH hEH hcomm hHU hpU hmin

/-- A finite two-closed group is solvable, by its two-core and odd-order quotient. -/
theorem IsTwoClosed.isSolvable (h : IsTwoClosed G) : Group.IsSolvable G := by
  obtain ⟨S, hS⟩ := h
  let _ := hS
  let _ : Group.IsSolvable S := @IsNilpotent.to_isSolvable _ _ S.isPGroup'.isNilpotent
  let _ : Group.IsSolvable (G ⧸ (S : Subgroup G)) := odd_order_theorem _
    (Nat.not_even_iff_odd.mp (fun he => S.not_dvd_index (even_iff_two_dvd.mp he)))
  exact (Group.isSolvable_iff_subgroup_quotient (S : Subgroup G)).mpr ⟨inferInstance, inferInstance⟩

/-- E.1.10(8): a two-closed normal supplement is absorbed by J and E1. -/
theorem sup_eSubgroup_one_eq_top_of_twoClosed
    (T : Sylow 2 G) (A Y J : Subgroup G) [Y.Normal]
    [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    (hres : pResidual 2 G = solvableResidual G)
    (hcomm : solvableResidual G = ⁅solvableResidual G,A⁆)
    (hY : IsTwoClosed Y) (hTJ : (T : Subgroup G) ≤ J) (hcover : J ⊔ Y = ⊤) :
    J ⊔ eSubgroup 1 (T : Subgroup G) A = ⊤ := by
  let _ : Group.IsSolvable Y := hY.isSolvable
  exact sup_eSubgroup_eq_top_of_solvable_normal_supplement T A Y J hAT hTJ hcover
    (by simpa only [hres] using hcomm)

end CFSG.Quasithin.ChapterE
