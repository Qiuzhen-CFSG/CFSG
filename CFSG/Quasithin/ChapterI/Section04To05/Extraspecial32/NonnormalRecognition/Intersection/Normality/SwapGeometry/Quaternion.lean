module

public import Theory.GroupTheory.QuaternionSplitBlockInvolutions.ActionTypes
public import Theory.GroupTheory.PGroup.ExtraspecialThirtyTwoElementaryAlternative
public import Theory.ElementaryAbelian.ExtraspecialAbelianBound

/-!
# The cubic-invariant eight in the swapping quaternion case

For the intrinsic central product Q₈ * Q₈, an involution swapping the factors
has an elementary-eight fixed subgroup D and makes every element commute
with its image. If another elementary eight E contains a noncentral fixed
involution s and is not centralized by the swap, then E and D are precisely
the two sources of involutions in C_Q(s).

A cubic inverted by the swap makes s, s^x and s^(x²) commute. Thus s^x lies
in E or D; the latter would centralize s under the cubic. When the cubic has
only central fixed points, its orbit and the center therefore generate E.
This establishes cubic invariance without an assumed orbit classification.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), Lemmas 2.3(a) and 2.6(1), pp.33–35.
-/

open Subgroup
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.SwapGeometry
variable {Q : Type*} [Group Q] [Finite Q]

private theorem card_le_sixteen_of_ne_top (hQ : Nat.card Q = 32)
    (K : Subgroup Q) (hne : K ≠ ⊤) : Nat.card K ≤ 16 := by
  have hi : 2 ≤ K.index := by
    have hp : 0 < K.index := by rw [index_eq_card]; exact Nat.card_pos
    have hn : K.index ≠ 1 := fun hh => hne (Subgroup.index_eq_one.mp hh)
    omega
  have hh := K.card_mul_index
  rw [hQ] at hh
  nlinarith

private theorem eq_eight_of_four_lt (E K : Subgroup Q) (hE : Nat.card E = 8)
    (hle : K ≤ E) (hlarge : 4 < Nat.card K) : K = E := by
  have hd := card_dvd_of_le hle
  rw [hE] at hd
  have hc : Nat.card K ≤ 8 := hE ▸ card_le_of_le hle
  apply eq_of_le_of_card_ge hle
  interval_cases hn : Nat.card K <;> norm_num at hd
  exact hE.le

/-- Two distinct elementary eights in a proper subgroup of an extraspecial
32-group are the only sources of involutions in their join. -/
private theorem square_one_mem_either
    [IsExtraspecial 2 Q] (hQ : Nat.card Q = 32)
    (E D : Subgroup Q) [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 D]
    (hE : Nat.card E = 8) (hD : Nat.card D = 8)
    (hne : E ≠ D) (hproper : E ⊔ D ≠ ⊤)
    {t : Q} (ht : t ∈ E ⊔ D) (ht2 : t^2 = 1) : t ∈ E ∨ t ∈ D := by
  obtain ⟨hEn, hZE⟩ :=
    IsExtraspecial.elementary_eight_normal_and_center_le_of_card_thirty_two hQ E hE
  let := hEn
  obtain ⟨hDn, _⟩ :=
    IsExtraspecial.elementary_eight_normal_and_center_le_of_card_thirty_two hQ D hD
  let := hDn
  have hN : D ≤ normalizer (E : Set Q) := by rw [E.normalizer_eq_top]; exact le_top
  have hmul := card_mul_eq_card_inf_mul_card_sup_of_normalizes E D hN
  rw [hE, hD] at hmul
  have hJ : Nat.card (E ⊔ D : Subgroup Q) = 16 := by
    have hu := card_le_sixteen_of_ne_top hQ (E ⊔ D) hproper
    have hd : 8 ∣ Nat.card (E ⊔ D : Subgroup Q) := hE ▸ card_dvd_of_le (show E ≤ E ⊔ D from le_sup_left)
    have hl : 8 ≤ Nat.card (E ⊔ D : Subgroup Q) := hE ▸ card_le_of_le (show E ≤ E ⊔ D from le_sup_left)
    have hn : Nat.card (E ⊔ D : Subgroup Q) ≠ 8 := by
      intro he
      have hEE : E = E ⊔ D := eq_of_le_of_card_ge le_sup_left (by rw [he,hE])
      have hDD : D = E ⊔ D := eq_of_le_of_card_ge le_sup_right (by rw [he,hD])
      exact hne (hEE.trans hDD.symm)
    obtain ⟨n, hn'⟩ := hd
    omega
  have hI : Nat.card (E ⊓ D : Subgroup Q) = 4 := by rw [hJ] at hmul; omega
  have hcE : centralizer (E : Set Q) = E :=
    extraspecial_two_centralizer_eq_of_card_sq E hZE (by rw [hE, hQ]; decide)
  have hp : t ∈ (E : Set Q) * (D : Set Q) := by
    rw [← coe_mul_of_right_le_normalizer_left E D hN]
    exact ht
  obtain ⟨e, he, d, hd, rfl⟩ := hp
  by_cases heD : e ∈ D
  · exact Or.inr (D.mul_mem heD hd)
  by_cases hdE : d ∈ E
  · exact Or.inl (E.mul_mem he hdE)
  have he2 : e^2 = 1 := elemPow_eq_one_of_isElementaryAbelian e he
  have hd2 : d^2 = 1 := elemPow_eq_one_of_isElementaryAbelian d hd
  have hcomm : e*d=d*e := by
    have hi : e⁻¹=e := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using he2)
    have hj : d⁻¹=d := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hd2)
    have hk : (e*d)⁻¹=e*d := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using ht2)
    simpa only [mul_inv_rev, hi, hj] using hk.symm
  have hgen : (E ⊓ D) ⊔ zpowers e = E := by
    apply eq_eight_of_four_lt _ _ hE (sup_le inf_le_left (zpowers_le.mpr he))
    have hl : 4 ≤ Nat.card ((E ⊓ D) ⊔ zpowers e : Subgroup Q) :=
      hI ▸ card_le_of_le (show E ⊓ D ≤ (E ⊓ D) ⊔ zpowers e from le_sup_left)
    have hn : Nat.card ((E ⊓ D) ⊔ zpowers e : Subgroup Q) ≠ 4 := by
      intro hh
      have hi : E ⊓ D = (E ⊓ D) ⊔ zpowers e :=
        eq_of_le_of_card_ge le_sup_left (by rw [hh, hI])
      exact heD ((hi.ge (mem_sup_right (mem_zpowers e))).2)
    omega
  have hdC : d ∈ centralizer (E : Set Q) := by
    have hle : E ≤ centralizer ({d} : Set Q) := by
      rw [← hgen]
      apply sup_le
      · intro y hy
        exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (mul_comm (⟨y, hy.2⟩ : D) ⟨d, hd⟩))
      · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hcomm)
    intro y hy
    exact mem_centralizer_singleton_iff.mp (hle hy)
  exact (hdE (hcE ▸ hdC)).elim

private theorem line_mem {s t : Q} (hs : s^2=1) (ht : t ∈ zpowers s) : t=1 ∨ t=s := by
  by_cases hs1 : s=1
  · simpa [hs1] using ht
  have ho : orderOf s = 2 := orderOf_eq_prime hs hs1
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, ho] at ht
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ht
  have hnlt := Finset.mem_range.mp hn
  interval_cases n <;> simp

private theorem cubic_image_not_line (d : QuaternionCentralProductData Q)
    (b : MulAut Q) (hb : b^3=1)
    (hfixed : ∀ q, b q=q → q ∈ center Q)
    (s : Q) (hs : s^2=1) (hsZ : s ∉ center Q) :
    b s ∉ center Q ⊔ zpowers s := by
  intro hm
  obtain ⟨z, hz, t, ht, he⟩ := mem_sup_of_normal_left.mp hm
  have hbs : b s = z*t := he.symm
  have hzfix : b z=z := d.fixes_center b ⟨z,hz⟩
  have hcube : b (b (b s))=s := by
    simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply]
      using DFunLike.congr_fun hb s
  apply hsZ
  apply hfixed
  rcases line_mem hs ht with ht1 | hts
  · rw [ht1] at hbs
    simp only [mul_one] at hbs
    apply b.injective
    rw [hbs, hzfix]
  · rw [hts] at hbs
    have hsecond : b (b s)=s := by
      rw [hbs, map_mul, hzfix, hbs, ← mul_assoc,
        ← pow_two, show z^2=1 from congrArg Subtype.val (d.center_square ⟨z,hz⟩), one_mul]
    rwa [hsecond] at hcube

private theorem center_line_card (d : QuaternionCentralProductData Q)
    (s : Q) (hs : s^2=1) (hsZ : s ∉ center Q) :
    Nat.card (center Q ⊔ zpowers s : Subgroup Q) = 4 := by
  have hs1 : s ≠ 1 := fun hh => hsZ (hh ▸ (center Q).one_mem)
  have ho : orderOf s=2 := orderOf_eq_prime hs hs1
  have hdisj : Disjoint (center Q) (zpowers s) := by
    apply disjoint_iff.mpr
    apply le_antisymm ?_ bot_le
    intro t ht
    rcases line_mem hs ht.2 with he | he
    · exact he
    · exact (hsZ (he ▸ ht.1)).elim
  have hn : zpowers s ≤ normalizer (center Q : Set Q) := by
    rw [(center Q).normalizer_eq_top]; exact le_top
  rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn hdisj,
    d.center_card, Nat.card_zpowers, ho]

/-- The intrinsic part of source 2.6(1): the noncentralized eight through a
fixed noncentral involution is preserved by an inverted fixed-free cubic. -/
public theorem eight_invariant (d : QuaternionCentralProductData Q)
    (E : Subgroup Q) [IsElementaryAbelian 2 E] (hE : Nat.card E=8)
    (a b : MulAut Q) (ha : a^2=1) (hswap : d.left.map a.toMonoidHom=d.right)
    (hmove : ∃ e ∈ E, a e ≠ e)
    (hb : b^3=1) (hinv : a*b*a⁻¹=b⁻¹)
    (hfixed : ∀ q, b q=q → q ∈ center Q)
    (s : Q) (hsE : s ∈ E) (hsa : a s=s) (hsZ : s ∉ center Q) :
    E.map b.toMonoidHom=E := by
  let := d.extraspecial
  obtain ⟨hEn, hZE⟩ :=
    IsExtraspecial.elementary_eight_normal_and_center_le_of_card_thirty_two d.card E hE
  let := hEn
  let D := a.toMonoidHom.eqLocus (MonoidHom.id Q)
  let θ : d.left ≃* d.right := (a.subgroupMap d.left).trans (MulEquiv.subgroupCongr hswap)
  have hdiag : D = quaternionDiagonal d.left d.right θ d.commute :=
    quaternion_diagonal_eq_fixed_of_involution_swap d.left d.right θ d.intersection_card
      d.commute d.span a ha (fun _ => rfl)
  have hde := quaternion_diagonal_elementary_eight d.left d.right d.left_model.some θ
    d.intersection_card d.commute
  let : IsElementaryAbelian 2 D := hdiag ▸ hde.1
  have hD : Nat.card D=8 := hdiag ▸ hde.2.1
  have hne : E ≠ D := by
    intro he
    obtain ⟨e, heE, hem⟩ := hmove
    have heD : e ∈ D := he ▸ heE
    exact hem heD
  have hs2 : s^2=1 := elemPow_eq_one_of_isElementaryAbelian s hsE
  have hsD : s ∈ D := hsa
  let C := centralizer ({s} : Set Q)
  have hJC : E ⊔ D ≤ C := by
    apply sup_le
    · intro e he
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mul_comm (⟨e,he⟩ : E) ⟨s,hsE⟩))
    · intro e he
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mul_comm (⟨e,he⟩ : D) ⟨s,hsD⟩))
  have hCproper : C ≠ ⊤ := by
    intro he
    apply hsZ
    exact mem_center_iff.mpr fun q => mem_centralizer_singleton_iff.mp (show q ∈ C from he.symm ▸ mem_top q)
  have hproper : E ⊔ D ≠ ⊤ := fun he => hCproper (top_unique (he ▸ hJC))
  have hJ : E ⊔ D = C := by
    apply eq_of_le_of_card_ge hJC
    have hC := card_le_sixteen_of_ne_top d.card C hCproper
    have hd : 8 ∣ Nat.card (E ⊔ D : Subgroup Q) :=
      hE ▸ card_dvd_of_le (show E ≤ E ⊔ D from le_sup_left)
    have hl : 8 ≤ Nat.card (E ⊔ D : Subgroup Q) :=
      hE ▸ card_le_of_le (show E ≤ E ⊔ D from le_sup_left)
    have hn : Nat.card (E ⊔ D : Subgroup Q) ≠ 8 := by
      intro he
      exact hne ((eq_of_le_of_card_ge (show E ≤ E ⊔ D from le_sup_left) (by rw [he,hE])).trans
        (eq_of_le_of_card_ge (show D ≤ E ⊔ D from le_sup_right) (by rw [he,hD])).symm)
    obtain ⟨n, hn'⟩ := hd
    omega
  have hb3 (q : Q) : b (b (b q))=q := by
    simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply]
      using DFunLike.congr_fun hb q
  have hbInv : b⁻¹=b^2 := by
    symm
    apply mul_eq_one_iff_eq_inv.mp
    rw [← pow_succ, hb]
  have hab : a (b s) = b (b s) := by
    have hh := DFunLike.congr_fun (mul_inv_eq_iff_eq_mul.mp hinv) s
    simpa only [MulAut.mul_apply, hsa, hbInv, pow_two] using hh
  have hcommAll (q : Q) : Commute q (a q) := by
    have hh := ((d.isA2Action_iff_source a).mp (d.isA2Action_of_swap a ha hswap)).2.2
      (QuotientGroup.mk' (center Q) q)
    rw [quotientAut_apply_mk, d.polarBilin_mk, d.centerCoordinate_eq_zero_iff] at hh
    exact commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val hh)
  have h12 : Commute (b s) (b (b s)) := by simpa only [hab] using hcommAll (b s)
  have h02 : Commute (b (b s)) s := by
    change b (b s) * s = s * b (b s)
    simpa only [map_mul, hb3] using congrArg b h12.eq
  have h01 : Commute s (b s) := by
    change s * b s = b s * s
    simpa only [map_mul, hb3] using congrArg b h02.eq
  have hbsE : b s ∈ E := by
    have hbsC : b s ∈ C := mem_centralizer_singleton_iff.mpr h01.symm.eq
    have hbs2 : (b s)^2=1 := by rw [← map_pow, hs2, map_one]
    rcases square_one_mem_either d.card E D hE hD hne hproper (hJ.symm ▸ hbsC) hbs2 with he | hd
    · exact he
    · have hh : b (b s)=b s := hab.symm.trans hd
      have hf : b s=s := b.injective hh
      exact (hsZ (hfixed s hf)).elim
  have hgen : (center Q ⊔ zpowers s) ⊔ zpowers (b s)=E := by
    apply eq_eight_of_four_lt _ _ hE
      (sup_le (sup_le hZE (zpowers_le.mpr hsE)) (zpowers_le.mpr hbsE))
    have hK := center_line_card d s hs2 hsZ
    have hl : 4 ≤ Nat.card ((center Q ⊔ zpowers s) ⊔ zpowers (b s) : Subgroup Q) :=
      hK ▸ card_le_of_le (show center Q ⊔ zpowers s ≤ _ from le_sup_left)
    have hn : Nat.card ((center Q ⊔ zpowers s) ⊔ zpowers (b s) : Subgroup Q) ≠ 4 := by
      intro hh
      have he : center Q ⊔ zpowers s = (center Q ⊔ zpowers s) ⊔ zpowers (b s) :=
        eq_of_le_of_card_ge le_sup_left (by rw [hh,hK])
      exact cubic_image_not_line d b hb hfixed s hs2 hsZ (he.ge (mem_sup_right (mem_zpowers (b s))))
    omega
  have hnorm : s * b s * b (b s) ∈ center Q := by
    apply hfixed
    rw [map_mul, map_mul, hb3, mul_assoc, h02.eq, ← mul_assoc, h01.eq]
  have hbbs : b (b s) ∈ E := by
    have hh := E.mul_mem (E.inv_mem (E.mul_mem hsE hbsE)) (hZE hnorm)
    simpa only [inv_mul_cancel_left] using hh
  apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective b.injective])
  rw [← hgen, Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  apply sup_le (sup_le ?_ ?_) ?_
  · rintro _ ⟨q,hq,rfl⟩
    change b q ∈ _
    rw [d.fixes_center b ⟨q,hq⟩]
    exact mem_sup_left (mem_sup_left hq)
  · exact zpowers_le.mpr (mem_sup_right (mem_zpowers (b s)))
  · exact zpowers_le.mpr (hgen.symm ▸ hbbs)

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.SwapGeometry
