module
public import Stellmacher.Recognition.LyonsU3Four.BrauerLocalInvolutionPairing
public import Stellmacher.Recognition.LyonsU3Four.InvolutionFusion
public import Stellmacher.Recognition.LyonsU3Four.LocalFiveSectionSupport
/-! Actual centralizer involution sums for Lyons's local table. -/
public section
noncomputable section
set_option maxHeartbeats 5000000
namespace Stellmacher.Recognition.LyonsU3Four
open scoped BigOperators
open Theory.Character
attribute [local instance] Fintype.ofFinite Classical.propDecidable
variable {G : Type*} [Group G] [Finite G]
variable {H : Type*} [Group H] [Finite H]
private theorem three_involution_sum
    (a b c : H) (ha : orderOf a = 2) (hb : orderOf b = 2) (hc : orderOf c = 2)
    (hcover : ∀ u : H, orderOf u = 2 → IsConj u a ∨ IsConj u b ∨ IsConj u c)
    (hsepab : ¬ IsConj a b) (hsepac : ¬ IsConj a c) (hsepbc : ¬ IsConj b c)
    (f : ClassFunction H) (hf : IsClassFunction f) :
    involutionSum f =
      (Nat.card H : ℂ) / Nat.card (Subgroup.centralizer ({a} : Set H)) * f a +
      (Nat.card H : ℂ) / Nat.card (Subgroup.centralizer ({b} : Set H)) * f b +
      (Nat.card H : ℂ) / Nat.card (Subgroup.centralizer ({c} : Set H)) * f c := by
  let A : Finset H := Finset.univ.filter (fun x => ConjClasses.mk x = ConjClasses.mk a)
  let B : Finset H := Finset.univ.filter (fun x => ConjClasses.mk x = ConjClasses.mk b)
  let C : Finset H := Finset.univ.filter (fun x => ConjClasses.mk x = ConjClasses.mk c)
  have hAinv : ∀ x ∈ A, orderOf x = 2 := by
    intro x hx
    have hx' : ConjClasses.mk x = ConjClasses.mk a := by simpa [A] using hx
    have hx'' : IsConj x a := ConjClasses.mk_eq_mk_iff_isConj.mp hx'
    obtain ⟨g, hg⟩ := isConj_iff.mp hx''
    have ho := (MulAut.conj g).orderOf_eq x
    change orderOf (g * x * g⁻¹) = orderOf x at ho
    rw [hg] at ho
    exact ho.symm.trans ha
  have hBinv : ∀ x ∈ B, orderOf x = 2 := by
    intro x hx
    have hx' : ConjClasses.mk x = ConjClasses.mk b := by simpa [B] using hx
    have hx'' : IsConj x b := ConjClasses.mk_eq_mk_iff_isConj.mp hx'
    obtain ⟨g, hg⟩ := isConj_iff.mp hx''
    have ho := (MulAut.conj g).orderOf_eq x
    change orderOf (g * x * g⁻¹) = orderOf x at ho
    rw [hg] at ho
    exact ho.symm.trans hb
  have hCinv : ∀ x ∈ C, orderOf x = 2 := by
    intro x hx
    have hx' : ConjClasses.mk x = ConjClasses.mk c := by simpa [C] using hx
    have hx'' : IsConj x c := ConjClasses.mk_eq_mk_iff_isConj.mp hx'
    obtain ⟨g, hg⟩ := isConj_iff.mp hx''
    have ho := (MulAut.conj g).orderOf_eq x
    change orderOf (g * x * g⁻¹) = orderOf x at ho
    rw [hg] at ho
    exact ho.symm.trans hc
  have hdisjAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxa hxb
    exact hsepab ((ConjClasses.mk_eq_mk_iff_isConj.mp (by simpa [A] using hxa)).symm.trans
      (ConjClasses.mk_eq_mk_iff_isConj.mp (by simpa [B] using hxb)))
  have hdisjAC : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro x hxa hxc
    exact hsepac ((ConjClasses.mk_eq_mk_iff_isConj.mp (by simpa [A] using hxa)).symm.trans
      (ConjClasses.mk_eq_mk_iff_isConj.mp (by simpa [C] using hxc)))
  have hdisjBC : Disjoint B C := by
    rw [Finset.disjoint_left]
    intro x hxb hxc
    exact hsepbc ((ConjClasses.mk_eq_mk_iff_isConj.mp (by simpa [B] using hxb)).symm.trans
      (ConjClasses.mk_eq_mk_iff_isConj.mp (by simpa [C] using hxc)))
  have hunion : (Finset.univ.filter (fun x : H => orderOf x = 2)) = A ∪ B ∪ C := by
    ext x
    simp [A, B, C, Finset.mem_union]
    constructor
    · intro hx
      rcases hcover x hx with hxa | hxb | hxc
      · exact Or.inl (by simpa [A] using (ConjClasses.mk_eq_mk_iff_isConj.mpr hxa))
      · exact Or.inr (Or.inl (by simpa [B] using (ConjClasses.mk_eq_mk_iff_isConj.mpr hxb)))
      · exact Or.inr (Or.inr (by simpa [C] using (ConjClasses.mk_eq_mk_iff_isConj.mpr hxc)))
    · intro hx
      rcases hx with hxa | hxbc
      · exact hAinv x (by simpa [A] using hxa)
      · rcases hxbc with hxb | hxc
        · exact hBinv x (by simpa [B] using hxb)
        · exact hCinv x (by simpa [C] using hxc)
  rw [involutionSum_eq_sum_ite]
  rw [← Finset.sum_filter]
  rw [hunion, Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hdisjAC, hdisjBC⟩), Finset.sum_union hdisjAB]
  have hfa : ∀ x ∈ A, f x = f a := by
    intro x hx
    have hxa : IsConj x a := ConjClasses.mk_eq_mk_iff_isConj.mp (by simpa [A] using hx)
    obtain ⟨g, hg⟩ := isConj_iff.mp hxa
    exact (hf x g).symm.trans (by rw [hg])
  have hfb : ∀ x ∈ B, f x = f b := by
    intro x hx
    have hxb : IsConj x b := ConjClasses.mk_eq_mk_iff_isConj.mp (by simpa [B] using hx)
    obtain ⟨g, hg⟩ := isConj_iff.mp hxb
    exact (hf x g).symm.trans (by rw [hg])
  have hfc : ∀ x ∈ C, f x = f c := by
    intro x hx
    have hxc : IsConj x c := ConjClasses.mk_eq_mk_iff_isConj.mp (by simpa [C] using hx)
    obtain ⟨g, hg⟩ := isConj_iff.mp hxc
    exact (hf x g).symm.trans (by rw [hg])
  have hsumA : (∑ x ∈ A, f x) = (∑ x ∈ A, f a) := Finset.sum_congr rfl hfa
  have hsumB : (∑ x ∈ B, f x) = (∑ x ∈ B, f b) := Finset.sum_congr rfl hfb
  have hsumC : (∑ x ∈ C, f x) = (∑ x ∈ C, f c) := Finset.sum_congr rfl hfc
  rw [hsumA, hsumB, hsumC, Finset.sum_const, Finset.sum_const, Finset.sum_const]
  simp only [nsmul_eq_mul]
  have hca := class_card_mul_centralizer_card a
  have hcb := class_card_mul_centralizer_card b
  have hcc := class_card_mul_centralizer_card c
  have hAc : Nat.card A = Nat.card (ConjClasses.mk a).carrier := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun x => by
      simpa [A] using (ConjClasses.mem_carrier_iff_mk_eq (a := x) (b := ConjClasses.mk a)).symm))
  have hBc : Nat.card B = Nat.card (ConjClasses.mk b).carrier := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun x => by
      simpa [B] using (ConjClasses.mem_carrier_iff_mk_eq (a := x) (b := ConjClasses.mk b)).symm))
  have hCc : Nat.card C = Nat.card (ConjClasses.mk c).carrier := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun x => by
      simpa [C] using (ConjClasses.mem_carrier_iff_mk_eq (a := x) (b := ConjClasses.mk c)).symm))
  have hca := class_card_mul_centralizer_card a
  have hcb := class_card_mul_centralizer_card b
  have hcc := class_card_mul_centralizer_card c
  have hcenta : Nat.card (Subgroup.centralizer ({a} : Set H)) = Nat.card {x : H // x * a = a * x} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun x => Subgroup.mem_centralizer_singleton_iff)
  have hcentb : Nat.card (Subgroup.centralizer ({b} : Set H)) = Nat.card {x : H // x * b = b * x} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun x => Subgroup.mem_centralizer_singleton_iff)
  have hcentc : Nat.card (Subgroup.centralizer ({c} : Set H)) = Nat.card {x : H // x * c = c * x} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun x => Subgroup.mem_centralizer_singleton_iff)
  have hca' : (Nat.card A : ℂ) * (Nat.card (Subgroup.centralizer ({a} : Set H)) : ℂ) = Nat.card H := by
    rw [hAc, hcenta]
    exact_mod_cast hca
  have hcb' : (Nat.card B : ℂ) * (Nat.card (Subgroup.centralizer ({b} : Set H)) : ℂ) = Nat.card H := by
    rw [hBc, hcentb]
    exact_mod_cast hcb
  have hcc' : (Nat.card C : ℂ) * (Nat.card (Subgroup.centralizer ({c} : Set H)) : ℂ) = Nat.card H := by
    rw [hCc, hcentc]
    exact_mod_cast hcc
  have hna : (Nat.card (Subgroup.centralizer ({a} : Set H)) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := Subgroup.centralizer ({a} : Set H))).ne'
  have hnb : (Nat.card (Subgroup.centralizer ({b} : Set H)) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := Subgroup.centralizer ({b} : Set H))).ne'
  have hnc : (Nat.card (Subgroup.centralizer ({c} : Set H)) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := Subgroup.centralizer ({c} : Set H))).ne'
  have hqa : (Nat.card A : ℂ) = (Nat.card H : ℂ) / Nat.card (Subgroup.centralizer ({a} : Set H)) := by
    apply (eq_div_iff hna).2
    exact hca'
  have hqb : (Nat.card B : ℂ) = (Nat.card H : ℂ) / Nat.card (Subgroup.centralizer ({b} : Set H)) := by
    apply (eq_div_iff hnb).2
    exact hcb'
  have hqc : (Nat.card C : ℂ) = (Nat.card H : ℂ) / Nat.card (Subgroup.centralizer ({c} : Set H)) := by
    apply (eq_div_iff hnc).2
    exact hcc'
  have hqa' : (A.card : ℂ) = (Nat.card H : ℂ) / Nat.card (Subgroup.centralizer ({a} : Set H)) := by
    simpa [Nat.card_eq_fintype_card] using hqa
  have hqb' : (B.card : ℂ) = (Nat.card H : ℂ) / Nat.card (Subgroup.centralizer ({b} : Set H)) := by
    simpa [Nat.card_eq_fintype_card] using hqb
  have hqc' : (C.card : ℂ) = (Nat.card H : ℂ) / Nat.card (Subgroup.centralizer ({c} : Set H)) := by
    simpa [Nat.card_eq_fintype_card] using hqc
  rw [hqa', hqb', hqc']

end Stellmacher.Recognition.LyonsU3Four

namespace Stellmacher.Recognition.LyonsU3Four

open Theory.Character
attribute [local instance] Fintype.ofFinite Classical.propDecidable
variable {G : Type*} [Group G] [Finite G]
variable {S : Sylow 2 G}
/-- The three-class count turns the local values on three involution representatives into
actual involution sums.  The hypotheses expose only fusion, class separation, and the
three orbit--stabilizer quotients; no involution sum is assumed. -/
theorem actual_involution_sums_of_three_classes
    {H : Type*} [Group H] [Finite H]
    (a b c : H) (r : ℂ)
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hc : orderOf c = 2)
    (hcover : ∀ u : H, orderOf u = 2 → IsConj u a ∨ IsConj u b ∨ IsConj u c)
    (hsepab : ¬ IsConj a b) (hsepac : ¬ IsConj a c) (hsepbc : ¬ IsConj b c)
    (hca : (Nat.card H : ℂ) / Nat.card (Subgroup.centralizer ({a} : Set H)) = 1)
    (hcb : (Nat.card H : ℂ) / Nat.card (Subgroup.centralizer ({b} : Set H)) = r)
    (hcc : (Nat.card H : ℂ) / Nat.card (Subgroup.centralizer ({c} : Set H)) = r)
    (f : ClassFunction H) (hf : IsClassFunction f)
    (hfa : f a = 1) (hfb : f b = 1) (hfc : f c = 1) :
    involutionSum f = 1 + 2 * r := by
  rw [three_involution_sum a b c ha hb hc hcover hsepab hsepac hsepbc f hf]
  rw [hca, hcb, hcc, hfa, hfb, hfc]
  ring

omit [Finite G] in
/-- The quartic row sum obtained from the actual three local involution classes. -/
theorem actual_quartic_involution_sum_of_three_classes
    {H : Type*} [Group H] [Finite H]
    (a b c : H) (r : ℂ) (v w : QuarticCentralIndex S)
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hc : orderOf c = 2)
    (hcover : ∀ u : H, orderOf u = 2 → IsConj u a ∨ IsConj u b ∨ IsConj u c)
    (hsepab : ¬ IsConj a b) (hsepac : ¬ IsConj a c) (hsepbc : ¬ IsConj b c)
    (hca : (Nat.card H : ℂ) / Nat.card (Subgroup.centralizer ({a} : Set H)) = 1)
    (hcb : (Nat.card H : ℂ) / Nat.card (Subgroup.centralizer ({b} : Set H)) = r)
    (hcc : (Nat.card H : ℂ) / Nat.card (Subgroup.centralizer ({c} : Set H)) = r)
    (f : ClassFunction H) (hf : IsClassFunction f)
    (hfa : f a = if v = w then 4 else -4)
    (hfb : f b = if v = w then 4 else -4)
    (hfc : f c = if v = w then 4 else -4)
    (hcalc : (if v = w then 4 else -4) +
      r * (if v = w then 4 else -4) + r * (if v = w then 4 else -4) =
      if v = w then 4 - 8 * r else -4) :
    involutionSum f = if v = w then 4 - 8 * r else -4 := by
  rw [three_involution_sum a b c ha hb hc hcover hsepab hsepac hsepbc f hf]
  rw [hca, hcb, hcc, hfa, hfb, hfc]
  simpa only [one_mul] using hcalc

/-- The quintic row sum obtained from the actual three local involution classes. -/
theorem actual_quintic_involution_sum_of_three_classes
    {H : Type*} [Group H] [Finite H]
    (a b c : H) (r : ℂ)
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hc : orderOf c = 2)
    (hcover : ∀ u : H, orderOf u = 2 → IsConj u a ∨ IsConj u b ∨ IsConj u c)
    (hsepab : ¬ IsConj a b) (hsepac : ¬ IsConj a c) (hsepbc : ¬ IsConj b c)
    (hca : (Nat.card H : ℂ) / Nat.card (Subgroup.centralizer ({a} : Set H)) = 1)
    (hcb : (Nat.card H : ℂ) / Nat.card (Subgroup.centralizer ({b} : Set H)) = r)
    (hcc : (Nat.card H : ℂ) / Nat.card (Subgroup.centralizer ({c} : Set H)) = r)
    (f : ClassFunction H) (hf : IsClassFunction f)
    (hfa : f a = 5) (hfb : f b = 5) (hfc : f c = 5) :
    involutionSum f = 5 + 10 * r := by
  rw [three_involution_sum a b c ha hb hc hcover hsepab hsepac hsepbc f hf]
  rw [hca, hcb, hcc, hfa, hfb, hfc]
  ring

end Stellmacher.Recognition.LyonsU3Four


