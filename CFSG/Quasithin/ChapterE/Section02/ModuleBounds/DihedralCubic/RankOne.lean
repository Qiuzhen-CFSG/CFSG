module

public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.Bound
/-!
# The rank-one two-conjugate core

If the actual actor quotient A/Z has order two, the core P=BA is elementary.
Choose a nonzero A/Z element. The exact fixed-space identity on P/Z supplies
an element v of V whose commutator with a is in B outside Z. This commutator
is an involution and commutes with a. Since both A/Z and B/Z have order two,
centrality of Z then makes A and B commute. Their elementary join is P.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.2.10(2,5)
and the dihedral branch of E.2.15, printed pp.222–228. This proves the
small-actor step directly from the genuine two-conjugate hypotheses.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
variable {X : Type*} [Group X] [Finite X]
variable {T : Sylow 2 X} {V M : Subgroup X} {g : X}

omit [Finite X] in
private lemma line_centralizer {Y : Type*} [Group Y] (q : X →* Y)
    (hz : q.ker ≤ center X) (D : Subgroup X) (hd : Nat.card (D.map q) = 2)
    (a : X) (ha : a ∈ D) (han : q a ≠ 1) (b : X) (hab : a * b = b * a) :
    D ≤ centralizer ({b} : Set X) := by
  obtain ⟨u, hu, huniq⟩ := (Nat.card_eq_two_iff' (1 : D.map q)).mp hd
  have hsame (x : X) (hx : x ∈ D) (hxn : q x ≠ 1) : q x = q a := by
    have ha' : (⟨q a, mem_map_of_mem q ha⟩ : D.map q) ≠ 1 :=
      fun he => han (congrArg Subtype.val he)
    have hx' : (⟨q x, mem_map_of_mem q hx⟩ : D.map q) ≠ 1 :=
      fun he => hxn (congrArg Subtype.val he)
    exact congrArg Subtype.val ((huniq _ hx').trans (huniq _ ha').symm)
  intro x hx
  rw [mem_centralizer_singleton_iff]
  by_cases hxn : q x = 1
  · exact (mem_center_iff.mp (hz hxn) b).symm
  · have he : x * a⁻¹ ∈ q.ker := by
      change q (x * a⁻¹) = 1
      rw [map_mul, map_inv, hsame x hx hxn, mul_inv_cancel]
    have hc := mem_center_iff.mp (hz he) b
    have hca : a ∈ centralizer ({b} : Set X) := mem_centralizer_singleton_iff.mpr hab
    have hcx : x * a⁻¹ ∈ centralizer ({b} : Set X) :=
      mem_centralizer_singleton_iff.mpr hc.symm
    simpa only [inv_mul_cancel_right] using
      mem_centralizer_singleton_iff.mp ((centralizer ({b} : Set X)).mul_mem hcx hca)

/-- In the rank-one case the actual two-conjugate core is elementary. -/
theorem P_elementary_of_actor_index_two (h : Hypotheses T V M g)
    (hi : (Z V g).relIndex (A V M g) = 2) :
    IsElementaryAbelian 2 (P V M g) := by
  let := h.Z_normal
  let := h.elementary
  let := h.A_elementary
  let := h.B_elementary
  let q := QuotientGroup.mk' (Z V g)
  have hz : q.ker ≤ center X := by
    rw [QuotientGroup.ker_mk']
    exact h.core_geometry.2.2.trans inf_le_right
  have hA : Nat.card ((A V M g).map q) = 2 := by
    rw [← relIndex_ker, QuotientGroup.ker_mk', hi]
  have hZconj : (Z V g).map (MulAut.conj g).toMonoidHom = Z V g :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top g))
  have hBi : (Z V g).relIndex (B V M) = 2 := by
    have hh := relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) (Z V g) (B V M) (MulAut.conj g).injective
    rw [hZconj] at hh
    exact hh.symm.trans hi
  have hB : Nat.card ((B V M).map q) = 2 := by
    rw [← relIndex_ker, QuotientGroup.ker_mk', hBi]
  obtain ⟨aa, haa, _⟩ := (Nat.card_eq_two_iff' (1 : (A V M g).map q)).mp hA
  obtain ⟨a, ha, hea⟩ := aa.property
  have han : q a ≠ 1 := by
    intro he
    apply haa
    apply Subtype.ext
    exact hea.symm.trans he
  obtain ⟨v, hv, hmove⟩ : ∃ v ∈ V, ⁅v,a⁆ ∉ Z V g := by
    by_contra hn
    push Not at hn
    have hac : q a ∈ centralizer (V.map q : Set (X ⧸ Z V g)) := by
      rw [mem_centralizer_iff]
      rintro _ ⟨v, hv, rfl⟩
      apply commutatorElement_eq_one_iff_mul_comm.mp
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr (hn v hv)
    have he : q a ∈ (A V M g).map q ⊓ centralizer (V.map q : Set (X ⧸ Z V g)) :=
      ⟨mem_map_of_mem q ha, hac⟩
    rw [h.quotient_A_fixed_eq_bot] at he
    exact han he
  let c := ⁅v,a⁆
  have hcB : c ∈ B V M := by
    apply h.commutator_P_V_le_B
    rw [commutator_comm]
    exact commutator_mem_commutator hv (show a ∈ P V M g from (show A V M g ≤ P V M g from le_sup_right) ha)
  have hcn : q c ≠ 1 := fun he => hmove ((QuotientGroup.eq_one_iff _).mp he)
  have haI : a⁻¹ = a := inv_eq_of_mul_eq_one_left
    (by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha)
  have hvI : v⁻¹ = v := inv_eq_of_mul_eq_one_left
    (by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv)
  have hcI : c⁻¹ = c := inv_eq_of_mul_eq_one_left
    (by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) c hcB)
  have hac : a * c = c * a := by
    apply mul_inv_eq_iff_eq_mul.mp
    calc
      a * c * a⁻¹ = c⁻¹ := by
        dsimp only [c]
        have ha2 : a * a = 1 := by simpa only [haI] using inv_mul_cancel a
        simp only [commutatorElement_def, mul_inv_rev, haI, hvI, mul_assoc, ha2, mul_one]
      _ = c := hcI
  have hAc : A V M g ≤ centralizer ({c} : Set X) :=
    line_centralizer q hz _ hA a ha han c hac
  have hBA : B V M ≤ centralizer (A V M g : Set X) := by
    intro b hb a' ha'
    have hca : c * a' = a' * c := (mem_centralizer_singleton_iff.mp (hAc ha')).symm
    exact (mem_centralizer_singleton_iff.mp
      (line_centralizer q hz _ hB c hcB hcn a' hca hb)).symm
  exact IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp hBA)
end CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
