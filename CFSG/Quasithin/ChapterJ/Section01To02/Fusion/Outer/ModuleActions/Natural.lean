module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.Defs
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.QuotientModule.Alternating
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.FinCases

/-!
# Freeness on the actual restricted natural SL₂(4) module

An outer involution of S₅ centralizes a three-cycle and fails to centralize A₅.
Faithfulness of the restricted natural action makes its involution operator
nonidentity. The cubic action has no nonzero fixed vector: a determinant-one
matrix fixing a nonzero vector is conjugate to an upper unipotent and squares
to one, so it cannot also have order three. A binary displacement line would
be fixed by the commuting cubic operator. Thus the displacement dimension is
two, and rank-nullity identifies it with the involution's fixed space.

The final application uses the literal Ru2 quotient map and O²(H)=K. Its only
earlier-source premise is Q≤K from J.2.2(1). No semilinear-normalizer
identification or deleted permutation module is used.
Source: Aschbacher–Smith, J.2.6, printed p.435 (PDF p.446).
-/

public section

open Subgroup Representation
open CFSG.Quasithin.ChapterJ
namespace CFSG.Quasithin.ChapterJ.Fusion.Outer

private lemma binary_add_self (v : FourSpace) : v + v = 0 := by
  have h := @two_smul (ZMod 2) FourSpace _ _ _ v
  rw [show (2 : ZMod 2) = 0 by decide, zero_smul] at h
  exact h.symm

private lemma first_vector_stabilizer_square (g : SL2FourNatural.SL)
    (hg : SL2FourNatural.action g ![1, 0] = ![1, 0]) : g * g = 1 := by
  have h0 := congrFun hg 0
  have h1 := congrFun hg 1
  simp only [SL2FourNatural.action_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, mul_zero,
    add_zero] at h0 h1
  have hd := g.property
  simp only [Matrix.det_fin_two, h0, h1, one_mul, mul_zero, sub_zero] at hd
  apply Subtype.ext
  change g.val * g.val = 1
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h0, h1, hd, CharTwo.add_self_eq_zero]

private lemma cubic_fixed_free (g : SL2FourNatural.SL) (hg3 : g ^ 3 = 1)
    (hg1 : g ≠ 1) (v : FourSpace) (hv : SL2FourNatural.action g v = v) : v = 0 := by
  by_contra hv0
  obtain ⟨A, hA⟩ := SL2FourNatural.exists_first_column v hv0
  have hfix : SL2FourNatural.action (A⁻¹ * g * A) ![1, 0] = ![1, 0] := by
    rw [map_mul, map_mul]
    change SL2FourNatural.action A⁻¹ (SL2FourNatural.action g
      (SL2FourNatural.action A ![1, 0])) = _
    rw [hA, hv, ← hA]
    change (SL2FourNatural.action A⁻¹ * SL2FourNatural.action A) ![1, 0] = _
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  have hs := first_vector_stabilizer_square (A⁻¹ * g * A) hfix
  have hg2 : g ^ 2 = 1 := by
    rw [pow_two]
    calc
      g * g = A * ((A⁻¹ * g * A) * (A⁻¹ * g * A)) * A⁻¹ := by group
      _ = 1 := by rw [hs]; group

  apply hg1
  calc
    g = g ^ 3 * (g ^ 2)⁻¹ := by group
    _ = 1 := by rw [hg3, hg2, inv_one, mul_one]

private def cubicChoices : Fin 10 → S5 := ![
  Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 0 1 * Equiv.swap 1 3,
  Equiv.swap 0 1 * Equiv.swap 1 4, Equiv.swap 0 2 * Equiv.swap 2 3,
  Equiv.swap 0 2 * Equiv.swap 2 4, Equiv.swap 0 3 * Equiv.swap 3 4,
  Equiv.swap 1 2 * Equiv.swap 2 3, Equiv.swap 1 2 * Equiv.swap 2 4,
  Equiv.swap 1 3 * Equiv.swap 3 4, Equiv.swap 2 3 * Equiv.swap 3 4]

private lemma cubicChoices_spec : ∀ j, (cubicChoices j).sign = 1 ∧
    cubicChoices j ^ 3 = 1 ∧ cubicChoices j ≠ 1 := by decide +kernel

private lemma outer_cubic_choice : ∀ t : S5, t.sign ≠ 1 → t * t = 1 →
    ∃ j : Fin 10, t * cubicChoices j = cubicChoices j * t := by
  decide +kernel

private lemma outer_cubic (t : S5) (ht : t.sign ≠ 1) (ht2 : t * t = 1) :
    ∃ b : S5, b.sign = 1 ∧ b ^ 3 = 1 ∧ b ≠ 1 ∧ t * b = b * t := by
  obtain ⟨j, hj⟩ := outer_cubic_choice t ht ht2
  exact ⟨cubicChoices j, (cubicChoices_spec j).1, (cubicChoices_spec j).2.1,
    (cubicChoices_spec j).2.2, hj⟩

private lemma outer_not_central_choice : ∀ t : S5, t.sign ≠ 1 →
    t * cubicChoices 0 * t⁻¹ ≠ cubicChoices 0 ∨
      t * cubicChoices 9 * t⁻¹ ≠ cubicChoices 9 := by
  decide +kernel

private lemma outer_not_central (t : S5) (ht : t.sign ≠ 1) :
    ∃ a : S5, a.sign = 1 ∧ t * a * t⁻¹ ≠ a := by
  rcases outer_not_central_choice t ht with h | h
  · exact ⟨cubicChoices 0, (cubicChoices_spec 0).1, h⟩
  · exact ⟨cubicChoices 9, (cubicChoices_spec 9).1, h⟩

theorem natural_injective_on_alternating (r : L2FourAction)
    (a b : alternatingGroup (Fin 5)) (h : r.action a = r.action b) : a = b := by
  apply r.marking.symm.injective
  apply SL2FourNatural.action_faithful
  apply LinearEquiv.ext
  intro v
  have he := LinearMap.congr_fun h v
  simpa only [← r.restriction, r.marking.apply_symm_apply] using he

theorem natural_outer_ne_one (r : L2FourAction) (t : S5)
    (ht : t ∉ alternatingGroup (Fin 5)) (ht2 : t * t = 1) : r.action t ≠ 1 := by
  intro he
  obtain ⟨a, ha, hta⟩ := outer_not_central t (fun h => ht (Equiv.Perm.mem_alternatingGroup.mpr h))
  have ha' : a ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.mpr ha
  have hc : t * a * t⁻¹ ∈ alternatingGroup (Fin 5) :=
    (inferInstance : (alternatingGroup (Fin 5)).Normal).conj_mem a ha' t
  have hi : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  apply hta
  exact congrArg Subtype.val (natural_injective_on_alternating r ⟨_, hc⟩ ⟨a, ha'⟩ (by
    change r.action (t * a * t⁻¹) = r.action a
    rw [map_mul, map_mul, hi, he, one_mul, mul_one]))

theorem natural_cubic_fixed_free (r : L2FourAction) (b : alternatingGroup (Fin 5))
    (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) (v : FourSpace)
    (hv : r.action b v = v) : v = 0 := by
  let g := r.marking.symm b
  have hg3 : g ^ 3 = 1 := by simp [g, ← map_pow, hb3]
  have hg1 : g ≠ 1 := by simpa [g] using hb1
  apply cubic_fixed_free g hg3 hg1 v
  simpa only [g, ← r.restriction, r.marking.apply_symm_apply] using hv

private lemma four_dimensional_free
    (a b : Module.End (ZMod 2) FourSpace)
    (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (hb : ∀ v, b v = v → v = 0)
    (hbi : Function.Injective b) (hab : a * b = b * a) :
    ∀ v, a v = v → ∃ w, a w + w = v := by
  let D := a - 1
  have hincl : D.range ≤ D.ker := by
    rintro _ ⟨w, rfl⟩
    change a (a w - w) - (a w - w) = 0
    have haa : a (a w) = w := LinearMap.congr_fun ha2 w
    rw [map_sub, haa]
    calc
      w - a w - (a w - w) = (w + w) - (a w + a w) := by abel
      _ = 0 := by rw [binary_add_self, binary_add_self, sub_self]
  have hdim := D.finrank_range_add_finrank_ker
  rw [SL2FourNatural.finrank_vector] at hdim
  have hr0 : Module.finrank (ZMod 2) D.range ≠ 0 := by
    intro h
    have hz : D = 0 := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h)
    exact ha1 (sub_eq_zero.mp hz)
  have hr1 : Module.finrank (ZMod 2) D.range ≠ 1 := by
    intro hr
    obtain ⟨w, hw, hw0⟩ := D.range.ne_bot_iff.mp (fun h => hr0 (Submodule.finrank_eq_zero.mpr h))
    have hbw : b w ∈ D.range := by
      obtain ⟨u, rfl⟩ := hw
      refine ⟨b u, ?_⟩
      change a (b u) - b u = b (a u - u)
      rw [map_sub]
      exact congrArg (fun v => v - b u) (LinearMap.congr_fun hab u)
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hr
      (show (⟨w, hw⟩ : D.range) ≠ 0 from fun he => hw0 (congrArg Subtype.val he))
      (⟨b w, hbw⟩ : D.range)
    have hcv : c • w = b w := congrArg Subtype.val hc
    fin_cases c
    · change (0 : ZMod 2) • w = b w at hcv
      have hb0 : b w = 0 := by simpa only [zero_smul] using hcv.symm
      exact hw0 (hbi (hb0.trans (map_zero b).symm))
    · change (1 : ZMod 2) • w = b w at hcv
      exact hw0 (hb w (by simpa only [one_smul] using hcv.symm))
  have he : D.range = D.ker := Submodule.eq_of_le_of_finrank_eq hincl
    (by have := Submodule.finrank_mono hincl; omega)
  intro v hv
  have hvk : v ∈ D.ker := by change a v - v = 0; rw [hv, sub_self]
  obtain ⟨w, hw⟩ := he.symm ▸ hvk
  refine ⟨w, ?_⟩
  change a w - w = v at hw
  simpa only [sub_eq_add_neg, neg_eq_of_add_eq_zero_left (binary_add_self w)] using hw

theorem natural_free_outer (r : L2FourAction) (t : S5)
    (ht : t ∉ alternatingGroup (Fin 5)) (ht2 : t * t = 1) : FreeAt r.action t := by
  obtain ⟨b, hb, hb3, hb1, htb⟩ := outer_cubic t
    (fun h => ht (Equiv.Perm.mem_alternatingGroup.mpr h)) ht2
  have hbmem := Equiv.Perm.mem_alternatingGroup.mpr hb
  apply four_dimensional_free (r.action t) (r.action b)
  · rw [← map_mul, ht2, map_one]
  · exact natural_outer_ne_one r t ht ht2
  · exact natural_cubic_fixed_free r ⟨b, hbmem⟩ (Subtype.ext hb3)
      (fun h => hb1 (congrArg Subtype.val h))
  · intro x y hxy
    have hx := congrArg (r.action b⁻¹) hxy
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using hx
  · rw [← map_mul, ← map_mul, htb]

variable {G : Type*} [Group G] [Finite G]

theorem quotientMap_not_alternating (d : TypeRuSetup G) (hQK : d.Q ≤ d.K)
    (i : d.H) (hi : (i : G) ∉ d.K) : d.ru2.quotientMap i ∉ alternatingGroup (Fin 5) := by
  have hk : d.ru2.quotientMap.ker ≤ d.K.subgroupOf d.H := by
    rw [d.ru2.quotient_kernel]
    exact comap_mono hQK
  have he : (alternatingGroup (Fin 5)).comap d.ru2.quotientMap = d.K.subgroupOf d.H := by
    rw [← d.quotientMap_K, comap_map_eq_self hk]
  intro h
  have himem : i ∈ (alternatingGroup (Fin 5)).comap d.ru2.quotientMap := h
  rw [he] at himem
  exact hi himem

theorem quotientMap_involution (d : TypeRuSetup G) (i : d.H)
    (hi : orderOf (i : G) = 2) : d.ru2.quotientMap i * d.ru2.quotientMap i = 1 := by
  have hi2 : i * i = 1 := by
    apply Subtype.ext
    change (i : G) * (i : G) = 1
    simpa only [hi, pow_two] using pow_orderOf_eq_one (i : G)
  rw [← map_mul, hi2, map_one]

theorem natural_free (d : TypeRuSetup G) (hQK : d.Q ≤ d.K)
    (i : d.H) (hi : (i : G) ∉ d.K) (hi2 : orderOf (i : G) = 2) :
    FreeAt d.ru2.naturalAction.action (d.ru2.quotientMap i) :=
  natural_free_outer d.ru2.naturalAction _ (quotientMap_not_alternating d hQK i hi)
    (quotientMap_involution d i hi2)

end CFSG.Quasithin.ChapterJ.Fusion.Outer
