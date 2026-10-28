module
public import Theory.SpecificGroups.GL2.ThreeResidualAutomorphisms
public import Theory.SpecificGroups.SL2.ThreeResidualCore
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Cubic centralizers and automorphisms in SL₂(3)

The centralizer of an element of order three has order six and is generated
by that element and the center. Every automorphism fixing that element is
inner: lift the automorphism to GL₂(3), then the commuting-matrix equation
forces determinant one. The finite calculation ranges over two-by-two
matrices over the three-element field. Both statements transport through
an arbitrary given SL₂(3) equivalence.

Source: the local calculation in Fong–Wong, Nagoya Math. J.36 (1969),
§3B–C, p.156. The consumer `G2Recognition.CubicLocal` uses these facts
for the original normal factors, before passing to ambient centralizers.
-/

public section
open Subgroup Matrix
namespace Matrix.SpecialLinearGroup
local notation "SL23" => SpecialLinearGroup (Fin 2) (ZMod 3)
private theorem cubic_fix_determinant :
    ∀ (g x : Matrix (Fin 2) (Fin 2) (ZMod 3)),
      x ^ 3 = 1 → x ≠ 1 → g * x = x * g → g.det ≠ 0 → g.det = 1 := by
  decide +kernel

theorem cubic_fixer_inner (a : MulAut SL23) (x : SL23) (hx : orderOf x = 3) :
    a x = x → ∃ y : SL23, a = MulAut.conj y := by
  intro hax
  let e := GeneralLinearGroup.threeSpecialLinearEquiv
  let b := (MulAut.congr e.symm) a
  obtain ⟨g,hg⟩ := GeneralLinearGroup.three_specialLinear_aut_surjective b
  have hfx : (MulAut.conjNormal g : MulAut GeneralLinearGroup.threeSpecialLinear)
      (e.symm x) = e.symm x := by
    rw [hg]
    change e.symm (a (e (e.symm x))) = e.symm x
    rw [e.apply_symm_apply, hax]
  have h3 : (e.symm x)^3=1 := by rw [← map_pow, show x^3=1 by simpa only [hx] using pow_orderOf_eq_one x, map_one]
  have hn : e.symm x ≠ 1 := by
    intro he
    have hx1 := e.symm.injective (he.trans e.symm.map_one.symm)
    simp [hx1] at hx
  have hm : g ∈ GeneralLinearGroup.threeSpecialLinear := by
    apply (GeneralLinearGroup.three_mem_specialLinear g).mpr
    apply cubic_fix_determinant g.val (e.symm x).val.val
    · exact congrArg (fun w : GeneralLinearGroup.threeSpecialLinear => w.val.val) h3
    · intro he
      exact hn (Subtype.ext (Units.ext he))
    · have hh := congrArg Subtype.val hfx
      change g * (e.symm x).val * g⁻¹ = (e.symm x).val at hh
      exact congrArg Units.val (mul_inv_eq_iff_eq_mul.mp hh)
    · exact g.det_ne_zero
  refine ⟨e ⟨g,hm⟩, ?_⟩
  apply MulEquiv.ext
  intro t
  have hh := congrArg (fun f : MulAut GeneralLinearGroup.threeSpecialLinear => f (e.symm t)) hg
  have hh' := congrArg e hh
  change e ((⟨g,hm⟩ : GeneralLinearGroup.threeSpecialLinear) * e.symm t * (⟨g,hm⟩ : GeneralLinearGroup.threeSpecialLinear)⁻¹) = _ at hh'
  simpa [b, MulAut.congr_apply, MulAut.conj_apply] using hh'.symm

theorem cubic_centralizer_card (x : SL23) (hx : orderOf x = 3) :
    Nat.card (centralizer ({x} : Set SL23)) = 6 := by
  have h : ∀ x : SL23, x^3=1 → x≠1 →
      Fintype.card {y : SL23 // x*y=y*x} = 6 := by decide +kernel
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun _ =>
    mem_centralizer_singleton_iff.trans eq_comm)), Nat.card_eq_fintype_card]
  exact h x (by simpa only [hx] using pow_orderOf_eq_one x) (by intro he; simp [he] at hx)
theorem cubic_fixer_inner_of_equiv {I : Type*} [Group I] (e : I ≃* SL23)
    (a : MulAut I) (x : I) (hx : orderOf x = 3) (ha : a x = x) :
    ∃ y : I, a = MulAut.conj y := by
  obtain ⟨y,hy⟩ := cubic_fixer_inner ((MulAut.congr e) a) (e x)
    ((e.orderOf_eq x).trans hx) (by change e (a (e.symm (e x))) = e x; simp [ha])
  refine ⟨e.symm y, ?_⟩
  apply MulEquiv.ext
  intro t
  apply e.injective
  have hh := congrArg (fun f : MulAut SL23 => f (e t)) hy
  simpa using hh

theorem cubic_centralizer_of_equiv {I : Type*} [Group I] [Finite I] (e : I ≃* SL23)
    (x : I) (hx : orderOf x = 3) :
    centralizer ({x} : Set I) = center I ⊔ zpowers x := by
  have hcent : Nat.card (center I) = 2 :=
    (Nat.card_congr (centerCongr e).toEquiv).trans GLS3.Chapter5.SchurPresentation.sl23_center_card
  have hci : Nat.card (centralizer ({x} : Set I)) = 6 := by
    have he : (centralizer ({x} : Set I)).map e.toMonoidHom = centralizer ({e x} : Set SL23) := by
      ext y
      constructor
      · rintro ⟨w,hw,rfl⟩
        apply mem_centralizer_singleton_iff.mpr
        change e w * e x = e x * e w
        simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp hw)
      · intro hy
        refine ⟨e.symm y, mem_centralizer_singleton_iff.mpr ?_, e.apply_symm_apply y⟩
        apply e.injective
        simpa only [map_mul,e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hy
    rw [← card_map_of_injective (f := e.toMonoidHom) e.injective,he]
    exact cubic_centralizer_card (e x) ((e.orderOf_eq x).trans hx)
  have hd : Disjoint (center I) (zpowers x) := disjoint_of_coprime_natCard (by
    rw [hcent,Nat.card_zpowers,hx]; decide)
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes (center I) (zpowers x)
    (show zpowers x ≤ normalizer (center I : Set I) from le_normalizer_of_normal)
  rw [hcent,Nat.card_zpowers,hx,hd.eq_bot,Nat.card_unique,one_mul] at hc
  apply (eq_of_le_of_card_ge (sup_le (center_le_centralizer _) (zpowers_le.mpr
    (mem_centralizer_singleton_iff.mpr rfl))) ?_).symm
  rw [hci,←hc]
end Matrix.SpecialLinearGroup
