module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.QuotientRank

/-!
# The actual central quotient in the direct ordinary-component route

The component's own prime-to-three residual identity comes from A.3.18.
It places the original K in the marked fixed subgroup, with three-rank two.
Its central two-core quotient preserves this rank and the original inner
involution. This does not use a residual identity for the partner Mc.

Source: Aschbacher--Smith, proof of 15.2.15, printed p.1118.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 Section03 ChapterA.Section05To06 ChapterD.UniqueFactor
open OrdinaryComponents Candidates.ComponentStructure ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I : Subgroup G}
variable {h : ChosenSmallSource T M Mc V}
variable (r : ResidualInput h H B)
include r
variable {P : Sylow 2 I} {z : G}
variable (c : ComponentData (T := T) (Mc := Mc) I P z)
variable {D : Type*} [Group D] [Finite D]

/-- The original rank-two K embeds in the marked fixed subgroup upstairs. -/
theorem ResidualInput.fixed_three_rank_of_quotient_direct
    (hcard : Nat.card (centralInvolutions T) = 2) (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (e : (c.component ⧸ pCore 2 c.component) ≃* D)
    (hr : 2 ≤ primeRank 3 D) (ho : IsPGroup 2 (MulAut.Outer D))
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹) :
    2 ≤ primeRank 3 a.fixedSubgroup := by
  let K := residual H
  have hKL : K ≤ c.component.map I.subtype := by
    rw [component_eq_residual_of_quotient (hsource := h) c hI e hr ho]
    exact r.residual_le_escape_cubic hI
  let eL := c.component.equivMapOfInjective I.subtype I.subtype_injective
  let f : K →* c.component := eL.symm.toMonoidHom.comp (inclusion hKL)
  have hf (k : K) : ((f k : I) : G) = k := by
    exact congrArg Subtype.val (eL.apply_symm_apply ⟨k,hKL k.property⟩)
  have hfix (k : K) : f k ∈ a.fixedSubgroup := by
    rw [MulAut.mem_fixedSubgroup]
    apply Subtype.ext
    apply Subtype.ext
    rw [ha,hf]
    have hkMc : (k : G) ∈ Mc :=
      r.geometry.in_partner (map_subtype_le _ k.property)
    have hkz : (k : G) * z = z * k := mem_centralizer_singleton_iff.mp
      ((r.marked_centralizer_of_seed_card hcard hz hzne).2.ge hkMc)
    rw [← hkz,mul_inv_cancel_right]
  let g := f.codRestrict a.fixedSubgroup hfix
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    exact (hf x).symm.trans ((congrArg (fun w : a.fixedSubgroup => ((w.val : I) : G)) h).trans (hf y))
  have hbound := _root_.primeRank_le_of_injective 3 g hg
  have e := residualQuotientEquiv H r.quotient.some
  let : IsElementaryAbelian 3 (Chapter1.XiQuotient K) :=
    IsElementaryAbelian.of_injective e.toMonoidHom e.injective
  have hrq : primeRank 3 (Chapter1.XiQuotient K) = 2 := by
    rw [← IsElementaryAbelian.log_card_eq_primeRank (p := 3),
      Nat.card_congr e.toEquiv,
      Chapter13.Section08.Components.Swapped.LinearThree.WreathModel.cubicBase_card]
    decide
  have hl : 2 ≤ primeRank 3 K := by
    rw [←hrq]
    exact primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup
  exact hl.trans hbound

/-- The literal quotient involution centralizer has three-rank at least two. -/
theorem ResidualInput.quotient_centralizer_three_rank_direct
    (hcard : Nat.card (centralInvolutions T) = 2) (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (e : (c.component ⧸ pCore 2 c.component) ≃* D)
    (hr : 2 ≤ primeRank 3 D) (ho : IsPGroup 2 (MulAut.Outer D))
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (hai : TwoCentralInner a) :
    ∃ t : D, orderOf t = 2 ∧ DoubleCoverCentralizer.TwoCentral t ∧
      2 ≤ primeRank 3 (centralizer ({t} : Set D)) := by
  obtain ⟨t,ht,htc,hact⟩ := quotient_twoCentral_of_inner c e a hai
  let q : c.component →* D := e.toMonoidHom.comp (QuotientGroup.mk' _)
  have hk : q.ker = pCore 2 c.component := by
    ext x
    change e (QuotientGroup.mk' _ x) = 1 ↔ _
    rw [e.map_eq_one_iff,QuotientGroup.mk'_apply,QuotientGroup.eq_one_iff]
  have hle : a.fixedSubgroup.map q ≤ centralizer ({t} : Set D) := by
    rintro x ⟨y,hy,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have hh := hact y
    rw [(MulAut.mem_fixedSubgroup _ _).mp hy] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  refine ⟨t,ht,htc,?_⟩
  have hlow := r.fixed_three_rank_of_quotient_direct c hcard hI hz hzne e hr ho a ha
  have he := ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel
    (by decide : Odd 3) q (by rw [hk]; exact pCore_isPGroup) a.fixedSubgroup
  rw [←he] at hlow
  exact hlow.trans (primeRank_mono 3 hle)

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
