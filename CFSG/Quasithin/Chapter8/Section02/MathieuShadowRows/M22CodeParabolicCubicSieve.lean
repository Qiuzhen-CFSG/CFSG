module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.OddLinearTwo.SmallImage
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.LinearThree
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168
public import GorensteinWalter.LinearRingEquiv
public import Theory.SpecificGroups.PSL2.CubicInverters
public import Theory.GroupAction.InvertedOddLift
public import Theory.GroupTheory.InvolutionCentralizerControl
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The odd-linear M22 parabolic sieve

An involution normalized by the actual maximal subgroup is centralized by
that subgroup. Odd rotations inverted by this involution lift through the
full maximal core with their exact orders. The cubic-only restriction
therefore holds in the marked odd-linear component. Its reflected tori
force field order seven, and the checked PSL₂(7) comparison gives the
binary PSL₃(2) diagram model with the original maximal overlap retained.

Source: Aschbacher--Smith 8.2.9, printed pp.720--721, refs/quasithin.pdf.
This discharges the odd-linear case of the nonsolvable model catalogue;
the original marked chief-section exclusion remains a later step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {X : Type*} [Group X] [Finite X]
set_option backward.isDefEq.respectTransparency false

omit [Finite X] in
/-- The marked cubic rotation restriction survives the full maximal-core quotient. -/
theorem parabolic_star_cubic_rotations
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (W : Subgroup X) [IsElementaryAbelian 2 W]
    (hcent : minimalParabolicMax S hP ≤ centralizer (W : Set X))
    (hrot : ∀ (v r : X), v ∈ W → v ≠ 1 → v*r*v⁻¹=r⁻¹ →
      ∀ p a : ℕ, p.Prime → p ≠ 2 → 0 < a → orderOf r = p^a →
        orderOf r = 3) :
    let q := QuotientGroup.mk' (minimalParabolicCore S hP)
    ∀ (v r : X ⧸ minimalParabolicCore S hP), v ∈ W.map q → v ≠ 1 →
      v*r*v⁻¹=r⁻¹ → ∀ p a : ℕ, p.Prime → p ≠ 2 → 0 < a →
        orderOf r = p^a → orderOf r = 3 := by
  let J := minimalParabolicCore S hP
  let q := QuotientGroup.mk' J
  dsimp only
  intro v r hv hv1 hi p a hp hp2 ha hr
  obtain ⟨w,hw,rfl⟩ := hv
  have hw1 : w ≠ 1 := fun he => hv1 (by rw [he,map_one])
  have hw2 : w^2=1 := elemPow_eq_one_of_isElementaryAbelian w hw
  have hker : ∀ x ∈ q.ker, MulAut.conj w x=x := by
    intro x hx
    have hxJ : x ∈ J := by simpa only [q,QuotientGroup.ker_mk'] using hx
    have hc := hcent ((minimalParabolicMax S hP).normalCore_le hxJ) w hw
    change w*x*w⁻¹=x
    rw [hc,mul_inv_cancel_right]
  obtain ⟨x,hx,hix⟩ := MulAut.exists_inverted_odd_of_fixed_kernel
    (MulAut.conj w) (MulAut.conj (q w)) q (QuotientGroup.mk'_surjective J)
    (fun x => by simp only [MulAut.conj_apply,map_mul,map_inv])
    (by rw [←map_pow,hw2,map_one]) hker (hp.odd_of_ne_two hp2).pow r hr hi
  have hh := hrot w x hw hw1 hix p a hp hp2 ha hx
  exact hr.trans (hx.symm.trans hh)

/-- The odd linear row gives the actual binary PSL₃(2) diagram model. -/
theorem parabolic_odd_linear_cubic_rotation_model
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) (hs : ¬Group.IsSolvable X)
    (K : Subgroup X) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (S : Subgroup X) = ⊤)
    (W : Subgroup X) [IsElementaryAbelian 2 W] (hWS : W ≤ S)
    (hout : ¬W ≤ minimalParabolicCore S hP)
    (hMW : minimalParabolicMax S hP ≤ normalizer (W : Set X))
    (hcard : Nat.card W = 2)
    (hrot : ∀ (v r : X), v ∈ W → v ≠ 1 → v*r*v⁻¹=r⁻¹ →
      ∀ p a : ℕ, p.Prime → p ≠ 2 → 0 < a → orderOf r = p^a →
        orderOf r = 3)
    (hm : SingleOddLinearModel (minimalParabolicMax S hP) K (S : Subgroup X)) :
    ClassicalGroup.IsPSL (sourceImage (minimalParabolicMax S hP) K) 3 2 ∧
        DiagramModel (minimalParabolicMax S hP) K (S : Subgroup X) 1 := by
  obtain ⟨p,d,hp,hp3,hd,hd2,hmod,F,hF,hfin,hsize,e,_⟩ := hm
  let : Fact p.Prime := ⟨hp⟩
  have hd' : d=1 ∨ d=2 := by omega
  have ho : Odd p := hp.odd_of_ne_two (by omega)
  by_cases hseven : p^d=7
  · let := Fintype.ofFinite F
    let eF : ZMod 7 ≃+* F := ZMod.ringEquivOfPrime F (by decide)
      (by simpa only [Nat.card_eq_fintype_card,hseven] using hsize)
    let e' := (e.trans (GorensteinWalter.psl2RingEquiv eF).symm).trans
      Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two
    have hbinary : ClassicalGroup.IsPSL
        (sourceImage (minimalParabolicMax S hP) K) 3 2 :=
      ⟨ZMod 2,inferInstance,inferInstance,by simp,⟨e'⟩⟩
    exact ⟨hbinary,source_binary_linear_three_model S hP hs K hK hgen
      (by decide : 0<1) (by simpa only [pow_one] using hbinary)⟩
  · have hlarge : 9<p^d := by
      rcases hd' with rfl | rfl
      · simp only [pow_one] at hmod hseven ⊢
        have hp9 : p≠9 := by intro he; exact (by decide : ¬Nat.Prime 9) (he ▸ hp)
        omega
      · nlinarith
    let J := minimalParabolicCore S hP
    let q := QuotientGroup.mk' J
    have hWN : (W.subgroupOf (S : Subgroup X)).Normal :=
      (normal_subgroupOf_iff_le_normalizer hWS).mpr
        ((minimalParabolicMax_spec S hP).2.trans hMW)
    have hcore : W ≤ (minimalParabolicMax S hP).pCoreIn 2 :=
      le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 W)
        (hWS.trans (minimalParabolicMax_spec S hP).2) hMW
    obtain ⟨_,t,ht,htW⟩ := Witnesses.OddLinearTwo.source_odd_image_involution
      S hP hs K hK hgen hp ho hp3 hd' hlarge ⟨F,hF,hfin,hsize,⟨e⟩⟩
      W hWS hWN hcore hout
    have hcent := hMW.trans (normalizer_le_centralizer_of_card_two W hcard)
    have hrotq := parabolic_star_cubic_rotations S hP W hcent hrot
    let j := (K.map q).subtype.comp e.symm.toMonoidHom
    have hj : Function.Injective j := Subtype.val_injective.comp e.symm.injective
    have hjt : j (e t) = (t : X ⧸ J) := by
      change (e.symm (e t)).val=t.val
      rw [e.symm_apply_apply]
    have ht1 : (t : X ⧸ J) ≠ 1 := by
      intro he
      have ht1 : t=1 := Subtype.ext he
      simp [ht1] at ht
    have hb : ∀ r : PSL(2,F), e t*r*(e t)⁻¹=r⁻¹ → ∀ r₀ a : ℕ,
        r₀.Prime → r₀≠2 → 0<a → orderOf r=r₀^a → orderOf r=3 := by
      intro r hi r₀ a hr₀ hr2 ha hr
      have hir : (t : X ⧸ J)*j r*(t : X ⧸ J)⁻¹=(j r)⁻¹ := by
        simpa only [map_mul,map_inv,hjt] using congrArg j hi
      have hord := orderOf_injective j hj r
      simpa only [hord] using hrotq t (j r) htW ht1 hir r₀ a hr₀ hr2 ha (hord.trans hr)
    have hq := Theory.PSL2.CubicInverters.field_card_eq_seven hp3 hd' hsize
      (by simpa only [hsize] using hmod) (e t) ((e.orderOf_eq t).trans ht) hb
    exact (hseven (hsize.symm.trans hq)).elim

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
