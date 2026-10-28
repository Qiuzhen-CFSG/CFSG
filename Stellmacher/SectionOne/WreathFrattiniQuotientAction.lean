module
public import Theory.GroupTheory.PGroup.FrattiniActionImage
public import Theory.Frattini.PGroup
public import BenderSuzuki.External.Huppert.IV.Residual
public import Stellmacher.SectionOne.WreathCoatomOddCore

/-!
# Wreath coatom control on a normal two-group quotient

Let Q and V be normal subgroups of a finite group P, with Q a two-group,
and fix a surjection f:P→K with kernel Q and wreath model SL₂(2) ≀ C₂.
Suppose the image of A is an elementary four normal in a supplied Sylow
of K. If N has relative index dividing two in Q and [N,A]≤V, then the
actual two-residual of P acts trivially on Q/(V∩Q), so [Q,O²(P)]≤V.
The supplied quotient-conjugation action and its formula are retained.
Neither N≤Q nor V≤Q is needed, since subgroupOf uses the actual intersections.

Compose this action with the action on the Frattini quotient W. Inner
conjugations by Q vanish on the elementary abelian W, so the action descends
through the exact f. The image of N∩Q is a fixed subgroup of index at most
two. The wreath coatom theorem gives a two-group action image on W, and the
Burnside basis-kernel transfer lifts this to Q/(V∩Q). The defining minimality
of O²(P) kills that action. Finally, the literal quotient-conjugation formula
lifts triviality to the ambient commutator bound.

Source: Stellmacher (10.1), printed p.60/PDF p.50 of
`refs/files/stellmacher-n-group.pdf`, the exclusion of alternative (5).
This gives the action transfer behind the source's noncentral-chief-factor
contradiction; geometric normality, index, and commutator data are supplied
by the Section Ten consumer, without a chief-series assumption.
-/

open Subgroup BenderSuzuki.External
open scoped IsMulCommutative commutatorElement

universe u
namespace Stellmacher.SectionOne

public theorem wreath_residual_commutator_le_of_fixed_coatom
    {P K : Type u} [Group P] [Finite P] [Group K] [Finite K]
    (Q V : Subgroup P) [Q.Normal] [V.Normal] (hQ : IsPGroup 2 Q)
    (f : P →* K) (hsurj : Function.Surjective f) (hkernel : f.ker = Q)
    (model : Nonempty (K ≃* Later.SL2TwoWreathC2))
    (S : Sylow 2 K) (A N : Subgroup P)
    (hAS : A.map f ≤ S) (hAN : ((A.map f).subgroupOf (S : Subgroup K)).Normal)
    (hAE : IsElementaryAbelian 2 (A.map f)) (hAc : Nat.card (A.map f) = 4)
    (hindex : N.relIndex Q ∣ 2) (hcomm : ⁅N,A⁆ ≤ V)
    (action : P →* MulAut (Q ⧸ V.subgroupOf Q))
    (hformula : ∀ actor : P, ∀ point : Q,
      action actor (QuotientGroup.mk' (V.subgroupOf Q) point) =
        QuotientGroup.mk' (V.subgroupOf Q) (MulAut.conjNormal actor point)) :
    ⁅Q, hktPResidual 2 P⁆ ≤ V := by
  let B := Q ⧸ V.subgroupOf Q
  let W := B ⧸ frattini B
  let qV : Q →* B := QuotientGroup.mk' (V.subgroupOf Q)
  let qPhi : B →* W := QuotientGroup.mk' (frattini B)
  let q : Q →* W := qPhi.comp qV
  have hq : Function.Surjective q :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hB : IsPGroup 2 B := hQ.of_surjective qV (QuotientGroup.mk'_surjective _)
  let _ : Fact (IsPGroup 2 B) := ⟨hB⟩
  let _ : IsElementaryAbelian 2 W := isElementaryAbelian_quotient_frattini
  let actionPhi := (Subgroup.quotientAut (frattini B)).comp action
  have hPhi (actor : P) (point : Q) :
      actionPhi actor (q point) = q (MulAut.conjNormal actor point) := by
    change Subgroup.quotientAut (frattini B) (action actor) (qPhi (qV point)) = _
    rw [Subgroup.quotientAut_apply_mk, hformula]
    rfl
  have hkill : f.ker ≤ actionPhi.ker := by
    rw [hkernel]
    intro actor hactor
    apply MulEquiv.ext
    intro point
    obtain ⟨point, rfl⟩ := hq point
    rw [hPhi]
    change q (⟨actor,hactor⟩ * point * ⟨actor,hactor⟩⁻¹) = q point
    simp only [map_mul, map_inv]
    simp [mul_comm]
  let descended := f.liftOfSurjective hsurj ⟨actionPhi,hkill⟩
  have hcompat (actor : P) : descended (f actor) = actionPhi actor :=
    MonoidHom.liftOfRightInverse_comp_apply f (Function.surjInv hsurj)
      (Function.rightInverse_surjInv hsurj) ⟨actionPhi,hkill⟩ actor
  let _ : MulDistribMulAction K W := MulDistribMulAction.compHom W descended
  let C := (N.subgroupOf Q).map q
  have hCindex : C.index ≤ 2 := by
    apply Nat.le_of_dvd (by decide : 0 < 2)
    exact ((N.subgroupOf Q).index_map_dvd hq).trans hindex
  have hfixed : ∀ actor ∈ A.map f, ∀ point ∈ C, actor • point = point := by
    rintro actor ⟨actor, hactor, rfl⟩ point ⟨point, hpoint, rfl⟩
    change descended (f actor) (q point) = q point
    rw [hcompat, hPhi]
    apply congrArg qPhi
    apply QuotientGroup.eq_iff_div_mem.mpr
    change actor * (point : P) * actor⁻¹ / (point : P) ∈ V
    rw [commutator_comm] at hcomm
    simpa only [commutatorElement_def, div_eq_mul_inv, Subgroup.coe_subtype] using
      hcomm (commutator_mem_commutator hactor hpoint)
  have heq : MulDistribMulAction.toMulAut K W = descended := by
    ext actor point
    rfl
  have hdescended : IsPGroup 2 descended.range := by
    rw [← heq]
    exact wreath_action_image_isTwoGroup_of_fixed_coatom
      model S (A.map f) hAS hAN hAE hAc C hCindex hfixed
  have hPhiImage : IsPGroup 2 actionPhi.range := by
    apply hdescended.to_le
    rintro image ⟨actor,rfl⟩
    exact ⟨f actor,hcompat actor⟩
  have hfull := action.isPGroup_range_of_frattini_range hB hPhiImage
  have hres : hktPResidual 2 P ≤ action.ker :=
    hktPResidual_le action.ker inferInstance
      (hfull.of_equiv (QuotientGroup.quotientKerEquivRange action).symm)
  rw [commutator_comm]
  apply commutator_le.mpr
  intro actor hactor point hpoint
  have hfix := DFunLike.congr_fun (hres hactor)
    (QuotientGroup.mk' (V.subgroupOf Q) ⟨point,hpoint⟩)
  rw [hformula] at hfix
  have hm := QuotientGroup.eq_iff_div_mem.mp hfix
  change actor * point * actor⁻¹ / point ∈ V at hm
  simpa only [commutatorElement_def, div_eq_mul_inv] using hm

end Stellmacher.SectionOne
