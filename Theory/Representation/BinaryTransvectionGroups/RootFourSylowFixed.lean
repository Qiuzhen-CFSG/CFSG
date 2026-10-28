module

public import Theory.Representation.BinaryTransvectionGroups.Duality
public import Theory.SpecificGroups.BinaryLinear.SylowInvariantFixed
public import Theory.GroupTheory.SpecificGroups.KleinFourResidualCentralizer
import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models

/-!
# A moved root four-group excludes a common dual fixed vector

The forms of an actual common-center four-group are a nonzero invariant
subspace of the dual module. A full Sylow's fixed vectors lie in this
subspace. A two-perfect actor generating the four-group by commutators
fixes no nonzero form, so the actor and Sylow have no common dual fixed
vector. This uses the actual root subgroup and its normalizers.

Source application: Aschbacher--Smith12.7.18, printed p.845.
-/

public noncomputable section
open Subgroup BinaryLinear
namespace BinaryTransvectionGroups
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private theorem dual_onto : Function.Surjective (contragredient (V := V)) := by
  let : Finite (DualSpace V) := Finite.of_injective
    (fun f : DualSpace V => (f : V → ZMod 2)) DFunLike.coe_injective
  let : Finite (BinaryLinear.GL (DualSpace V)) := Finite.of_injective
    (fun g : BinaryLinear.GL (DualSpace V) => (g : DualSpace V → DualSpace V)) DFunLike.coe_injective
  let e : V ≃ₗ[ZMod 2] DualSpace V := LinearEquiv.ofFinrankEq _ _ (by
    rw [Subspace.dual_finrank_eq])
  let F := BinaryLinear.SmallParabolicLevi.linearGroupCongr e
  exact contragredient_injective.bijective_of_nat_card_le
    (Nat.card_congr F.toEquiv).symm.le |>.2

omit [Finite V] in
private theorem forms_stable (A : Subgroup (BinaryLinear.GL V)) (x : V)
    (g : BinaryLinear.GL V) (hn : g ∈ normalizer (A : Set (BinaryLinear.GL V))) (hx : g x = x)
    {f : DualSpace V} (hf : f ∈ rootForms A x) :
    contragredient g f ∈ rootForms A x := by
  have he : (contragredient g f) x = 0 := by
    have hix : g.symm x = x := by
      apply g.injective
      rw [g.apply_symm_apply,hx]
    change f (g.symm x) = 0
    rw [hix]
    exact hf.1
  apply (mem_rootForms he).mpr
  have hh := (mem_normalizer_iff.mp hn (transvection x f hf.1)).mp hf.2
  have hfc : f.comp g.symm.toLinearMap = contragredient g f := by ext v; rfl
  simpa only [transvection_conj,hx,hfc] using hh

private theorem normalizer_fixes_center (x : V) (hx : x ≠ 0)
    (A : Subgroup (BinaryLinear.GL V)) [IsKleinFour A]
    (hA : A ≤ radical (centerLine x))
    (g : BinaryLinear.GL V) (hg : g ∈ normalizer (A : Set (BinaryLinear.GL V))) : g x = x := by
  let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp
    (by rw [IsKleinFour.card_four]; decide)
  obtain ⟨t,ht⟩ := exists_ne (1 : A)
  have ht1 : (t : BinaryLinear.GL V) ≠ 1 := fun he => ht (Subtype.ext he)
  obtain ⟨v,hv⟩ : ∃ v : V, t.val v ≠ v := by
    by_contra! hfix
    exact ht1 (LinearEquiv.ext hfix)
  have hdisp : t.val v - v = x :=
    ((mem_centerLine_iff x _).mp ((hA t.property).2 v)).resolve_left (sub_ne_zero.mpr hv)
  have hconj : g*t.val*g⁻¹ ∈ A := (mem_normalizer_iff.mp hg t.val).mp t.property
  have hline := (hA hconj).2 (g v)
  have he : (g*t.val*g⁻¹) (g v) - g v = g x := by
    change g (t.val (g.symm (g v))) - g v = g x
    rw [g.symm_apply_apply,←map_sub,hdisp]
  rw [he] at hline
  exact ((mem_centerLine_iff x _).mp hline).resolve_left (fun hz => hx (g.map_eq_zero_iff.mp hz))

/-- The original residual and a full Sylow have no common fixed covector
if they normalize a fully moved common-center four-group. -/
theorem dual_fixedSpace_sup_sylow_eq_bot_of_root_four
    (x : V) (hx : x ≠ 0) (A J : Subgroup (BinaryLinear.GL V)) [IsKleinFour A]
    (hA : A ≤ radical (centerLine x)) (hJ : IsPPerfect 2 J)
    (hJN : J ≤ normalizer (A : Set (BinaryLinear.GL V))) (hmove : A = ⁅A,J⁆)
    (S : Sylow 2 (BinaryLinear.GL V)) (hSN : (S : Subgroup (BinaryLinear.GL V)) ≤ normalizer (A : Set (BinaryLinear.GL V))) :
    fixedSpace (dualGroup (J ⊔ (S : Subgroup (BinaryLinear.GL V)))) = ⊥ := by
  let E := rootForms A x
  have hJx (j : BinaryLinear.GL V) (hj : j ∈ J) : j x = x :=
    normalizer_fixes_center x hx A hA j (hJN hj)
  have hSx (s : BinaryLinear.GL V) (hs : s ∈ S) : s x = x :=
    normalizer_fixes_center x hx A hA s (hSN hs)
  have hroot : rootGroup A x = A := inf_eq_left.mpr hA
  have hEcard : Nat.card E = 4 := by
    rw [show E = rootForms A x from rfl,rootForms_card_eq A hx,hroot,IsKleinFour.card_four]
  have hE : E ≠ ⊥ := by
    intro he
    rw [he,Nat.card_unique] at hEcard
    omega
  let S' := S.mapSurjective (f := contragredient) dual_onto
  have hSE : (S' : Subgroup (BinaryLinear.GL (DualSpace V))) ≤ parabolic E := by
    rintro _ ⟨g,hg,rfl⟩ f
    constructor
    · intro hf
      have hh := forms_stable A x g⁻¹ (hSN (S.inv_mem hg)) (hSx g⁻¹ (S.inv_mem hg)) hf
      simpa only [map_inv,LinearEquiv.coe_inv,LinearEquiv.symm_apply_apply] using hh
    · exact forms_stable A x g (hSN hg) (hSx g hg)
  have hJE : Disjoint E (fixedSpace (dualGroup J)) := by
    apply Submodule.disjoint_def.mpr
    intro f hf hfix
    let t := transvection x f hf.1
    have ht : t ∈ A := hf.2
    have htc : t ∈ centralizer (J : Set (BinaryLinear.GL V)) := by
      apply mem_centralizer_iff.mpr
      intro j hj
      have hfj : contragredient j f = f := hfix _ ⟨j,hj,rfl⟩
      have hh : j*t*j⁻¹ = t := by
        have hc := transvection_conj j x f hf.1
        have hfc : f.comp j.symm.toLinearMap = f := hfj
        simpa only [hJx j hj,hfc] using hc
      exact mul_inv_eq_iff_eq_mul.mp hh
    have ht1 : t = 1 := by
      have he := kleinFour_inf_centralizer_eq_bot_of_twoPerfect A J hJ hJN hmove
      have hh : t ∈ A ⊓ centralizer (J : Set (BinaryLinear.GL V)) := ⟨ht,htc⟩
      rw [he] at hh
      exact hh
    ext v
    have he := congrArg (fun g : BinaryLinear.GL V => g v) ht1
    change v + f v • x = v at he
    exact (smul_eq_zero.mp (add_eq_left.mp he)).resolve_right hx
  have hz := fixedSpace_sup_sylow_eq_bot_of_invariant S' (dualGroup J) E hE hSE hJE
  simpa only [dualGroup,Subgroup.map_sup,S',Sylow.coe_mapSurjective] using hz

end BinaryTransvectionGroups
