module
public import Theory.GroupTheory.PGroup.SmallFrattiniLinearForms
public import Theory.GroupAction.FixedIndexTwoResidual
public import Theory.PGroupCore
public import Theory.Representation.ElementaryAbelianAction
public import Theory.Representation.BinaryPolarity.SymmetricSix

/-!
# A faithful six-point action above a small two-core

Let P be the self-centralizing two-core of a finite group X. If its Frattini
subgroup has order two, its center has order at most four, and P/Z(P) has
order sixteen, then the literal quotient X/P embeds in the symmetric group
on six letters.

Every automorphism fixes the order-two Frattini subgroup pointwise. Inside
the center this subgroup has index at most two, so the restriction image
is a two-group. The existing paired-action kernel theorem then makes the
kernel on P/Z(P) a two-group. Self-centralization identifies the ambient
conjugation kernel with P. The already constructed nondegenerate binary
commutator form is invariant under every automorphism; its faithful quotient
action embeds in Sp₄(2), hence in S₆.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma 13.5.15(6), printed p.921, combined manuscript of 1 March 2004.
The theorem is independent of the chapter setup and retains the actual core
and quotient maps used by its involution-centralizer application.
-/

public section
open Subgroup
open scoped IsMulCommutative

namespace SmallFrattini

/-- The central-quotient action kernel is a two-group when the Frattini
subgroup has order two and the center has order at most four. -/
theorem central_action_kernel_isPGroup
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hphi : Nat.card (frattini P) = 2) (hZ : Nat.card (center P) ≤ 4) :
    IsPGroup 2 (quotientAut (center P)).ker := by
  let Z := center P
  let D := (frattini P).subgroupOf Z
  have hle : frattini P ≤ Z := central_of_normal_card_two _ hphi
  have hD : Nat.card D = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
    exact hphi
  have hi : D.index ≤ 2 := by
    have h := D.card_mul_index
    rw [hD] at h
    change Nat.card Z ≤ 4 at hZ
    omega
  let r : MulAut P →* MulAut Z := MulAut.characteristic Z
  have hr : IsPGroup 2 r.range :=
    MulAut.isPGroup_range_of_fixed_index_le_two r (hP.to_subgroup Z) D hi (by
      intro a x hx
      apply Subtype.ext
      exact SmallNonabelianTwoGroup.frattini_two_fixed hphi a ⟨x.val, hx⟩)
  let B : Subgroup (MulAut Z × MulAut (P ⧸ Z)) := r.range.prod ⊥
  have hB : IsPGroup 2 B := by
    intro b
    obtain ⟨n, hn⟩ := hr ⟨b.val.1, b.property.1⟩
    refine ⟨n, Subtype.ext (Prod.ext ?_ ?_)⟩
    · exact congrArg Subtype.val hn
    · have hb : b.val.2 = 1 := b.property.2
      change b.val.2 ^ (2 ^ n) = 1
      rw [hb, one_pow]
  have hpre := hB.comap_of_ker_isPGroup (automorphismPair Z)
    (isPGroup_automorphism_pair_kernel Z (hP.to_subgroup Z))
  apply hpre.to_le
  intro a ha
  change automorphismPair Z a ∈ B
  rw [automorphismPair_apply]
  exact ⟨⟨a, rfl⟩, ha⟩

end SmallFrattini

namespace Subgroup

/-- The literal conjugation action on the central quotient of the two-core
has kernel exactly that core. -/
theorem pCore_central_action_kernel
    {X : Type*} [Group X] [Finite X]
    (hcentral : centralizer (pCore 2 X : Set X) ≤ pCore 2 X)
    (hphi : Nat.card (frattini (pCore 2 X)) = 2)
    (hZ : Nat.card (center (pCore 2 X)) ≤ 4) :
    ((quotientAut (center (pCore 2 X))).comp
      (MulAut.conjNormal : X →* MulAut (pCore 2 X))).ker = pCore 2 X := by
  let P := pCore 2 X
  have hP : IsPGroup 2 P := pCore_isPGroup
  let : IsElementaryAbelian 2 (P ⧸ center P) := SmallFrattini.centralElementary hP hphi
  let c : X →* MulAut P := MulAut.conjNormal
  let a := (quotientAut (center P)).comp c
  have hc : c.ker ≤ P := by
    intro x hx
    apply hcentral
    rw [mem_centralizer_iff]
    intro q hq
    have hf := congrArg (fun f : MulAut P => (f ⟨q, hq⟩ : X))
      (MonoidHom.mem_ker.mp hx)
    change x * q * x⁻¹ = q at hf
    exact (mul_inv_eq_iff_eq_mul.mp hf).symm
  have hk : IsPGroup 2 a.ker :=
    (SmallFrattini.central_action_kernel_isPGroup hP hphi hZ).comap_of_ker_isPGroup c
      (hP.to_le hc)
  apply le_antisymm (show a.ker ≤ pCore 2 X from le_sSup ⟨inferInstance, hk⟩)
  intro x hx
  rw [MonoidHom.mem_ker]
  apply MulEquiv.ext
  intro v
  obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (center P) v
  change quotientAut (center P) (c x) (QuotientGroup.mk' (center P) q) =
    QuotientGroup.mk' (center P) q
  rw [quotientAut_apply_mk]
  change QuotientGroup.mk' (center P) ((⟨x, hx⟩ : P) * q * (⟨x, hx⟩ : P)⁻¹) = _
  rw [map_mul, map_mul, map_inv,
    mul_comm (QuotientGroup.mk' (center P) (⟨x, hx⟩ : P))
      (QuotientGroup.mk' (center P) q), mul_inv_cancel_right]

/-- A self-centralizing two-core with a small Frattini subgroup and center
has a faithful six-point quotient action when its central quotient has order sixteen. -/
theorem exists_injective_six_action_of_pCore
    {X : Type*} [Group X] [Finite X]
    (hcentral : centralizer (pCore 2 X : Set X) ≤ pCore 2 X)
    (hphi : Nat.card (frattini (pCore 2 X)) = 2)
    (hZ : Nat.card (center (pCore 2 X)) ≤ 4)
    (hquot : Nat.card (pCore 2 X ⧸ center (pCore 2 X)) = 16) :
    ∃ f : (X ⧸ pCore 2 X) →* Equiv.Perm (Fin 6), Function.Injective f := by
  classical
  let P := pCore 2 X
  have hP : IsPGroup 2 P := pCore_isPGroup
  let E := P ⧸ center P
  let : IsElementaryAbelian 2 E := SmallFrattini.centralElementary hP hphi
  let a : X →* MulAut E := (quotientAut (center P)).comp MulAut.conjNormal
  have hk : a.ker = P := pCore_central_action_kernel hcentral hphi hZ
  let b : (X ⧸ P) →* MulAut E := QuotientGroup.lift P a hk.ge
  have hb : Function.Injective b :=
    (QuotientGroup.injective_lift_iff P a hk.ge).mpr hk.symm
  let : MulDistribMulAction (X ⧸ P) E := MulDistribMulAction.compHom E b
  let ρ := Representation.ofElementaryAbelianAction (A := X ⧸ P) (G := E) (p := 2)
  have hρ : Function.Injective ρ := by
    intro x y hxy
    apply hb
    apply MulEquiv.ext
    intro v
    exact congrArg Additive.toMul (LinearMap.congr_fun hxy (Additive.ofMul v))
  have hd : Module.finrank (ZMod 2) (Additive E) = 4 := by
    have hc : Nat.card (Additive E) = 16 := (Nat.card_congr Additive.toMul).trans hquot
    rw [@Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E)] at hc
    rw [Nat.card_eq_fintype_card, ZMod.card] at hc
    exact Nat.pow_right_injective (by decide : 1 < 2) hc
  apply BinaryPolarity.exists_injective_six_action_of_form ρ hρ hd
    (SmallFrattini.centralBilinearForm hP hphi)
    (SmallFrattini.centralBilinearForm_isAlt hP hphi)
    (SmallFrattini.centralBilinearForm_nondegenerate hP hphi)
  intro x u v
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective P x
  exact SmallFrattini.centralBilinearForm_invariant hP hphi (MulAut.conjNormal x)
    u.toMul v.toMul

end Subgroup
