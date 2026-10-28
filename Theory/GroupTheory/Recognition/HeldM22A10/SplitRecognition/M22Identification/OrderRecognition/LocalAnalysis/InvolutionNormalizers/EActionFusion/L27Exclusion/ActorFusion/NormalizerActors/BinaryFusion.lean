module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.L27Exclusion.ActorFusion.NormalizerActors.Parity
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
public import Theory.SpecificGroups.PSL3Two.InvolutionConjugacy

/-!
# The order-168 binary image on its even eight-group

Restriction to the invariant even space has a two-group kernel: an element
fixing this hyperplane pointwise has square one. The local S₄ remains faithful
on the hyperplane, so 24 divides the restriction image order. Since the whole
image has order 168, its restriction kernel divides seven and is trivial.
Restriction is therefore an isomorphism onto the full GL₃(2). An actual
isomorphism to PSL₃(2) transports its checked involution-conjugacy theorem.

Source: Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, Lemma 6, printed p.6.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
open LocalModelDichotomy
namespace L27NormalizerActors

private theorem evenSpace_card : Nat.card evenSpace = 8 := by
  change Nat.card {v : BinaryFour // parity v = 0} = 8
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private instance : IsElementaryAbelian 2 evenSpace where
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    intro v
    apply Subtype.ext
    have h : ∀ w : BinaryFour, w ^ 2 = 1 := by decide +kernel
    exact h v.val)

private theorem aut_even_card : Nat.card (MulAut evenSpace) = 168 := by
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow evenSpace 3
    (by simpa using evenSpace_card)]
  decide +kernel

private noncomputable def evenAutEquivPSL : MulAut evenSpace ≃* Matrix.PSL3Two.PSL := by
  let hex := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (p := 2) (n := 3) evenSpace (by rw [evenSpace_card]; decide)
  let f := Classical.choose hex
  have hf := Classical.choose_spec hex
  have hc : Nat.card (MulAut evenSpace) = Nat.card Matrix.PSL3Two.GeneralLinear := by
    rw [aut_even_card, ← Nat.card_congr Matrix.PSL3Two.equivGL.toEquiv,
      Nat.card_congr Matrix.PSL3Two.equiv.toEquiv, Matrix.PSL3Two.card_PSL]
  exact (MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf, hc⟩)).trans
    (Matrix.PSL3Two.equivGL.symm.trans Matrix.PSL3Two.equiv)

variable (H : Subgroup (MulAut BinaryFour))
  (hp : ∀ (f : H) (v : BinaryFour), parity (f.val v) = parity v)

private def restrictEven : H →* MulAut evenSpace where
  toFun f :=
    { toFun v := ⟨f.val v.val, (hp f v.val).trans v.property⟩
      invFun v := ⟨(f⁻¹).val v.val, (hp f⁻¹ v.val).trans v.property⟩
      left_inv v := Subtype.ext (f.val.symm_apply_apply v.val)
      right_inv v := Subtype.ext (f.val.apply_symm_apply v.val)
      map_mul' v w := Subtype.ext (f.val.map_mul v.val w.val) }
  map_one' := by apply MulEquiv.ext; intro v; apply Subtype.ext; rfl
  map_mul' f g := by apply MulEquiv.ext; intro v; apply Subtype.ext; rfl

private theorem restrictEven_ker_two : IsPGroup 2 (restrictEven H hp).ker := by
  intro f
  refine ⟨1, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply MulEquiv.ext
  intro v
  have hfix (w : BinaryFour) (hw : parity w = 0) : f.val.val w = w := by
    have h := congrArg (fun g : MulAut evenSpace => (g ⟨w, hw⟩).val) f.property
    exact h
  have hproduct : parity (f.val.val v * v) = 0 := by
    have h : ∀ u w : BinaryFour, parity u = parity w → parity (u * w) = 0 := by
      decide +kernel
    exact h _ _ (hp f.val v)
  change f.val.val (f.val.val v) = v
  apply mul_right_cancel (b := f.val.val v)
  calc
    f.val.val (f.val.val v) * f.val.val v = f.val.val (f.val.val v * v) :=
      (f.val.val.map_mul _ _).symm
    _ = f.val.val v * v := hfix _ hproduct
    _ = v * f.val.val v := mul_comm _ _

variable (hS : twistedAction.range ≤ H)

private def localActor : SymmetricFour →* H :=
  twistedAction.codRestrict H (fun s => hS ⟨s, rfl⟩)

include hp hS

private theorem local_restriction_injective :
    Function.Injective ((restrictEven H hp).comp (localActor H hS)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro s hs
  change s = 1
  have h : ∀ s : SymmetricFour,
      (∀ v : BinaryFour, parity v = 0 → twistedAction s v = v) → s = 1 := by
    decide +kernel
  apply h s
  intro v hv
  exact congrArg (fun g : MulAut evenSpace => (g ⟨v, hv⟩).val) hs

private theorem restriction_card_divisible : 24 ∣ Nat.card (restrictEven H hp).range := by
  let f := (restrictEven H hp).rangeRestrict.comp (localActor H hS)
  have hi : Function.Injective f := by
    intro s t he
    exact local_restriction_injective H hp hS (congrArg Subtype.val he)
  have hd := card_dvd_of_injective f hi
  simpa only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin,
    show Nat.factorial 4 = 24 from by decide] using hd

private theorem restriction_injective (h168 : Nat.card H = 168) :
    Function.Injective (restrictEven H hp) := by
  let q := restrictEven H hp
  have hc := q.ker.card_mul_index
  rw [index_ker, h168] at hc
  obtain ⟨m, hm⟩ := restriction_card_divisible H hp hS
  have hseven : Nat.card q.ker ∣ 7 := by
    refine ⟨m, ?_⟩
    change Nat.card q.range = 24 * m at hm
    rw [hm] at hc
    nlinarith
  obtain ⟨r, hr⟩ := (restrictEven_ker_two H hp).exists_card_dvd_pow
  have hone : Nat.card q.ker = 1 := Nat.eq_one_of_dvd_coprimes
    ((by decide : Nat.Coprime 7 2).pow_right r) hseven hr
  apply (MonoidHom.ker_eq_bot_iff q).mp
  exact q.ker.eq_bot_iff_card.mpr hone

private noncomputable def restrictionEquiv (h168 : Nat.card H = 168) :
    H ≃* MulAut evenSpace :=
  MulEquiv.ofBijective (restrictEven H hp)
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨restriction_injective H hp hS h168, h168.trans aut_even_card.symm⟩)

/-- The order-168 binary subgroup, with its actual local S₄ and invariant
parity, has one involution class. The proof constructs its PSL₃(2) isomorphism. -/
public theorem binary_involutions_conjugate (h168 : Nat.card H = 168)
    (x y : H) (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  let e := (restrictionEquiv H hp hS h168).trans evenAutEquivPSL
  have hc := Matrix.PSL3Two.isConj_of_orderOf_eq_two (e x) (e y)
    ((e.orderOf_eq x).trans hx) ((e.orderOf_eq y).trans hy)
  simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using
    e.symm.toMonoidHom.map_isConj hc

end L27NormalizerActors
end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
