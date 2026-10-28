module
public import Theory.Representation.AlternatingFiveMovedPair.Mixed.Centralizer
public import Theory.Representation.AlternatingFiveMovedPair.Mixed.WreathAction
public import Theory.Representation.BinaryOffender.NormalizerExtension
public import Theory.GroupTheory.InvolutionOddProduct

/-!
# The full-normalizer estimate for the mixed moved A₅ pair

The faithful mixed action identifies its actor with A₅ × A₅. Its commutant
has fourth-power identity, so centralizing involutions vanish and elementary
normalizer actors embed in Aut(A₅ × A₅), of two-rank at most four.

Every involutive automorphism has an involutive lift through the literal
symmetric wreath action. The product of that lift with the given normalizer
involution centralizes the actor and has cube one. The elementary odd-product
conjugacy lemma therefore identifies their displacements. The wreath estimate
is at least twelve, strictly greater than twice the elementary rank bound.

This is the mixed tensor-pair branch of Aschbacher–Smith D.3.5, printed
pp.195–196. All statements concern the full linear normalizer of the literal
thirty-two dimensional model, including outer and factor-exchanging actors.
-/

public noncomputable section
open Subgroup
open Representation.BinaryOffender Representation.BinaryOffender.NaturalTensor
namespace Representation.AlternatingFiveMovedPair.Mixed
open SL2FourNatural SL2FourNatural.SemilinearNormalizer

@[expose] def imageEquiv : Pair ≃* actionImage action :=
  pairEquiv.symm.trans (MonoidHom.ofInjective
    (fun _ _ h => action_injective (congrArg Units.val h)))

lemma imageEquiv_val (a : Pair) : ((imageEquiv a).val).val = altAction a := by
  change action (pairEquiv.symm a) = altAction a
  rw [action_pairEquiv,pairEquiv.apply_symm_apply]

@[expose] def normalizerAut : linearNormalizer action →* MulAut Pair :=
  (MulAut.congr imageEquiv.symm).toMonoidHom.comp (actionImage action).normalizerMonoidHom

lemma normalizerAut_image (t : linearNormalizer action) (a : Pair) :
    imageEquiv (normalizerAut t a) =
      (actionImage action).normalizerMonoidHom t (imageEquiv a) := by
  change imageEquiv (imageEquiv.symm ((actionImage action).normalizerMonoidHom t (imageEquiv a))) = _
  exact imageEquiv.apply_symm_apply _

lemma normalizer_intertwines (t : linearNormalizer action) (a : Pair) (v : Space) :
    t.val.val (altAction a v) = altAction (normalizerAut t a) (t.val.val v) := by
  have h := congrArg (fun x : actionImage action => x.val) (normalizerAut_image t a)
  change (imageEquiv (normalizerAut t a)).val =
    t.val * (imageEquiv a).val * t.val⁻¹ at h
  have hm : t.val * (imageEquiv a).val = (imageEquiv (normalizerAut t a)).val * t.val :=
    mul_inv_eq_iff_eq_mul.mp h.symm
  have hv := congrArg (fun z : (Module.End (ZMod 2) Space)ˣ => z.val v) hm
  change t.val.val ((imageEquiv a).val.val v) =
    (imageEquiv (normalizerAut t a)).val.val (t.val.val v) at hv
  rw [imageEquiv_val a,imageEquiv_val (normalizerAut t a)] at hv
  exact hv

lemma normalizer_elementary_injective (A : Subgroup (linearNormalizer action))
    [IsElementaryAbelian 2 A] :
    Function.Injective (normalizerAut.comp A.subtype) := by
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  have he : a.val.val.val = 1 := by
    apply centralizer_involution_eq_one
    · intro g v
      rw [action_pairEquiv]
      have h := normalizer_intertwines a.val (pairEquiv g) v
      have ha' : normalizerAut a.val = 1 := ha
      simpa only [ha',MulAut.one_apply] using h
    · have h : a.val ^ 2=1 := elemPow_eq_one_of_isElementaryAbelian a.val a.property
      change normalizerRepresentation action a.val * normalizerRepresentation action a.val = 1
      rw [←map_mul,←pow_two,h,map_one]
  apply Subtype.ext
  apply Subtype.ext
  exact Units.ext he

lemma elementary_rank_le_four (A : Subgroup (linearNormalizer action))
    (hA : IsElementaryTwo A) : rank A ≤ 4 := by
  let : Finite Space := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) Space) := Finite.of_injective
    (fun f : Module.End (ZMod 2) Space => (f : Space → Space)) DFunLike.coe_injective
  let : IsElementaryAbelian 2 A := hA.2
  let f := normalizerAut.comp A.subtype
  have hf : Function.Injective f := normalizer_elementary_injective A
  have he : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hc := (primeRank_le_iff_elementary_card_le (MulAut Pair)).mp
    Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms.rank_le_four f.range he
  have hc' : Nat.card A ≤ 2^4 :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).le.trans hc
  have hh := Nat.log_mono_right (b:=2) hc'
  simpa only [rank,Nat.log_pow (by decide : 1<2)] using hh

private lemma displacement_eq_of_isConj (t u : (Module.End (ZMod 2) Space)ˣ)
    (h : IsConj t u) : operatorFixedCodim t.val = operatorFixedCodim u.val := by
  obtain ⟨b,hb⟩ := isConj_iff.mp h
  let e := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Space b
  apply operatorFixedCodim_eq_of_equiv t.val u.val e
  intro v
  have he : b*t=u*b := mul_inv_eq_iff_eq_mul.mp hb
  exact LinearMap.congr_fun (congrArg Units.val he) v

private lemma involution_lift_centralizes (t : linearNormalizer action) (ht : t^2=1)
    (w : Wreath)
    (hw : Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms.wreathHom w = normalizerAut t) :
    ∀ g : SL×SL, ∀ v,
      (t.val * wreathRepresentation.asGroupHom w).val (action g v) =
        action g ((t.val * wreathRepresentation.asGroupHom w).val v) := by
  intro g v
  have hs : normalizerAut t (normalizerAut t (pairEquiv g)) = pairEquiv g := by
    have h : normalizerAut t * normalizerAut t=1 := by
      rw [←pow_two,←map_pow,ht,map_one]
    have he := congrArg (fun f : MulAut Pair => f (pairEquiv g)) h
    simpa only [MulAut.mul_apply,MulAut.one_apply] using he
  have hauto : normalizerAut t
      (Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms.wreathHom w (pairEquiv g)) =
      pairEquiv g := by rw [hw]; exact hs
  change t.val.val (wreathRepresentation w (action g v)) =
    action g (t.val.val (wreathRepresentation w v))
  rw [action_pairEquiv g,wreath_intertwines w (pairEquiv g) v]
  exact (normalizer_intertwines t
    (Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms.wreathHom w (pairEquiv g))
    (wreathRepresentation w v)).trans
    (congrArg (fun a : Pair => altAction a (t.val.val (wreathRepresentation w v))) hauto)

/-- Every nonidentity involution in the full mixed normalizer moves at least
 twelve dimensions, including scalar corrections of outer or exchanged lifts. -/
lemma normalizer_involution_displacement (t : linearNormalizer action)
    (ht : t^2=1) (hne : t≠1) :
    12 ≤ operatorFixedCodim ((normalizerRepresentation action) t) := by
  obtain ⟨w,hw⟩ := Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms.wreathHom_surjective
    (normalizerAut t)
  have hw2 : w*w=1 := by
    apply Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms.wreathHom_injective
    rw [map_mul,hw,map_one,←pow_two,←map_pow,ht,map_one]
  let u := wreathRepresentation.asGroupHom w
  have hu2 : u^2=1 := by
    change wreathRepresentation.asGroupHom w ^ 2=1
    rw [←map_pow,pow_two,hw2,map_one]
  have ht2 : t.val^2=1 := congrArg Subtype.val ht
  let c := t.val*u
  have hcomm : ∀ g : SL×SL, ∀ v, c.val (action g v)=action g (c.val v) :=
    involution_lift_centralizes t ht w hw
  have hc4 : c^4=c := Units.ext (centralizer_fourth c.val hcomm)
  have hc3 : c^3=1 := mul_right_cancel (show c^3*c=1*c by
    simpa only [←pow_succ,one_mul] using hc4)
  have hodd : Odd (orderOf (t.val*u)) :=
    (by decide : Odd 3).of_dvd_nat (orderOf_dvd_of_pow_eq_one hc3)
  have hconj : IsConj t.val u := isConj_of_involutions_odd_product _ _ ht2 hu2 hodd
  have hwn : w≠1 := by
    intro h
    have hu : u=1 := by simp [u,h]
    rw [hu] at hconj
    exact hne (Subtype.ext (isConj_one_left.mp hconj))
  have hd := wreath_displacement_ge_twelve w hw2 hwn
  have he := displacement_eq_of_isConj t.val u hconj
  change operatorFixedCodim t.val.val = operatorFixedCodim (wreathRepresentation w) at he
  change 12 ≤ operatorFixedCodim t.val.val
  exact he.symm ▸ hd

/-- The mixed moved pair has fixed codimension strictly larger than twice the
rank of every nontrivial elementary two-subgroup of its full linear normalizer. -/
theorem normalizer_estimate (A : Subgroup (linearNormalizer action))
    (hA : IsElementaryTwo A) :
    2 * rank A < fixedCodim (normalizerRepresentation action) A := by
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨t,ht,htne⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have ht2 : t^2=1 := elemPow_eq_one_of_isElementaryAbelian t ht
  have hd := normalizer_involution_displacement t ht2 htne
  have hb := operatorFixedCodim_le_fixedCodim (normalizerRepresentation action) A ht
  have hr := elementary_rank_le_four A hA
  omega

/-- The source-assembly endpoint, with the common name for both moved-pair models. -/
theorem normalizer_strict_cubic_bound (A : Subgroup (linearNormalizer action))
    (hA : IsElementaryTwo A) :
    2 * rank A < fixedCodim (normalizerRepresentation action) A :=
  normalizer_estimate A hA

end Representation.AlternatingFiveMovedPair.Mixed
