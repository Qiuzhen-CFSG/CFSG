module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelInterface
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.BinaryIdentification
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.QuotientAction

/-!
# Transport of the marked component action to concrete models

The action of the whole normalizer quotient on K/Z(K) is faithful and agrees
with inner conjugation on K*. Its central four-group fixes a genuine Sylow
two-subgroup in every identified model. Thus an intrinsic pointwise-fixer
calculation implies containment of the literal E* in K*, including central
covers. The Sylow center of the whole quotient cannot be cyclic.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
13.6.6, printed p.927. These are action transports, not model exclusions.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve
open A5Module
variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}
  {s : Marking L V} {T : Sylow 2 G}

/-- The faithful quotient action expressed on the specified concrete carrier. -/
noncomputable def modelAction (K : Subgroup (Gv (markedV s)))
    {Q : Type*} [Group Q] (e : NormalizerAction.componentImage K ≃* Q) :
    XStar K →* MulAut Q :=
  (MulAut.congr e).toMonoidHom.comp (quotientAction K)

omit [Finite G] in
/-- Transport preserves faithfulness, also for nontrivial central covers. -/
theorem modelAction_injective (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K)
    {Q : Type*} [Group Q] (e : NormalizerAction.componentImage K ≃* Q) :
    Function.Injective (modelAction K e) :=
  (MulAut.congr e).injective.comp (quotientAction_injective K hK)

omit [Finite G] in
/-- Elements of K* act by their own conjugation in the model. -/
theorem modelAction_component (K : Subgroup (Gv (markedV s)))
    {Q : Type*} [Group Q] (e : NormalizerAction.componentImage K ≃* Q)
    (k : NormalizerAction.componentImage K) :
    modelAction K e k = MulAut.conj (e k) := by
  have hk : quotientAction K k = MulAut.conj k := by
    ext x
    exact quotientAction_apply K k x
  change MulAut.congr e (quotientAction K k) = _
  rw [hk, MulAut.congr_conj]

omit [Finite G] in
/-- The full inner automorphism group lies in the action image. -/
theorem inner_le_modelAction_range (K : Subgroup (Gv (markedV s)))
    {Q : Type*} [Group Q] (e : NormalizerAction.componentImage K ≃* Q) :
    MulAut.innerSubgroup Q ≤ (modelAction K e).range := by
  rintro _ ⟨q, rfl⟩
  exact ⟨e.symm q, (modelAction_component K e (e.symm q)).trans
    (congrArg MulAut.conj (e.apply_symm_apply q))⟩

/-- Preserve the literal E* while transporting its pointwise fixed Sylow subgroup. -/
theorem exists_model_sylow_fixed (K : Subgroup (Gv (markedV s)))
    (a : ActionData s (T : Subgroup G) K)
    {Q : Type*} [Group Q] (e : NormalizerAction.componentImage K ≃* Q) :
    ∃ S : Sylow 2 Q, ∀ x ∈ EStar s K a.a_normalizes a.z_normalizes,
      ∀ y ∈ S, modelAction K e x y = y := by
  obtain ⟨P, hP⟩ := a.sylow
  let := componentImage_normal K
  obtain ⟨S, hS⟩ := P.exists_subgroupOf_eq_of_normal (NormalizerAction.componentImage K)
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  rintro x hx _ ⟨y, hy, rfl⟩
  change e (quotientAction K x (e.symm (e y))) = e y
  rw [e.symm_apply_apply]
  congr 1
  apply Subtype.ext
  rw [quotientAction_apply]
  have hyP : (y : XStar K) ∈ (P : Subgroup (XStar K)) := by
    change y ∈ (S : Subgroup (NormalizerAction.componentImage K)) at hy
    rw [hS] at hy
    exact hy
  obtain ⟨c, hc, he⟩ := a.central hx
  have hyI : (y : XStar K) ∈ NormalizerAction.sylowImage K (localT (T : Subgroup G) (markedV s)) :=
    hP ▸ hyP
  have hcomm := congrArg Subtype.val (mem_center_iff.mp hc ⟨y, hyI⟩)
  change (y : XStar K) * c.val = c.val * y at hcomm
  change c.val = x at he
  rw [he] at hcomm
  rw [← hcomm, mul_inv_cancel_right]

/-- An intrinsic pointwise-fixer theorem places the actual E* inside K*. -/
theorem EStar_le_component_of_model_fixers (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K)
    {Q : Type*} [Group Q] (e : NormalizerAction.componentImage K ≃* Q)
    (hinner : ∀ (S : Sylow 2 Q) (α : MulAut Q),
      (∀ y ∈ S, α y = y) → α ∈ MulAut.innerSubgroup Q) :
    EStar s K a.a_normalizes a.z_normalizes ≤ NormalizerAction.componentImage K := by
  obtain ⟨S, hS⟩ := exists_model_sylow_fixed K a e
  intro x hx
  apply (quotientAction_mem_inner_iff K hK x).mp
  obtain ⟨q, hq⟩ := hinner S (modelAction K e x) (hS x hx)
  refine ⟨e.symm q, ?_⟩
  apply (MulAut.congr e).injective
  rw [MulAut.congr_conj, e.apply_symm_apply]
  exact hq

/-- Only square-one pointwise fixers need be inner: every element of E*
has this order bound, including the identity. -/
theorem EStar_le_component_of_model_involutive_fixers (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K)
    {Q : Type*} [Group Q] (e : NormalizerAction.componentImage K ≃* Q)
    (hinner : ∀ (S : Sylow 2 Q) (α : MulAut Q), α ^ 2 = 1 →
      (∀ y ∈ S, α y = y) → α ∈ MulAut.innerSubgroup Q) :
    EStar s K a.a_normalizes a.z_normalizes ≤ NormalizerAction.componentImage K := by
  obtain ⟨S, hS⟩ := exists_model_sylow_fixed K a e
  intro x hx
  have hxpow : x ^ 2 = 1 := by
    have hdiv : Monoid.exponent (EStar s K a.a_normalizes a.z_normalizes) ∣ 2 := by
      rw [a.four.exponent_two]
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hdiv
      (⟨x,hx⟩ : EStar s K a.a_normalizes a.z_normalizes)
    exact congrArg Subtype.val h
  have hpow : modelAction K e x ^ 2 = 1 := by
    rw [← map_pow, hxpow, map_one]
  apply (quotientAction_mem_inner_iff K hK x).mp
  obtain ⟨q, hq⟩ := hinner S (modelAction K e x) hpow (hS x hx)
  refine ⟨e.symm q, ?_⟩
  apply (MulAut.congr e).injective
  rw [MulAut.congr_conj, e.apply_symm_apply]
  exact hq

omit [Finite G] in
/-- The source Sylow center contains an actual four-group and is not cyclic. -/
theorem sylow_center_not_cyclic (K : Subgroup (Gv (markedV s)))
    (a : ActionData s (T : Subgroup G) K)
    (P : Sylow 2 (XStar K))
    (hP : (P : Subgroup (XStar K)) = NormalizerAction.sylowImage K
      (localT (T : Subgroup G) (markedV s))) : ¬ IsCyclic (center P) := by
  intro hc
  let := hc
  let E := EStar s K a.a_normalizes a.z_normalizes
  let := a.four
  have hle : E ≤ (center P).map (P : Subgroup (XStar K)).subtype := by
    rw [hP]
    exact a.central
  let eC := (center P).equivMapOfInjective (P : Subgroup (XStar K)).subtype
    Subtype.val_injective
  let : IsCyclic ((center P).map (P : Subgroup (XStar K)).subtype) :=
    eC.isCyclic.mp hc
  exact IsKleinFour.not_isCyclic (Subgroup.isCyclic_of_le hle)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve
