module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelInterface
public import Theory.GroupAction.PerfectCentralQuotient
/-!
# The faithful four-group on the central quotient

Perfectness makes the action on K/Z(K) faithful. Under the canonical
identification with K* inside N(K)/C(K), this is ordinary conjugation.
Restricting the supplied Sylow subgroup to the normal component image
therefore exhibits a faithful four-group fixing an actual Sylow subgroup
of K* pointwise. The argument includes components with nontrivial center.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.6.6, printed p.927.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve
open A5Module

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions
variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}

/-- The faithful component action, transported through K/Z(K) ≃ K*. -/
noncomputable def quotientAction {v : G} (K : Subgroup (Gv v)) :
    XStar K →* MulAut (NormalizerAction.componentImage K) :=
  (MulAut.centralQuotientAction (NormalizerAction.componentCentralQuotientEquiv K)).comp
    (NormalizerAction.action K)

omit [Finite G] in
theorem quotientAction_injective {v : G} (K : Subgroup (Gv v))
    (hK : IsComponent (Gv v) K) : Function.Injective (quotientAction K) := by
  let : IsQuasisimple K := hK.2
  exact MulAut.centralQuotientAction_comp_injective _ _ (NormalizerAction.action_injective K)

omit [Finite G] in
/-- Innerness on K* is equivalent to membership in the embedded K*. -/
theorem quotientAction_mem_inner_iff {v : G} (K : Subgroup (Gv v))
    (hK : IsComponent (Gv v) K) (x : XStar K) :
    quotientAction K x ∈ MulAut.innerSubgroup (NormalizerAction.componentImage K) ↔
      x ∈ NormalizerAction.componentImage K := by
  let : IsQuasisimple K := hK.2
  rw [← NormalizerAction.action_mem_inner_iff]
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨l, hl⟩ := (MulAut.centralQuotientAction_inner_iff
      (NormalizerAction.componentCentralQuotientEquiv K) (NormalizerAction.action K x)).mp
        ⟨k, hk.symm⟩
    exact ⟨l, hl.symm⟩
  · rintro ⟨k, hk⟩
    refine ⟨NormalizerAction.componentCentralQuotientEquiv K
      (QuotientGroup.mk' (center K) k), ?_⟩
    change _ = MulAut.centralQuotientAction (NormalizerAction.componentCentralQuotientEquiv K)
      (NormalizerAction.action K x)
    rw [← hk, MulAut.centralQuotientAction_conj]

omit [Finite G] in
theorem quotientAction_apply {v : G} (K : Subgroup (Gv v))
    (x : XStar K) (k : NormalizerAction.componentImage K) :
    (quotientAction K x k : XStar K) = x * k * x⁻¹ := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (NormalizerAction.C K) x
  obtain ⟨q, rfl⟩ := (NormalizerAction.componentCentralQuotientEquiv K).surjective k
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center K) q
  change (MulAut.centralQuotientAction (NormalizerAction.componentCentralQuotientEquiv K)
    (NormalizerAction.action K (NormalizerAction.quotient K n))
    (NormalizerAction.componentCentralQuotientEquiv K (QuotientGroup.mk' (center K) y)) : XStar K) = _
  rw [MulAut.centralQuotientAction_apply, NormalizerAction.action_quotient,
    NormalizerAction.componentCentralQuotientEquiv_mk,
    NormalizerAction.componentCentralQuotientEquiv_mk]
  change NormalizerAction.quotient K _ = NormalizerAction.quotient K n *
    NormalizerAction.quotient K (inclusion K.le_normalizer y) * (NormalizerAction.quotient K n)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1

omit [Finite G] in
theorem componentImage_normal {v : G} (K : Subgroup (Gv v)) : (NormalizerAction.componentImage K).Normal := by
  change ((K.subgroupOf (X K)).map (NormalizerAction.quotient K)).Normal
  exact (inferInstance : (K.subgroupOf (X K)).Normal).map _
    (QuotientGroup.mk'_surjective (NormalizerAction.C K))

/-- The source central four-group yields actual pointwise Sylow fixers on K*. -/
theorem exists_fixed_four {s : Marking L V} {T : Sylow 2 G}
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K) :
    ∃ (S : Sylow 2 (NormalizerAction.componentImage K))
      (A : Subgroup (MulAut (NormalizerAction.componentImage K))),
      IsKleinFour A ∧ ∀ α ∈ A, ∀ x ∈ S, α x = x := by
  let E := EStar s K a.a_normalizes a.z_normalizes
  let A := E.map (quotientAction K)
  let e := E.equivMapOfInjective (quotientAction K) (quotientAction_injective K hK)
  have hA : IsKleinFour A := {
    card_four := (Nat.card_congr e.toEquiv).symm.trans a.four.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv e).symm.trans a.four.exponent_two }
  obtain ⟨P, hP⟩ := a.sylow
  let := componentImage_normal K
  obtain ⟨S, hS⟩ := P.exists_subgroupOf_eq_of_normal (NormalizerAction.componentImage K)
  refine ⟨S, A, hA, ?_⟩
  rintro _ ⟨z, hz, rfl⟩ x hx
  apply Subtype.ext
  rw [quotientAction_apply]
  have hxP : (x : XStar K) ∈ (P : Subgroup (XStar K)) := by
    change x ∈ (S : Subgroup (NormalizerAction.componentImage K)) at hx
    rw [hS] at hx
    exact hx
  obtain ⟨c, hc, he⟩ := a.central hz
  have hxI : (x : XStar K) ∈ NormalizerAction.sylowImage K (localT (T : Subgroup G) (markedV s)) :=
    hP ▸ hxP
  have hcomm := congrArg Subtype.val (mem_center_iff.mp hc ⟨x, hxI⟩)
  change (x : XStar K) * c.val = c.val * x at hcomm
  change c.val = z at he
  rw [he] at hcomm
  rw [← hcomm, mul_inv_cancel_right]


/-- Transport the fixed four-group to any specified concrete central quotient model. -/
theorem exists_fixed_four_of_equiv {s : Marking L V} {T : Sylow 2 G}
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K) {Q : Type*} [Group Q]
    (e : NormalizerAction.componentImage K ≃* Q) :
    ∃ (S : Sylow 2 Q) (A : Subgroup (MulAut Q)),
      IsKleinFour A ∧ ∀ α ∈ A, ∀ x ∈ S, α x = x := by
  obtain ⟨S, A, hA, hfix⟩ := exists_fixed_four K hK a
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let A' := A.map (MulAut.congr e).toMonoidHom
  let eA := A.equivMapOfInjective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective
  refine ⟨S', A', ⟨(Nat.card_congr eA.toEquiv).symm.trans hA.card_four,
    (Monoid.exponent_eq_of_mulEquiv eA).symm.trans hA.exponent_two⟩, ?_⟩
  rintro _ ⟨α, hα, rfl⟩ x ⟨y, hy, rfl⟩
  change e (α (e.symm (e y))) = e y
  rw [e.symm_apply_apply, hfix α hα y hy]

/-- Trivial odd core identifies the central quotient with the literal two-core quotient. -/
noncomputable def componentImageEquivTwoCoreQuotient {v : G}
    (K : Subgroup (Gv v)) (hK : IsComponent (Gv v) K)
    (hodd : pPrimeCore 2 (Gv v) = ⊥) :
    NormalizerAction.componentImage K ≃* (K ⧸ pCore 2 K) := by
  let : IsQuasisimple K := hK.2
  exact (NormalizerAction.componentCentralQuotientEquiv K).symm.trans
    (QuotientGroup.quotientMulEquivOfEq
      (IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot hodd K)))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions
