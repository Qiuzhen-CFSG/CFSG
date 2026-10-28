module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.LocalNormality
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.Alternating.Aut

/-!
# Comparing the original A₅ quotient and module actions

Conjugation by the normalizer of L descends through O₂(L), and the chosen
quotient isomorphism transports this action to the actual A₅ carrier. On LT
it agrees with conjugation by the original five-point module action, since
both actions agree on every representative from L. The faithful isomorphism
S₅ ≃ Aut(A₅) then detects inner quotient action as even permutation action.

The final comparison discharges the coordinate transfer used by the even
Sylow-normalizer step in the proof of original 13.2.9.

Source: Aschbacher–Smith, 13.2.9, printed pp.880–881.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

/-- The actual normalizer action on the chosen two-core quotient. -/
noncomputable def quotientNormalizerAction :
    normalizer (L : Set G) →* MulAut (alternatingGroup (Fin 5)) :=
  (MulAut.congr d.quotient).toMonoidHom.comp
    ((quotientAut (pCore 2 L)).comp L.normalizerMonoidHom)

/-- The quotient action retains the original representative and conjugation. -/
theorem quotientNormalizerAction_mk (n : normalizer (L : Set G)) (l : L) :
    d.quotientNormalizerAction n (d.quotient (QuotientGroup.mk' (pCore 2 L) l)) =
      d.quotient (QuotientGroup.mk' (pCore 2 L) (L.normalizerMonoidHom n l)) := by
  change d.quotient (quotientAut (pCore 2 L) (L.normalizerMonoidHom n)
    (d.quotient.symm (d.quotient (QuotientGroup.mk' (pCore 2 L) l)))) = _
  rw [d.quotient.symm_apply_apply, quotientAut_apply_mk]

private theorem localActor_on_component (l : L) :
    d.localActor (inclusion (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) l) =
      (d.quotient (QuotientGroup.mk' (pCore 2 L) l)).val := by
  exact d.flag.action_agrees l (d.chosen.normalizes l.property)

/-- On LT the quotient action is conjugation by its original five-point image. -/
theorem quotientNormalizerAction_eq_localActor (t : (L ⊔ (T : Subgroup G) : Subgroup G)) :
    d.quotientNormalizerAction
        ⟨t, (sup_le L.le_normalizer d.normalizes_L) t.property⟩ =
      MulAut.conjNormal (d.localActor t) := by
  apply MulEquiv.ext
  intro a
  obtain ⟨l, rfl⟩ := (d.quotient.surjective.comp (QuotientGroup.mk'_surjective _)) a
  change d.quotientNormalizerAction
      ⟨t, (sup_le L.le_normalizer d.normalizes_L) t.property⟩
      (d.quotient (QuotientGroup.mk' (pCore 2 L) l)) = _
  rw [d.quotientNormalizerAction_mk]
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  simp only [Function.comp_apply]
  rw [←d.localActor_on_component, ←d.localActor_on_component,
    ←map_mul, ←map_inv, ←map_mul]
  apply congrArg d.localActor
  apply Subtype.ext
  rfl

/-- An inner action on the original quotient has even original module image. -/
theorem localActor_even_of_quotientNormalizerAction_inner
    (t : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hi : d.quotientNormalizerAction
      ⟨t, (sup_le L.le_normalizer d.normalizes_L) t.property⟩ ∈
        MulAut.innerSubgroup (alternatingGroup (Fin 5))) :
    d.localActor t ∈ alternatingGroup (Fin 5) := by
  rw [d.quotientNormalizerAction_eq_localActor] at hi
  obtain ⟨a, ha⟩ := hi
  have he : a.val = d.localActor t := by
    apply (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
      (by decide) (by decide)).1
    simpa only [MulAut.conjNormal_val] using ha
  exact he ▸ a.property

end CFSG.Quasithin.Chapter13.Section05.A5Source.Context
