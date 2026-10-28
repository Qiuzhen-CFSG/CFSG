module

public import Theory.GroupTheory.ReducedNormal.Representation
public import Theory.Representation.BinaryOffender.ActionImage

/-!
# Reducedness of the original conjugation action

The linear action of H on R₂(H) has exactly C_H(R₂(H)) as its kernel.
Its faithful image is therefore the defining reduced quotient, whose
two-core is trivial. The image of a normal actor is normal in this image,
so it also has trivial two-core.

This discharges the reduced actor action in Hypothesis D.3.2 for the
literal elementary section used in Aschbacher–Smith, Lemma 3.2.2,
combined manuscript of 1 March 2004, printed p.579.
-/

public section
open Subgroup
open scoped IsMulCommutative
open Representation.BinaryOffender
namespace Theory.GroupTheory.ReducedNormal
variable {G : Type*} [Group G]

/-- The reduced-module action retains its exact source centralizer kernel. -/
theorem representation_action_kernel (H : Subgroup G) :
    (actionHom (representation H)).ker = centralizer (ModuleGroup H : Set H) := by
  ext g
  rw [MonoidHom.mem_ker, actionHom_eq_one_iff, mem_centralizer_iff]
  constructor
  · intro hh x hx
    have he := congrArg (fun v : Additive (ModuleGroup H) => v.toMul.val)
      (hh (Additive.ofMul ⟨x, hx⟩))
    change g * x * g⁻¹ = x at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hh v
    apply congrArg Additive.ofMul
    apply Subtype.ext
    change g * v.toMul.val * g⁻¹ = v.toMul.val
    rw [← hh _ v.toMul.property, mul_inv_cancel_right]

/-- The faithful linear image is the actual reduced centralizer quotient. -/
theorem representation_action_twoCore_eq_bot (H : Subgroup G) :
    pCore 2 (actionImage (representation H)) = ⊥ := by
  let a := actionHom (representation H)
  let e := QuotientGroup.liftEquiv (centralizer (ModuleGroup H : Set H))
    (Representation.asGroupHom (representation H)).rangeRestrict_surjective
    (representation_action_kernel H).symm
  have hm := pCore_map_iso 2 e
  rw [(isPReduced_reducedPSubgroup (p := 2) (G := H)).quotient_pCore_eq_bot,
    Subgroup.map_bot] at hm
  exact hm.symm

/-- The original two-core stabilizes every seed in its reduced module. -/
theorem representation_twoCore_stabilizes (H : Subgroup G)
    (I : Submodule (ZMod 2) (Additive (ModuleGroup H))) :
    pCore 2 H ≤ subspaceStabilizer (representation H) I := by
  have hc : pCore 2 H ≤ (actionHom (representation H)).ker := by
    rw [representation_action_kernel]
    exact le_centralizer_iff.mp (reducedPSubgroup_le_centralizer_pCore 2 H)
  intro g hg v
  rw [(actionHom_eq_one_iff (representation H) g).mp (hc hg) v]

private theorem normal_actor_action_twoCore_eq_bot
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (X : Subgroup D) [X.Normal]
    (hc : pCore 2 (actionImage ρ) = ⊥) :
    pCore 2 (actionImage (ρ.comp X.subtype)) = ⊥ := by
  let A := actionSubgroup ρ X
  let : A.Normal := Normal.map inferInstance (actionHom ρ)
    ρ.asGroupHom.rangeRestrict_surjective
  have hA : pCore 2 A = ⊥ := by
    have hm : (pCore 2 A).map A.subtype ≤ pCore 2 (actionImage ρ) :=
      le_sSup ⟨inferInstance, pCore_isPGroup.map A.subtype⟩
    exact (map_eq_bot_iff_of_injective _ A.subtype_injective).mp
      (le_bot_iff.mp (hc ▸ hm))
  let σ : Representation (ZMod 2) X V := ρ.comp X.subtype
  have hk : (actionHom σ).ker = ((actionHom ρ).comp X.subtype).ker := by
    ext x
    change actionHom σ x = 1 ↔ actionHom ρ x = 1
    rw [actionHom_eq_one_iff, actionHom_eq_one_iff]
    rfl
  let e : actionImage σ ≃* A :=
    (QuotientGroup.quotientKerEquivOfSurjective (actionHom σ)
      σ.asGroupHom.rangeRestrict_surjective).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hk).trans (actionQuotientEquiv ρ X))
  have hm := pCore_map_iso 2 e
  rw [hA] at hm
  exact (map_eq_bot_iff_of_injective _ e.injective).mp hm

/-- Every original normal actor satisfies D.3.2's reduced action hypothesis. -/
theorem normal_actor_representation_twoCore_eq_bot (H : Subgroup G)
    (X : Subgroup H) [X.Normal] :
    pCore 2 (actionImage ((representation H).comp X.subtype)) = ⊥ :=
  normal_actor_action_twoCore_eq_bot (representation H) X
    (representation_action_twoCore_eq_bot H)

end Theory.GroupTheory.ReducedNormal
