module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.McL.ThreeCoverLocalLifts.Elements
public import Theory.GroupTheory.CentralThreeInvertedPlane
public import Theory.GroupTheory.Covering

/-!
# The concrete two-local elementary-nine lift in a McL three-cover

The marked cubic generators in the actual ATLAS permutation carrier
centralize the defining nonidentity involution. An order-four word inverts
one coordinate and fixes the other; a second word inverts the other
coordinate. These checked relations force commuting cubic lifts through
any central three-group kernel. The involution lifts uniquely and centralizes
the resulting nine, so its cyclic subgroup is the required two-local seed.

This supplies the McL input to Aschbacher--Smith A.2.19, printed p.41
(PDF52). I.2.1, printed p.409, uses an extension of E₃⁴ by A₆ to obtain
ordinary three-rank. The direct construction here establishes the stronger
local conclusion used in A.2.19, without any assumed splitting, local rank,
McL order, multiplier, or comparison with a different McL model.

The nontrivial-center hypothesis is retained in the cover theorem: it is
what lets the consumer adjoin a central cubic element and obtain local rank
three. No non-quasithinness assertion is made about simple McL.
-/

namespace Sporadic.LeechRelated.McL.ThreeCoverLocal

/-- The marked elementary nine in the actual permutation carrier. -/
@[expose] public def e9Embedding : Multiplicative (ZMod 3 × ZMod 3) →* Carrier :=
  MonoidHom.cubicPairHom x y x_cube y_cube xy

/-- The nine coordinate products have distinct action on letter zero. -/
public theorem e9Embedding_injective : Function.Injective e9Embedding := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro a ha
  have h : ∀ b : Multiplicative (ZMod 3 × ZMod 3),
      (e9Embedding b : Equiv.Perm (Fin 275)) 0 = 0 → b = 1 := by
    decide +kernel
  exact h a (congrArg (fun g : Carrier => (g : Equiv.Perm (Fin 275)) 0) ha)

end Sporadic.LeechRelated.McL.ThreeCoverLocal

namespace Sporadic.LeechRelated.McL
open Theory.GroupTheory

/-- Every nontrivial central three-cover of the literal McL carrier contains
an elementary nine independent of the center in a nontrivial two-local. -/
public theorem exists_three_cover_local_lift
    {G : Type*} [Group G] [Finite G] [IsQuasisimple G]
    (hZ : IsPGroup 3 (Subgroup.center G)) (_hZne : Subgroup.center G ≠ ⊥)
    (e : G ⧸ Subgroup.center G ≃* Carrier) :
    ∃ (Q : Subgroup G) (f : Multiplicative (ZMod 3 × ZMod 3) →* G),
      Q ≠ ⊥ ∧ IsPGroup 2 Q ∧
      Function.Injective ((QuotientGroup.mk' (Subgroup.center G)).comp f) ∧
      ∀ a, f a ∈ Subgroup.normalizer (Q : Set G) := by
  let q : G →* Carrier := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center G))
  have hq : Function.Surjective q :=
    e.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center G))
  have hker : q.ker = Subgroup.center G := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hc : q.ker ≤ Subgroup.center G := hker.le
  have hp : IsPGroup 3 q.ker := hker.symm ▸ hZ
  obtain ⟨Q, f, hQne, hQ, hf, hn⟩ := q.exists_two_local_cubicPair_lift hq hc hp
    ThreeCoverLocal.x ThreeCoverLocal.y ThreeCoverLocal.r ThreeCoverLocal.s ThreeCoverLocal.t
    ThreeCoverLocal.x_cube ThreeCoverLocal.y_cube ThreeCoverLocal.xy
    ThreeCoverLocal.e9Embedding_injective
    ThreeCoverLocal.r_four ThreeCoverLocal.rx
    ((mul_inv_eq_iff_eq_mul).mp ThreeCoverLocal.ry)
    ThreeCoverLocal.sy ThreeCoverLocal.t_square ThreeCoverLocal.t_ne_one
    ThreeCoverLocal.xt ThreeCoverLocal.yt
  refine ⟨Q, f, hQne, hQ, ?_, hn⟩
  intro a b hab
  apply hf
  exact congrArg e hab

end Sporadic.LeechRelated.McL
