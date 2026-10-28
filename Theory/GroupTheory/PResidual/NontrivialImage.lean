module
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.PGroupCore

/-!
# Residual images in a group with trivial prime core

A nontrivial normal image in a finite quotient with trivial p-core cannot
have trivial p-residual: otherwise that normal image is a p-group.
The conclusion uses the original embedded residual and homomorphism.

Source application: Aschbacher--Smith 14.3.15, printed p.995.
-/

public section
open Subgroup
namespace Subgroup
variable {G Q : Type*} [Group G] [Group Q] [Finite G]

theorem embedded_pResidual_image_ne_bot_of_pCore_eq_bot
    (p : ℕ) (J : Subgroup G) [J.Normal] (f : G →* Q)
    (hf : Function.Surjective f) (hq : pCore p Q = ⊥) (hj : J.map f ≠ ⊥) :
    ((pResidual p J).map J.subtype).map f ≠ ⊥ := by
  let : Finite Q := Finite.of_surjective f hf
  intro he
  rw [map_embedded_pResidual] at he
  have hb : pResidual p (J.map f) = ⊥ :=
    (map_eq_bot_iff_of_injective _ (J.map f).subtype_injective).mp he
  have hp : IsPGroup p (J.map f) :=
    (isPGroup_quotient_pResidual p).of_equiv
      ((QuotientGroup.quotientMulEquivOfEq hb).trans QuotientGroup.quotientBot)
  have hn : (J.map f).Normal := Normal.map inferInstance f hf
  have hl : J.map f ≤ pCore p Q := le_sSup ⟨hn,hp⟩
  exact hj (le_bot_iff.mp (hq ▸ hl))
end Subgroup

