module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairResidual
public import Theory.Representation.BinaryOffender.NormalLayerQuotient
public import Theory.Representation.SL2NaturalOffenders.NaturalPair
/-!
# The full action from a marked pair of natural modules

The fixed space of a normal actor is invariant under the whole group. The
marked quotient therefore extends to a full action, and its faithful normal
layer makes that action faithful whenever the layer is self-centralizing.
The quotient map and the original marked factor coordinates are preserved.
Source: Aschbacher--Smith B.6.9--10 and E.2.3; application to 13.6.14.
-/
public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceInduction.SourceTwoFactorCase.MarkedProduct
open QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

theorem linear_full_faithful_action
    (α : Representation (ZMod 2) G V) (I : Subgroup G) [I.Normal]
    (hI : centralizer (I : Set G) ≤ I)
    (d : SourceTwoFactorCase (α.comp I.subtype))
    (F : BinaryField) (c : d.MarkedProduct (linearNatural F 2)) :
    ∃ ρ : Representation (ZMod 2) G ((Fin 2 → F.Carrier) × (Fin 2 → F.Carrier)),
      Function.Injective ρ ∧
      (∀ g v, c.quotientMap (α g v) = ρ g (c.quotientMap v)) ∧
      ∀ (g : I) (a b : Fin 2 → F.Carrier),
        ρ (g : G) (a,b) = ((c.action.groupEquiv g).1.val.mulVec a,
          (c.action.groupEquiv g).2.val.mulVec b) := by
  let σ := SL2NaturalOffenders.naturalPair (F := F.Carrier)
  have hσ : Function.Injective σ := by
    intro a b hab
    apply Prod.ext
    · apply Subtype.ext
      apply Matrix.ext_iff_mulVec.mpr
      intro w
      exact congrArg Prod.fst (LinearMap.congr_fun hab (w,0))
    · apply Subtype.ext
      apply Matrix.ext_iff_mulVec.mpr
      intro w
      exact congrArg Prod.snd (LinearMap.congr_fun hab (0,w))
  let τ := σ.comp c.action.groupEquiv.toMonoidHom
  obtain ⟨ρ,hρ,he,hres⟩ := exists_faithful_action_of_normal_layer_quotient α I hI τ
    (hσ.comp c.action.groupEquiv.injective) c.quotientMap c.quotientMap_surjective
    c.quotientMap_ker c.quotientMap_action
  exact ⟨ρ,hρ,he,fun g a b => hres g (a,b)⟩
end CFSG.Quasithin.ChapterB.SourceInduction.SourceTwoFactorCase.MarkedProduct
