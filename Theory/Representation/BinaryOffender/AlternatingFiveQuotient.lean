module
public import Theory.Representation.OrthogonalFourMinusRankOne.FivePoint.Ambient
public import Theory.Representation.BinaryOffender.NormalLayerQuotient
public import Theory.Representation.BinaryPermutation.Faithful
/-!
# The full five-point quotient from an actual natural A5 layer

A surjective natural quotient with its exact fixed kernel inherits the full
ambient action. Faithfulness on the self-centralizing normal A5 layer makes
that action faithful. The checked binary natural normalizer gives a five-point
permutation action, and properness of A5 makes its image all of S5.
The original quotient map and intertwiner are retained throughout.

Source application: Aschbacher–Smith C.1.24 and E.2.3(3), pp.129 and217.
-/
public section
open Subgroup Representation Representation.BinaryOffender
set_option backward.isDefEq.respectTransparency false
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

theorem exists_five_quotient_of_natural_layer
    (α : Representation (ZMod 2) G V) (L : Subgroup G) [L.Normal]
    (hL : centralizer (L:Set G) ≤ L) (hne : L ≠ ⊤)
    (e : L ≃* alternatingGroup (Fin 5))
    (f : V →ₗ[ZMod 2] BinaryPermutation.natural (Fin 5)) (hf : Function.Surjective f)
    (hk : f.ker = fixedSpace α L)
    (he : ∀ (g : L) v, f (α (g:G) v) =
      BinaryPermutation.naturalRepresentation (Fin 5) (e g) (f v)) :
    ∃ p : G →* Equiv.Perm (Fin 5), Function.Bijective p ∧
      (∀ g v, f (α g v) = BinaryPermutation.naturalRepresentation (Fin 5) (p g) (f v)) ∧
      (∀ g:L,p g = (e g:Equiv.Perm (Fin 5))) := by
  let τ := (BinaryPermutation.naturalRepresentation (Fin 5)).comp
    ((alternatingGroup (Fin 5)).subtype.comp e.toMonoidHom)
  have hτ : Function.Injective τ :=
    (BinaryPermutation.naturalRepresentation_injective (Fin 5) (by decide)).comp
      ((alternatingGroup (Fin 5)).subtype_injective.comp e.injective)
  obtain ⟨ρ,hρ,hfρ,hρL⟩ := exists_faithful_action_of_normal_layer_quotient α L hL τ hτ f hf hk he
  obtain ⟨p,hp,hep,hpL⟩ := OrthogonalFourMinus.FivePoint.exists_ambient_permutation
    ρ L e (LinearEquiv.refl _ _) (fun g v => hρL g v) hρ
  have hmap : L.map p = alternatingGroup (Fin 5) := by
    ext x
    constructor
    · rintro ⟨g,hg,rfl⟩
      exact hpL ⟨g,hg⟩ ▸ (e ⟨g,hg⟩).property
    · intro hx
      obtain ⟨g,hg⟩ := e.surjective ⟨x,hx⟩
      exact ⟨g,g.property,(hpL g).trans (congrArg Subtype.val hg)⟩
  exact ⟨p,⟨hp,OrthogonalFourMinus.FivePoint.surjective_of_marked_alternating L p hp hmap hne⟩,
    fun g v => (hfρ g v).trans (hep g (f v)),hpL⟩
end Representation.BinaryOffender
