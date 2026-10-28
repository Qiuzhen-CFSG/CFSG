module
public import Theory.Representation.SmallDisplacementParabolics.Models
/-!
# Changing the carrier of a recognized small-displacement action

A group isomorphism transports each concrete action model by composing
its actual actor identification. The same linear intertwiner is retained,
including the inverse-shift convention in the paired wreath action.

Source application: Aschbacher–Smith 15.2.27(2), printed p.1119.
-/

public section
namespace Representation.SmallDisplacementParabolics
variable {D E W : Type*} [Group D] [Group E] [AddCommGroup W] [Module (ZMod 2) W]

theorem ActionModel.comp_equiv {ρ : Representation (ZMod 2) D W}
    (h : ActionModel ρ) (e : E ≃* D) : ActionModel (ρ.comp e.toMonoidHom) := by
  rcases h with ⟨j,⟨f⟩⟩ | ⟨n,hn,d,j,⟨f⟩⟩ | ⟨j,f,hf⟩
  · exact Or.inl ⟨e.trans j,⟨Representation.Equiv.mk f.toLinearEquiv
      (fun x => f.isIntertwining' (e x))⟩⟩
  · exact Or.inr (Or.inl ⟨n,hn,d,e.trans j,⟨Representation.Equiv.mk f.toLinearEquiv
      (fun x => f.isIntertwining' (e x))⟩⟩)
  · exact Or.inr (Or.inr ⟨e.trans j,f,fun x w i => hf (e x) w i⟩)
end Representation.SmallDisplacementParabolics
