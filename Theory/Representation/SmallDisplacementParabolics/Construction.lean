module
public import Theory.Representation.SmallDisplacementParabolics.OrthogonalEight
public import Theory.Representation.SmallDisplacementParabolics.PairedNatural
public import Theory.Representation.SmallDisplacementParabolics.NaturalDualExclusion

/-!
# Moving parabolics for the recognized small-displacement actions

The marked vector stabilizer excludes the natural-plus-dual models in degrees
four and five. The eight-point and paired-natural calculations construct
minimal moving parabolics in the remaining two models. Every transport uses
the actual group isomorphism and module equivalence in `ActionModel`.
The subgroup X is identified only after quotienting by its own two-core.

Source: Aschbacher--Smith, original 15.2.27(2), printed p.1119 (PDF p.1136).
-/

public section
open Subgroup
namespace Representation.SmallDisplacementParabolics
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]

/-- The full model calculation, with no assumed moving subgroup or movement. -/
theorem exists_of_actionModel (ρ : Representation (ZMod 2) D W) (hmodel : ActionModel ρ)
    (S : Sylow 2 D) (X : Subgroup D) (hSX : (S : Subgroup D) ≤ X)
    (hX : Nonempty ((X ⧸ pCore 2 X) ≃* RegularWreathProduct (Equiv.Perm (Fin 3)) PairIndex))
    (w : W) (hw : w ≠ 0) (hfix : ∀ g ∈ X, ρ g w = w) :
    Nonempty (MovingParabolic ρ S w) := by
  have hS : ∀ g ∈ (S : Subgroup D), ρ g w = w := fun g hg => hfix g (hSX hg)
  rcases hmodel with ⟨e,⟨f⟩⟩ | ⟨n,hn,d,e,⟨f⟩⟩ | ⟨e,E,hE⟩
  · exact OrthogonalEight.exists_of_equiv ρ e f S w hw hS
  · exact (NaturalDualExclusion.false_of_equiv ρ hn d e f S X hSX hX w hw hfix).elim
  · exact PairedNatural.exists_of_equiv ρ e E hE S w hw hS

end Representation.SmallDisplacementParabolics
