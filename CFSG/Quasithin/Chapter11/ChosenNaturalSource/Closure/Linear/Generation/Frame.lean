module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Frame.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Layers.Source

/-!
# The original SL₃ Cartan frame and its layer-generation application

The original field line is identified by inner Sylow uniqueness. Simultaneous
Sylow and Hall conjugacy aligns the actual Cartan image with the full diagonal
torus of SL₃. Exact normalizer lifts of the cycle and reversal produce three
direct conjugates of the original point. These supply the genuine G.2.5
hypothesis and discharge the frame input of all three original layer identities.

The field line, Sylow invariance, Cartan and local irreducibility are preceding
Chapter 11 geometry, retained with their original final assembly owner. The
Frattini bound in the layer application is the preceding 11.5.5 conclusion.
Source: Aschbacher–Smith, 11.5.7, printed pp.781–782; G.2.5, pp.335–336.
-/

open Subgroup Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Frame
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)
    (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))

/-- The literal layer-generation consumer with its Cartan frame constructed. -/
theorem source_frame_layer_generation
    (P : Submodule E.input.field.Carrier (Fin 3 → E.input.field.Carrier))
    (hdim : Module.finrank E.input.field.Carrier P = 1)
    (hpoint : E.point = (LocalGeometry.Coordinates.sl3 m).binarySubspace P)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : LocalGeometry.IsCartan T L E.X)
    (hXG : E.X ≤ E.G₁)
    (hirr : ∀ A : Subgroup G, E.V₁ ≤ A → A ≤ V →
      E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) → A = E.V₁ ∨ A = V)
    (hUT : E.W ≤ (T : Subgroup G)) (hn : ¬ IsMulCommutative E.W)
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁) :
    ∃ x y : G, x ∈ L ⊓ normalizer (E.X : Set G) ∧
      y ∈ L ⊓ normalizer (E.X : Set G) ∧
      Nonempty (ChapterG.Section02.LinearThree.Hypothesis
        (setup E) E.input.field.Carrier E.input.field.degree x y) ∧
      (threeCore E x y = ⁅threeCore E x y, E.L₁⁆ ⊔ oppositePair E x y) ∧
      (threeCore E x y ≤ ⁅threeCore E x y, E.X⁆ ⊔ (threeCore E x y ⊓ E.W)) ∧
      oppositePair E x y ≤ ⁅oppositePair E x y, E.X⁆ ⊔ triple E x y := by
  obtain ⟨x,y,hx,hy,⟨d⟩⟩ := exists_cartan_hypothesis E m P hdim hpoint hT hX hirr hUT hn
  exact ⟨x,y,hx,hy,⟨d⟩,sourceLayerGeneration E d hUT hf hX hXG hx.2 hy.2⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Frame
