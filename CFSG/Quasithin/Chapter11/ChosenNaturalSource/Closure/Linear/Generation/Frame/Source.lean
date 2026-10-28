module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Frame.SourceAlignment
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Frame.Lattice
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Seed
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry.Normalization
/-!
# The original Cartan-normalizer frame

The aligned cycle and reversal give three independent lines under one common
change of basis. Their exact lifts act on the preimages by the original right
conjugation. The centralizer of L in V is trivial, so preservation of meets and
joins makes these three preimages a direct frame spanning V.

The frame supplies every missing point condition in the genuine G.2.5
hypothesis. The original field line, Sylow invariance, Cartan, and local
irreducibility remain the permitted preceding Chapter 11 inputs; their final
discharge belongs to the ancestors of `qt-d-1222-sl3-three-conjugates`.
Source: Aschbacher–Smith 11.5.7, printed pp.781–782; G.2.5, pp.335–336.
-/

open Subgroup Theory.GroupTheory Representation Matrix
open scoped IsMulCommutative MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open Matrix.SpecialLinearGroup.FrameGeometry
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Frame
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)
    (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))

private theorem preimage_conjugate (U : Submodule E.input.field.Carrier
    (Fin 3 → E.input.field.Carrier)) (l : L) :
    ChapterG.Section02.Setup.conjugate ((Coordinates.sl3 m).preimage U) (l : G) =
      (Coordinates.sl3 m).preimage
        (U.map (specialLinearNatural 3 ((Coordinates.sl3 m).quotientMap l⁻¹))) := by
  exact ((Coordinates.sl3 m).preimage_map_action l⁻¹ U).symm

/-- The original three conjugates form a direct frame inside N_L(X). -/
theorem exists_cartan_frame
    (P : Submodule E.input.field.Carrier (Fin 3 → E.input.field.Carrier))
    (hdim : Module.finrank E.input.field.Carrier P = 1)
    (hpoint : E.point = (Coordinates.sl3 m).binarySubspace P)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : IsCartan T L E.X) :
    ∃ x y : G, x ∈ L ⊓ normalizer (E.X : Set G) ∧
      y ∈ L ⊓ normalizer (E.X : Set G) ∧
      Disjoint E.V₁ (ChapterG.Section02.Setup.conjugate E.V₁ x) ∧
      Disjoint (E.V₁ ⊔ ChapterG.Section02.Setup.conjugate E.V₁ x)
        (ChapterG.Section02.Setup.conjugate E.V₁ y) ∧
      (E.V₁ ⊔ ChapterG.Section02.Setup.conjugate E.V₁ x) ⊔
        ChapterG.Section02.Setup.conjugate E.V₁ y = V := by
  obtain ⟨g,x,y,hxN,hyN,hx,hy,hP⟩ := exists_aligned_lifts E m P hdim hpoint hT hX
  let c := Coordinates.sl3 m
  let A : Fin 3 → Submodule E.input.field.Carrier (Fin 3 → E.input.field.Carrier) :=
    fun i => (coordinateLine i).map (specialLinearNatural 3 g)
  have hAx : P.map (specialLinearNatural 3 (c.quotientMap x⁻¹)) = A 1 := by
    rw [hx,hP]
    exact transported_line g cycleSL 1 cycle_maps_coordinateLine
  have hAy : P.map (specialLinearNatural 3 (c.quotientMap y⁻¹)) = A 2 := by
    rw [hy,hP]
    exact transported_line g _ 2 reversal_maps_coordinateLine
  have h01 : Disjoint (A 0) (A 1) :=
    Submodule.disjoint_map (SpecialLinearGroup.toLin' g).injective
      (coordinateLine_disjoint (by decide))
  have h012 : Disjoint (A 0 ⊔ A 1) (A 2) := by
    dsimp only [A]
    rw [← Submodule.map_sup]
    exact Submodule.disjoint_map (SpecialLinearGroup.toLin' g).injective
      coordinateLine_01_disjoint_2
  have hspan : (A 0 ⊔ A 1) ⊔ A 2 = ⊤ := by
    dsimp only [A]
    rw [← Submodule.map_sup, ← Submodule.map_sup, coordinateFrame_span]
    rw [Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (SpecialLinearGroup.toLin' g).surjective
  have hpre : E.V₁ = c.preimage P := congrArg D.centralQuotientPreimage hpoint
  have h0 : E.V₁ = c.preimage (A 0) := by rw [hpre,hP]
  have h1 : ChapterG.Section02.Setup.conjugate E.V₁ (x : G) = c.preimage (A 1) := by
    rw [hpre]
    exact (preimage_conjugate E m P x).trans (congrArg c.preimage hAx)
  have h2 : ChapterG.Section02.Setup.conjugate E.V₁ (y : G) = c.preimage (A 2) := by
    rw [hpre]
    exact (preimage_conjugate E m P y).trans (congrArg c.preimage hAy)
  have hbot : c.preimage ⊥ = ⊥ := by
    rw [c.preimage_bot]
    exact Preliminary.sl3_centralizer_eq_bot D E.input m
  refine ⟨x,y,⟨x.property,hxN⟩,⟨y.property,hyN⟩,?_,?_,?_⟩
  · rw [h1,h0,disjoint_iff]
    exact (c.preimage_inf (A 0) (A 1)).symm.trans
      ((congrArg c.preimage h01.eq_bot).trans hbot)
  · rw [h1,h2,h0,disjoint_iff]
    calc
      _ = c.preimage (A 0 ⊔ A 1) ⊓ c.preimage (A 2) :=
        congrArg (fun H : Subgroup G => H ⊓ c.preimage (A 2))
          (c.preimage_sup (A 0) (A 1)).symm
      _ = c.preimage ((A 0 ⊔ A 1) ⊓ A 2) := (c.preimage_inf _ _).symm
      _ = ⊥ := (congrArg c.preimage h012.eq_bot).trans hbot
  · rw [h1,h2,h0]
    calc
      _ = c.preimage (A 0 ⊔ A 1) ⊔ c.preimage (A 2) :=
        congrArg (fun H : Subgroup G => H ⊔ c.preimage (A 2))
          (c.preimage_sup (A 0) (A 1)).symm
      _ = c.preimage ((A 0 ⊔ A 1) ⊔ A 2) := (c.preimage_sup _ _).symm
      _ = V := (congrArg c.preimage hspan).trans c.preimage_top

/-- The constructed Cartan frame supplies the genuine G.2.5 hypothesis. -/
theorem exists_cartan_hypothesis
    (P : Submodule E.input.field.Carrier (Fin 3 → E.input.field.Carrier))
    (hdim : Module.finrank E.input.field.Carrier P = 1)
    (hpoint : E.point = (Coordinates.sl3 m).binarySubspace P)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : IsCartan T L E.X)
    (hirr : ∀ A : Subgroup G, E.V₁ ≤ A → A ≤ V →
      E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) → A = E.V₁ ∨ A = V)
    (hUT : E.W ≤ (T : Subgroup G)) (hn : ¬ IsMulCommutative E.W) :
    ∃ x y : G, x ∈ L ⊓ normalizer (E.X : Set G) ∧
      y ∈ L ⊓ normalizer (E.X : Set G) ∧
      Nonempty (ChapterG.Section02.LinearThree.Hypothesis
        (setup E) E.input.field.Carrier E.input.field.degree x y) := by
  obtain ⟨x,y,hx,hy,hdisj,hthird,hspan⟩ := exists_cartan_frame E m P hdim hpoint hT hX
  exact ⟨x,y,hx,hy,⟨hypothesis_of_frame E m P hdim hpoint hT hirr hUT hn
    x y hx.1 hy.1 hdisj hthird hspan⟩⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Frame
