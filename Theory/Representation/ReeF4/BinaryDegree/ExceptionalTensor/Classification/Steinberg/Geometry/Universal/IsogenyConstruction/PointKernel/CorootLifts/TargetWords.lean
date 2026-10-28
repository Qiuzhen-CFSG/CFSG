module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.Coroots
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Basic
public import Theory.AlgebraicGroup.RootSubgroups.BinaryCorootWord
public import Theory.AlgebraicGroup.RootSubgroups.RootCocharacterChoice
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.RankOne

/-!
# Comparing rank-one words with the actual F4 coroots

The supplied coroot-product isomorphism makes character pullback injective.
Combined with the integral F4 root-lattice calculation, it shows that the
actual root characters generate all torus characters and hence separate
points. A Cartan-normalized rank-one cocharacter therefore equals the
cocharacter stored by the model.

Applying this uniqueness result to a rank-one chart identifies its root word
with the actual model coroot. The geometric chart and its Cartan normalization
are explicit inputs here; their construction is needed for the unconditional
four-coroot result. No choice of the model's positive base enters the comparison.

Sources: GLS3, Theorem 1.9.5(d), Remarks 1.9.6, the defining formulas of
Theorem 1.12.1 and Theorem 1.12.5(b), `refs/KGroup/GLS3/Chapter1.tex`.
-/

public section
open Theory.AlgebraicGroup.StandardRootSystem
universe u

namespace Theory.AlgebraicGroup.RootSystemModel
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
variable (M : RootSystemModel typeF4RootPairingULift G)
local instance : AlgebraicGroup M.torus.carrierVariety := M.torus.carrierAlgebraicGroup

/-- A supplied coroot-product isomorphism makes coroot evaluation injective
on the full character lattice. -/
theorem f4CorootCoordinates_injective_of_product_iso (e : Iso (dVariety k 4) M.torus.carrierVariety)
    (he : e.hom = M.f4CorootProduct) : Function.Injective M.f4CorootCoordinates := by
  intro x y hxy
  have hp : TorusCharacter.pullback M.f4CorootProduct x.toMul =
      TorusCharacter.pullback M.f4CorootProduct y.toMul := by
    rw [M.f4CorootProduct_pullback, M.f4CorootProduct_pullback]
    exact congrArg (dLaurentCharacter 4) hxy
  have hc : x.toMul = y.toMul := by
    apply Morphism.ext
    funext t
    have h := congrArg (fun χ : TorusCharacter (dVariety k 4) =>
      χ.onPoints (e.inv.onPoints t)) hp
    change x.toMul.onPoints (M.f4CorootProduct.onPoints (e.inv.onPoints t)) =
      y.toMul.onPoints (M.f4CorootProduct.onPoints (e.inv.onPoints t)) at h
    rw [← he, e.inv_hom_id] at h
    exact h
  exact congrArg Additive.ofMul hc

/-- Actual root characters separate torus points once the coroot product
is an isomorphism; the F4 root lattice then equals the character lattice. -/
theorem f4_torusPoint_ext_of_product_iso (e : Iso (dVariety k 4) M.torus.carrierVariety)
    (he : e.hom = M.f4CorootProduct)
    {x y : Variety.Point M.torus.carrierVariety}
    (h : ∀ a, (M.rootData.rootWeight a).pointCharacter x =
      (M.rootData.rootWeight a).pointCharacter y) : x = y := by
  apply (torusPointEval_bijective M.maximalTorus.1).1
  apply MonoidHom.eq_of_eqOn_dense
    (M.f4_rootLattice_eq_top_of_corootCoordinates_injective (f4CorootCoordinates_injective_of_product_iso M e he))
  intro χ hχ
  rw [← M.realization.2.1] at hχ
  obtain ⟨a, rfl⟩ := hχ
  exact Units.ext (h a)

/-- Cartan normalization determines the stored F4 cocharacter using actual
character separation, including every possible central-torus coordinate. -/
theorem f4_rootCocharacter_unique_of_product_iso (e : Iso (dVariety k 4) M.torus.carrierVariety)
    (he : e.hom = M.f4CorootProduct) (a : M.rootData.Root)
    (h : ClosedSubgroupTorusCocharacter M.torus)
    (hh : M.rootData.IsCartanRootCocharacter a h) :
    h = M.rootData.rootCocharacter a := by
  apply Morphism.ext
  funext t
  apply f4_torusPoint_ext_of_product_iso M e he
  intro b
  exact (hh b t).trans (M.realization.rootWeight_rootCocharacter b a t).symm
end Theory.AlgebraicGroup.RootSystemModel
namespace Theory.AlgebraicGroup.RootSystemModel
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {G : Variety k} [AlgebraicGroup G]
variable (M : RootSystemModel typeF4RootPairingULift G)
local instance : AlgebraicGroup M.torus.carrierVariety := M.torus.carrierAlgebraicGroup

/-- A geometrically constructed and Cartan-normalized chart realizes the
stored coroot as the source word in the actual model root subgroups.
The chart and its normalization remain explicit premises. -/
theorem f4_binaryCorootWord_eq_of_chart
    (e : Iso (dVariety k 4) M.torus.carrierVariety)
    (he : e.hom = M.f4CorootProduct) (a : M.rootData.Root)
    (C : BinaryOppositeRootSL2Chart M.torus (M.rootData.rootSubgroup a)
      (M.rootData.rootSubgroup (M.rootData.neg a)))
    (hC : M.rootData.IsCartanRootCocharacter a C.cocharacter)
    (t : Variety.Point (KMult k)) :
    (binaryCorootWord ((M.rootData.rootSubgroup a).inclusion.comp C.plus.hom).toVariety
      ((M.rootData.rootSubgroup (M.rootData.neg a)).inclusion.comp C.minus.hom).toVariety).toFun t =
        M.torus.inclusion.onPoints ((M.rootData.rootCocharacter a).onPoints t) := by
  rw [C.word_eq_cocharacter, f4_rootCocharacter_unique_of_product_iso M e he a C.cocharacter hC]
end Theory.AlgebraicGroup.RootSystemModel
