module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.OddResidual
public import Theory.Representation.SmallBinaryFiveResidual

/-!
# Residuals on the original quintic dihedral support

The original dihedral factor embeds normally in its faithful support image.
Its two-residual gives a normal five in that image. The binary four-space
centralizer bound makes the support residual cyclic of order dividing
fifteen, retaining the original restriction map and dihedral prime.

Source: Aschbacher--Smith 15.1.7(6) and 15.1.16(a), pp.1087--1088,1092.
The marked-centralizer application is in Chapter15 ExchangedSelection.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD.RatioDecomposition.Factor
universe u
variable {D V : Type u} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} (F : Factor ρ)

/-- The literal support residual is cyclic with order dividing fifteen. -/
theorem support_residual_of_five
    (hN : subspaceStabilizer ρ F.space ≤ normalizer (F.actor : Set D))
    (l : CyclicSource.LocalGeneration F.action) (hm : CyclicSource.DihedralMarking l 5 2) :
    Nat.card (pResidual 2 (subspaceActionImage ρ F.space)) ∣ 15 ∧
      IsCyclic (pResidual 2 (subspaceActionImage ρ F.space)) := by
  obtain ⟨k,J,hk,_,_,hn,_⟩ := F.faithful_normal_support_image_data hN
  let H := k.range
  let : H.Normal := hn
  let : FiniteDimensional (ZMod 2) F.space := Module.Finite.of_surjective J.toLinearMap J.surjective
  let e : F.Carrier ≃* H := MonoidHom.ofInjective hk
  let P := (pResidual 2 H).map H.subtype
  have hP : Nat.card P = 5 := by
    rw [card_map_of_injective H.subtype_injective,
      ←map_pResidual_of_surjective 2 e.toMonoidHom e.surjective,
      card_map_of_injective (f := e.toMonoidHom) e.injective,←l.kernel_eq_twoResidual]
    exact hm.card_kernel
  exact ⟨Representation.SmallBinaryFiveResidual.card_twoResidual_dvd_fifteen
    (subspaceImageRepresentation ρ F.space) (subspaceImageRepresentation_injective ρ F.space)
    (J.finrank_eq.symm.trans hm.dimension) P hP,
    Representation.SmallBinaryCyclicResidual.cyclic_twoResidual_of_normal_five
    (subspaceImageRepresentation ρ F.space) (subspaceImageRepresentation_injective ρ F.space)
    (J.finrank_eq.symm.trans hm.dimension) P hP⟩

end CFSG.Quasithin.ChapterD.RatioDecomposition.Factor
