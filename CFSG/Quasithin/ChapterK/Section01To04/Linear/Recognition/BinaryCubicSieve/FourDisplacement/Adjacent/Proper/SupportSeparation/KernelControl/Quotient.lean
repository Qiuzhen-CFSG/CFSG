module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.SupportSeparation.Presentation
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The relation quotient and its residual tensor kernel

The literal relation space is stable under the left regular action. Its
quotient therefore acts on the tensor orbit through a canonical intertwiner.
Rank-nullity shows that a quotient of dimension at most 21 mapping onto an
orbit of dimension at least 20 has kernel of dimension at most one. Every
binary action on such a kernel is trivial, giving the required displacement
containment back in the original regular module.

The two dimension bounds remain explicit here. In particular, no identification
of the universal quotient with the tensor orbit is asserted.

Source application: Aschbacher–Smith K.3.2, printed pp.451,454–455;
Guralnick–Malle, Classification of 2F-modules II, author manuscript,
Proposition 4.8(3), pp.27–28.
-/

@[expose] public section

open Representation
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.SupportSeparation.KernelControl
/-- The actual regular module modulo all translated highest-vector relations. -/
abbrev Universal := Free ⧸ relations
/-- The induced left regular action on the universal relation quotient. -/
noncomputable def universalRepresentation : Representation (ZMod 2) Group Universal :=
  regular.quotient relations relations_stable
/-- The literal tensor evaluation, descended through the relation space. -/
noncomputable def universalTensorMap : IntertwiningMap universalRepresentation mixedTensor where
  toLinearMap := relations.liftQ tensorOrbitMap.toLinearMap relations_le_tensorOrbitMap_ker
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    refine Submodule.Quotient.induction_on _ x ?_
    intro y
    change tensorOrbitMap (regular g y) = mixedTensor g (tensorOrbitMap y)
    exact LinearMap.congr_fun (tensorOrbitMap.isIntertwining' g) y

/-- Evaluation after quotienting is the original orbit evaluation. -/
theorem universalTensorMap_mk (x : Free) :
    universalTensorMap (relations.mkQ x) = tensorOrbitMap x := rfl

/-- The descended map has precisely the original tensor orbit as its image. -/
theorem universalTensorMap_range : universalTensorMap.toLinearMap.range =
    tensorOrbit.toSubmodule := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := relations.mkQ_surjective x
    exact ⟨y, rfl⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨relations.mkQ x, rfl⟩

private theorem binary_action_fixed_of_finrank_le_one
    {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) (hd : Module.finrank (ZMod 2) W ≤ 1)
    (g : H) (w : W) : ρ g w = w := by
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hd
  have hfix : ρ g v = v := by
    obtain ⟨c, hc⟩ := hv (ρ g v)
    have hc01 : c = 0 ∨ c = 1 :=
      (show ∀ a : ZMod 2, a = 0 ∨ a = 1 from by decide) c
    rcases hc01 with rfl | rfl
    · have hgv : ρ g v = 0 := by simpa using hc.symm
      have hv0 : v = 0 := (ρ.apply_bijective g).injective (hgv.trans (map_zero _).symm)
      simp [hv0]
    · simpa using hc.symm
  obtain ⟨c, rfl⟩ := hv w
  simp [hfix]

/-- A one-dimensional gap suffices: every kernel displacement is a relation. -/
theorem kernel_displacements_of_dimension_bounds
    (hupper : Module.finrank (ZMod 2) Universal ≤ 21)
    (hlower : 20 ≤ Module.finrank (ZMod 2) tensorOrbit.toSubmodule)
    (x : Free) (hx : tensorOrbitMap x = 0) (g : Group) :
    regular g x - x ∈ relations := by
  have hrank := universalTensorMap.toLinearMap.finrank_range_add_finrank_ker
  rw [universalTensorMap_range] at hrank
  have hk : Module.finrank (ZMod 2) universalTensorMap.ker.toSubmodule ≤ 1 := by
    change Module.finrank (ZMod 2) universalTensorMap.toLinearMap.ker ≤ 1
    omega
  let y : universalTensorMap.ker.toSubmodule := ⟨relations.mkQ x, hx⟩
  have hfix := binary_action_fixed_of_finrank_le_one
    universalTensorMap.ker.toRepresentation hk g y
  have he : relations.mkQ (regular g x) = relations.mkQ x :=
    congrArg Subtype.val hfix
  apply (Submodule.Quotient.mk_eq_zero relations).mp
  change relations.mkQ (regular g x - x) = 0
  rw [map_sub, he, sub_self]
end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.SupportSeparation.KernelControl
