module

public import Theory.GroupTheory.Recognition.TransvectionFive.LocalData

/-!
# Relative normalizers under the transvection-centralizer marking

The marking transports the normalizer inside `C_G(z)` to the normalizer
inside the binary model centralizer. Thus `pointLocal` and `planeLocal`
model the intersections of the ambient normalizers with `C_G(z)`. They
do not model the full ambient normalizers in the Mathieu alternative.

The proof transports subgroup normalizers along the actual marking, then
maps them back through the centralizer inclusion. The resulting equivalences
retain that same marking on elements.

Source: Aschbacher, *Sporadic Groups* (1994), §39, pp.213–215, and
§§40.3–40.5, pp.217–219. The source writes these relative normalizers as
`N_H(Aᵢ)`, with `H = C_G(z)`.
-/

@[expose] public section
namespace Theory.GroupTheory.TransvectionFive.MarkedCentralizer

open Subgroup

variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z)

private theorem pullback_subgroupOf (A : Subgroup BinaryLinear.TransvectionFiveLocal.SL) :
    (F.pullback A).subgroupOf (centralizer ({z} : Set G)) =
      (A.subgroupOf BinaryLinear.TransvectionFiveLocal.centralizer).map
        F.equiv.symm.toMonoidHom := by
  change (((A.subgroupOf _).map F.equiv.symm.toMonoidHom).map
      (centralizer ({z} : Set G)).subtype).comap
      (centralizer ({z} : Set G)).subtype = _
  exact comap_map_eq_self_of_injective (centralizer ({z} : Set G)).subtype_injective _

/-- Pulling back the model's relative normalizer gives the literal intersection
with the ambient point centralizer. -/
theorem pullback_relativeNormalizer (A : Subgroup BinaryLinear.TransvectionFiveLocal.SL)
    (hA : A ≤ BinaryLinear.TransvectionFiveLocal.centralizer) :
    F.pullback (BinaryLinear.TransvectionFiveLocal.centralizer ⊓ normalizer (A : Set _)) =
      centralizer ({z} : Set G) ⊓ normalizer (F.pullback A : Set G) := by
  conv_lhs => unfold MarkedCentralizer.pullback
  rw [inf_subgroupOf_left, subgroupOf_normalizer_eq hA, map_equiv_normalizer_eq]
  rw [← pullback_subgroupOf F A, ← subgroupOf_normalizer_eq (F.pullback_le A),
    subgroupOf_map_subtype, inf_comm]

/-- Restrict the original marking to a subgroup of the model centralizer. -/
def pullbackEquiv (A : Subgroup BinaryLinear.TransvectionFiveLocal.SL)
    (hA : A ≤ BinaryLinear.TransvectionFiveLocal.centralizer) : F.pullback A ≃* A where
  toFun x := ⟨F.equiv ⟨x, F.pullback_le A x.property⟩,
    (F.mem_pullback_iff A ⟨x, F.pullback_le A x.property⟩).mp x.property⟩
  invFun a := ⟨F.equiv.symm ⟨a, hA a.property⟩,
    (F.mem_pullback_iff A (F.equiv.symm ⟨a, hA a.property⟩)).mpr (by simp)⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv a := by apply Subtype.ext; simp
  map_mul' x y := by
    apply Subtype.ext
    exact congrArg (fun a : BinaryLinear.TransvectionFiveLocal.centralizer =>
      (a : BinaryLinear.TransvectionFiveLocal.SL))
      (F.equiv.map_mul ⟨x, F.pullback_le A x.property⟩
        ⟨y, F.pullback_le A y.property⟩)

/-- The actual relative normalizer equivalence induced by the marking. -/
def relativeNormalizerEquiv
    (A : Subgroup BinaryLinear.TransvectionFiveLocal.SL)
    (hA : A ≤ BinaryLinear.TransvectionFiveLocal.centralizer) :
    ↥(centralizer ({z} : Set G) ⊓ normalizer (F.pullback A : Set G)) ≃*
      ↥(BinaryLinear.TransvectionFiveLocal.centralizer ⊓ normalizer (A : Set _)) :=
  (MulEquiv.subgroupCongr (F.pullback_relativeNormalizer A hA).symm).trans
    (F.pullbackEquiv _ inf_le_left)

/-- The relative normalizer equivalence uses the original marked element map. -/
theorem relativeNormalizerEquiv_apply
    (A : Subgroup BinaryLinear.TransvectionFiveLocal.SL)
    (hA : A ≤ BinaryLinear.TransvectionFiveLocal.centralizer)
    (x : ↥(centralizer ({z} : Set G) ⊓ normalizer (F.pullback A : Set G))) :
    (F.relativeNormalizerEquiv A hA x : BinaryLinear.TransvectionFiveLocal.SL) =
      (F.equiv ⟨x, x.property.1⟩ : BinaryLinear.TransvectionFiveLocal.SL) := rfl

/-- `pointLocal` identifies `N_H(A₁)`, with the literal pulled-back plane. -/
def plane_relativeNormalizerEquiv :
    ↥(centralizer ({z} : Set G) ⊓ normalizer (F.plane : Set G)) ≃*
      BinaryLinear.TransvectionFiveLocal.pointLocal :=
  F.relativeNormalizerEquiv Model.plane Model.plane_le_centralizer

/-- `planeLocal` identifies `N_H(A₂)`, with the literal pulled-back three-space. -/
def threeSpace_relativeNormalizerEquiv :
    ↥(centralizer ({z} : Set G) ⊓ normalizer (F.threeSpace : Set G)) ≃*
      BinaryLinear.TransvectionFiveLocal.planeLocal :=
  F.relativeNormalizerEquiv Model.threeSpace Model.threeSpace_le_centralizer

end Theory.GroupTheory.TransvectionFive.MarkedCentralizer
