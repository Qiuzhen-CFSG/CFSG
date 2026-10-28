module

public import Theory.Mathieu.M22.Properties.FixedHexadLocal.KernelCharacteristic
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.RepresentativeKernel

/-!
# Intrinsic local properties of a fixed hexad in M22

Every involution fixes an actual Witt hexad. The translation kernel of its
stabilizer is self-centralizing, so the stabilizer has characteristic two.
The kernel contains the involution and is abelian; hence it lies normally
in the involution centralizer. At the standard involution it consists exactly
of the elements commuting with all their conjugates in the centralizer, so
it is characteristic there. Involution fusion transports characteristicity
to every involution. Thus every abstract automorphism fixing the involution
preserves the kernel and its normalizer, which is the hexad stabilizer.

The representative characterization is certified in the actual degree-22
model; no surjectivity of the design-automorphism map is assumed. These are
intrinsic inputs for Aschbacher--Smith 2.3.9(7)(f), printed pp.525--526, using
the inner-involution case of 1.1.5(3)(f), printed p.502.
-/

public section
namespace Sporadic.Mathieu
open Subgroup
open scoped Pointwise

/-- The local characteristic-two condition for the fixed hexad of an involution. -/
theorem m22FixedPoints_stabilizer_core_selfCentralizing (u : M22) (hu : orderOf u = 2) :
    centralizer (pCore 2 (MulAction.stabilizer M22 (m22FixedPoints u)) :
      Set (MulAction.stabilizer M22 (m22FixedPoints u))) ≤
        pCore 2 (MulAction.stabilizer M22 (m22FixedPoints u)) :=
  m22Hexad_stabilizer_core_selfCentralizing (m22FixedPoints_mem_blocks u hu)

/-- The fixed-hexad kernel is characteristic in the involution centralizer. -/
theorem m22FixedPoints_kernel_characteristic (u : M22) (hu : orderOf u = 2) :
    ((m22HexadPointwiseKernel (m22FixedPoints u)).subgroupOf
      (centralizer ({u} : Set M22))).Characteristic :=
  m22FixedPoints_kernel_characteristic_of_representative
    m22GeneratorA_fixedPoints_kernel_characteristic u hu

private theorem centralizer_map_of_fix (u : M22) (a : MulAut M22) (ha : a u = u) :
    (centralizer ({u} : Set M22)).map a.toMonoidHom = centralizer ({u} : Set M22) := by
  ext x
  rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  rw [← a.injective.eq_iff]
  simp only [map_mul, MulEquiv.apply_symm_apply, ha]

/-- Characteristicity inside the involution centralizer suffices for invariance
under every abstract automorphism fixing the involution. -/
theorem m22FixedPoints_stabilizer_map_of_kernel_characteristic
    (u : M22) (hu : orderOf u = 2)
    (hchar : ((m22HexadPointwiseKernel (m22FixedPoints u)).subgroupOf
      (centralizer ({u} : Set M22))).Characteristic)
    (a : MulAut M22) (ha : a u = u) :
    (MulAction.stabilizer M22 (m22FixedPoints u)).map a.toMonoidHom =
      MulAction.stabilizer M22 (m22FixedPoints u) := by
  let C := centralizer ({u} : Set M22)
  let e : C ≃* C := (a.subgroupMap C).trans (MulEquiv.subgroupCongr
    (centralizer_map_of_fix u a ha))
  have hf : C.subtype.comp e.toMonoidHom = a.toMonoidHom.comp C.subtype := by
    ext x
    rfl
  have hmap := congrArg (fun K : Subgroup C => K.map C.subtype)
    (characteristic_iff_map_eq.mp hchar e)
  rw [map_map, hf, ← map_map,
    map_subgroupOf_eq_of_le (m22FixedPoints_kernel_le_centralizer u hu)] at hmap
  rw [← m22HexadPointwiseKernel_normalizer (m22FixedPoints_mem_blocks u hu),
    map_equiv_normalizer_eq, hmap]

/-- Characteristicity at the standard involution suffices: fusion supplies it
at the involution fixed by the automorphism. -/
theorem m22FixedPoints_stabilizer_map_of_representative_kernel_characteristic
    (hrep : ((m22HexadPointwiseKernel (m22FixedPoints m22GeneratorAInM22)).subgroupOf
      (centralizer ({m22GeneratorAInM22} : Set M22))).Characteristic)
    (u : M22) (hu : orderOf u = 2) (a : MulAut M22) (ha : a u = u) :
    (MulAction.stabilizer M22 (m22FixedPoints u)).map a.toMonoidHom =
      MulAction.stabilizer M22 (m22FixedPoints u) :=
  m22FixedPoints_stabilizer_map_of_kernel_characteristic u hu
    (m22FixedPoints_kernel_characteristic_of_representative hrep u hu) a ha

/-- An intrinsic description using the standard centralizer's derived two-core
suffices for all abstract automorphisms fixing an involution. This adapter
retains that alternative description as an explicit premise. -/
theorem m22FixedPoints_stabilizer_map_of_representative_core
    (hrep :
      let C := centralizer ({m22GeneratorAInM22} : Set M22)
      centralizer (↑(⁅pCore 2 C, pCore 2 C⁆ : Subgroup C) : Set C) =
        (m22HexadPointwiseKernel (m22FixedPoints m22GeneratorAInM22)).subgroupOf C)
    (u : M22) (hu : orderOf u = 2) (a : MulAut M22) (ha : a u = u) :
    (MulAction.stabilizer M22 (m22FixedPoints u)).map a.toMonoidHom =
      MulAction.stabilizer M22 (m22FixedPoints u) :=
  m22FixedPoints_stabilizer_map_of_kernel_characteristic u hu
    (m22FixedPoints_kernel_characteristic_of_representative_core hrep u hu) a ha

/-- Every abstract automorphism fixing an involution preserves its fixed-hexad
stabilizer. -/
theorem m22FixedPoints_stabilizer_map
    (u : M22) (hu : orderOf u = 2) (a : MulAut M22) (ha : a u = u) :
    (MulAction.stabilizer M22 (m22FixedPoints u)).map a.toMonoidHom =
      MulAction.stabilizer M22 (m22FixedPoints u) :=
  m22FixedPoints_stabilizer_map_of_kernel_characteristic u hu
    (m22FixedPoints_kernel_characteristic u hu) a ha

end Sporadic.Mathieu
