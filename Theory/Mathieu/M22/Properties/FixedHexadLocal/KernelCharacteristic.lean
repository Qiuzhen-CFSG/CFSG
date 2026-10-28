module
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.Fusion

/-!
# Reducing fixed-hexad characteristicity to one involution

Involution fusion and the actual fixed-point action transport the hexad kernel
and the involution centralizer together. Characteristicity of the relative
kernel at the standard involution therefore implies characteristicity for every
involution. In particular, identifying that kernel with the centralizer of the
derived subgroup of the centralizer's two-core would suffice.

The representative calculation is an explicit premise, still to be proved;
these transport results do not assert that calculation or the unconditional
automorphism-invariance theorem. They support the intrinsic M22 local argument
in Aschbacher--Smith, 2.3.9(7)(f), printed pp.525--526.
-/

public section
namespace Sporadic.Mathieu
open Subgroup
open scoped Pointwise

private theorem characteristic_map_equiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (K : Subgroup G) (hK : K.Characteristic) :
    (K.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  obtain ⟨y, hy, rfl⟩ := hx
  let b : MulAut G := e.trans (a.trans e.symm)
  refine ⟨b y, (characteristic_iff_le_comap.mp hK b) hy, ?_⟩
  exact e.apply_symm_apply _

private theorem centralizer_map (a : MulAut M22) (u : M22) :
    (centralizer ({u} : Set M22)).map a.toMonoidHom = centralizer ({a u} : Set M22) := by
  ext x
  rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  rw [← a.injective.eq_iff]
  simp only [map_mul, MulEquiv.apply_symm_apply]

/-- A characteristic-kernel calculation at the standard involution transports
to every involution in the concrete M22. -/
theorem m22FixedPoints_kernel_characteristic_of_representative
    (hrep : ((m22HexadPointwiseKernel (m22FixedPoints m22GeneratorAInM22)).subgroupOf
      (centralizer ({m22GeneratorAInM22} : Set M22))).Characteristic)
    (u : M22) (hu : orderOf u = 2) :
    ((m22HexadPointwiseKernel (m22FixedPoints u)).subgroupOf
      (centralizer ({u} : Set M22))).Characteristic := by
  have h0 : orderOf m22GeneratorAInM22 = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact m22GeneratorA_order
  obtain ⟨g, hg⟩ := isConj_iff.mp (m22_involutions_isConj m22GeneratorAInM22 u h0 hu)
  let a := MulAut.conj g
  have ha : a m22GeneratorAInM22 = u := hg
  let C0 := centralizer ({m22GeneratorAInM22} : Set M22)
  let C := centralizer ({u} : Set M22)
  let K0 := m22HexadPointwiseKernel (m22FixedPoints m22GeneratorAInM22)
  let K := m22HexadPointwiseKernel (m22FixedPoints u)
  have hC : C0.map a.toMonoidHom = C := by rw [centralizer_map, ha]
  have hK : K0.map a.toMonoidHom = K := by
    change (m22HexadPointwiseKernel (m22FixedPoints m22GeneratorAInM22)).map
      (MulAut.conj g).toMonoidHom = _
    rw [← m22HexadPointwiseKernel_smul, ← m22FixedPoints_conj, ha]
  let e : C0 ≃* C := (a.subgroupMap C0).trans (MulEquiv.subgroupCongr hC)
  have hf : C.subtype.comp e.toMonoidHom = a.toMonoidHom.comp C0.subtype := by
    ext x
    rfl
  have hm : (K0.subgroupOf C0).map e.toMonoidHom = K.subgroupOf C := by
    apply Subgroup.map_injective C.subtype_injective
    rw [map_map, hf, ← map_map,
      map_subgroupOf_eq_of_le (m22FixedPoints_kernel_le_centralizer _ h0),
      map_subgroupOf_eq_of_le (m22FixedPoints_kernel_le_centralizer u hu), hK]
  rw [← hm]
  exact characteristic_map_equiv e _ hrep

/-- The proposed intrinsic identity inside the standard centralizer implies
the needed characteristicity for every fixed-hexad kernel. The identity is
an explicit model-calculation premise here. -/
theorem m22FixedPoints_kernel_characteristic_of_representative_core
    (hrep :
      let C := centralizer ({m22GeneratorAInM22} : Set M22)
      centralizer (↑(⁅pCore 2 C, pCore 2 C⁆ : Subgroup C) : Set C) =
        (m22HexadPointwiseKernel (m22FixedPoints m22GeneratorAInM22)).subgroupOf C)
    (u : M22) (hu : orderOf u = 2) :
    ((m22HexadPointwiseKernel (m22FixedPoints u)).subgroupOf
      (centralizer ({u} : Set M22))).Characteristic := by
  apply m22FixedPoints_kernel_characteristic_of_representative _ u hu
  rw [← hrep]
  infer_instance

end Sporadic.Mathieu
