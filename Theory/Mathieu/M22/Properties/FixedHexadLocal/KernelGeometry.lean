module

public import Theory.Mathieu.M22.Properties.HexadExtension.Kernel
public import Theory.Mathieu.M22.Properties.FixedHexads
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.KernelNormalizer

/-!
# Intrinsic geometry of the M22 pointwise hexad kernel

The inclusion of M22 into the point-9 stabilizer of M23 identifies each
pointwise hexad kernel with the pointwise kernel of its augmented heptad.
The faithful binary action in M23 makes this kernel self-centralizing.
Its common fixed points are precisely the hexad, so its normalizer is the
setwise hexad stabilizer.

These are local ingredients for Aschbacher--Smith 2.3.9(7)(f), printed
pp.525--526, in the combined manuscript of 1 March 2004.
-/

@[expose] public section
namespace Sporadic.Mathieu
open Subgroup M23Geometry
open scoped Pointwise

/-- The pointwise hexad kernel, included in the original degree-22 group. -/
noncomputable def m22HexadPointwiseKernel (B : Finset (Fin 22)) : Subgroup M22 :=
  (m22SetAction B).ker.map (MulAction.stabilizer M22 B).subtype

@[simp] theorem mem_m22HexadPointwiseKernel (B : Finset (Fin 22)) (g : M22) :
    g ∈ m22HexadPointwiseKernel B ↔ ∀ a ∈ B, g • a = a := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (mem_m22SetAction_ker B u).mp hu
  · intro hg
    have hs : g ∈ MulAction.stabilizer M22 B := by
      apply MulAction.mem_stabilizer_finset'.mpr
      intro a ha
      rwa [hg a ha]
    exact ⟨⟨g, hs⟩, (mem_m22SetAction_ker B _).mpr hg, rfl⟩

/-- The pointwise kernel is contained in the setwise stabilizer. -/
theorem m22HexadPointwiseKernel_le (B : Finset (Fin 22)) :
    m22HexadPointwiseKernel B ≤ MulAction.stabilizer M22 B := map_subtype_le _

private noncomputable def inclusionM23 : M22 →* M23 :=
  (MulAction.stabilizer M23 (9 : Fin 23)).subtype.comp
    m23EquivM22PointStabilizer.toMonoidHom

private theorem inclusionM23_injective : Function.Injective inclusionM23 :=
  Subtype.val_injective.comp m23EquivM22PointStabilizer.injective

private theorem pointwiseKernel_map (B : Finset (Fin 22)) :
    (m22HexadPointwiseKernel B).map inclusionM23 =
      heptadPointwiseKernel (m22M23AugmentedBlock B) := by
  ext g
  constructor
  · rintro ⟨u, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨(m22AugmentedKernelEquiv B ⟨v, hv⟩).val,
      (m22AugmentedKernelEquiv B ⟨v, hv⟩).property,
      m22AugmentedKernelEquiv_coe B ⟨v, hv⟩⟩
  · rintro ⟨v, hv, rfl⟩
    let u := (m22AugmentedKernelEquiv B).symm ⟨v, hv⟩
    refine ⟨u.val.val, ⟨u.val, u.property, rfl⟩, ?_⟩
    exact (m22AugmentedKernelEquiv_coe B u).symm.trans
      (congrArg (fun x : (setAction (m22M23AugmentedBlock B)).ker => x.val.val)
        ((m22AugmentedKernelEquiv B).apply_symm_apply ⟨v, hv⟩))

private theorem map_selfCentralizing {G H : Type*} [Group G] [Group H]
    (Q : Subgroup G) (e : G ≃* H) (hc : centralizer (Q : Set G) ≤ Q) :
    centralizer (Q.map e.toMonoidHom : Set H) ≤ Q.map e.toMonoidHom := by
  intro x hx
  refine ⟨e.symm x, hc ?_, e.apply_symm_apply x⟩
  intro y hy
  apply e.injective
  simpa only [map_mul, MulEquiv.apply_symm_apply] using
    hx (e y) (mem_map_of_mem _ hy)

private theorem heptadKernelAmbient_selfCentralizing :
    centralizer (heptadKernelAmbient : Set M23) ≤ heptadKernelAmbient := by
  intro x hx
  have hs : x ∈ heptadStabilizer := by
    rw [← heptadKernelAmbient_normalizer]
    exact centralizer_le_normalizer _ hx
  refine ⟨⟨x, hs⟩, heptadKernel_selfCentralizing ?_, rfl⟩
  intro y hy
  exact Subtype.ext (hx y.val ⟨y, hy, rfl⟩)

private theorem heptadPointwiseKernel_selfCentralizing {B : Finset (Fin 23)}
    (hB : B ∈ m23Blocks) :
    centralizer (heptadPointwiseKernel B : Set M23) ≤ heptadPointwiseKernel B := by
  obtain ⟨g, rfl⟩ := exists_smul_omega_eq hB
  rw [heptadPointwiseKernel_smul, heptadPointwiseKernel_omega]
  exact map_selfCentralizing _ (MulAut.conj g) heptadKernelAmbient_selfCentralizing

/-- The genuine translation kernel is self-centralizing in the full M22. -/
theorem m22HexadPointwiseKernel_selfCentralizing {B : Finset (Fin 22)}
    (hB : B ∈ m22Blocks) :
    centralizer (m22HexadPointwiseKernel B : Set M22) ≤ m22HexadPointwiseKernel B := by
  intro x hx
  have hc : inclusionM23 x ∈
      centralizer (heptadPointwiseKernel (m22M23AugmentedBlock B) : Set M23) := by
    rw [← pointwiseKernel_map]
    rintro y ⟨z, hz, rfl⟩
    exact (map_mul inclusionM23 z x).symm.trans
      ((congrArg inclusionM23 (hx z hz)).trans (map_mul inclusionM23 x z))
  have hk := heptadPointwiseKernel_selfCentralizing (m22Hexad_augmented_mem hB) hc
  rw [← pointwiseKernel_map] at hk
  obtain ⟨y, hy, he⟩ := hk
  exact inclusionM23_injective he ▸ hy

private theorem mem_heptad_iff_kernel_fixed {B : Finset (Fin 23)}
    (hB : B ∈ m23Blocks) (a : Fin 23) :
    a ∈ B ↔ ∀ u ∈ heptadPointwiseKernel B, u • a = a := by
  obtain ⟨g, rfl⟩ := exists_smul_omega_eq hB
  constructor
  · intro ha u hu
    exact (mem_heptadPointwiseKernel _ u).mp hu a ha
  · intro h
    have ha : g⁻¹ • a ∈ omega := by
      apply (mem_omega_iff_heptadKernel_fixed _).mpr
      intro u
      have hu : MulAut.conj g (u.val.val) ∈ heptadPointwiseKernel (g • omega) := by
        rw [heptadPointwiseKernel_smul, heptadPointwiseKernel_omega]
        exact mem_map_of_mem _ ⟨u.val, u.property, rfl⟩
      have he := congrArg (fun x : Fin 23 => g⁻¹ • x) (h _ hu)
      simpa only [MulAut.conj_apply, mul_smul, inv_smul_smul] using he
    exact Finset.mem_smul_finset.mpr ⟨g⁻¹ • a, ha, smul_inv_smul g a⟩

/-- The common fixed points of the kernel are exactly the original hexad. -/
theorem mem_hexad_iff_m22HexadPointwiseKernel_fixed {B : Finset (Fin 22)}
    (hB : B ∈ m22Blocks) (a : Fin 22) :
    a ∈ B ↔ ∀ u ∈ m22HexadPointwiseKernel B, u • a = a := by
  constructor
  · intro ha u hu
    exact (mem_m22HexadPointwiseKernel B u).mp hu a ha
  · intro ha
    have hfix : m22M23PointMap a ∈ m22M23AugmentedBlock B := by
      apply (mem_heptad_iff_kernel_fixed (m22Hexad_augmented_mem hB) _).mpr
      intro u hu
      rw [← pointwiseKernel_map] at hu
      obtain ⟨v, hv, rfl⟩ := hu
      change (m23EquivM22PointStabilizer v : M23) • m22M23PointMap a = _
      rw [m22PointStabilizerEquiv_apply, ha v hv]
    simpa [m22M23AugmentedBlock, m22M23LiftBlock, m22M23PointEmbedding,
      m22M23PointMap_ne_nine a] using hfix

/-- The setwise stabilizer is the normalizer of the actual pointwise kernel. -/
theorem m22HexadPointwiseKernel_normalizer {B : Finset (Fin 22)}
    (hB : B ∈ m22Blocks) :
    normalizer (m22HexadPointwiseKernel B : Set M22) = MulAction.stabilizer M22 B := by
  apply le_antisymm
  · intro g hg
    apply MulAction.mem_stabilizer_finset'.mpr
    intro a ha
    apply (mem_hexad_iff_m22HexadPointwiseKernel_fixed hB _).mpr
    intro u hu
    have hv := (mem_normalizer_iff.mp
      ((normalizer (m22HexadPointwiseKernel B : Set M22)).inv_mem hg) u).mp hu
    have hf := (mem_m22HexadPointwiseKernel B _).mp hv a ha
    have he := congrArg (fun b : Fin 22 => g • b) hf
    simpa only [inv_inv, mul_smul, smul_inv_smul] using he
  · have hn : ((m22HexadPointwiseKernel B).subgroupOf
        (MulAction.stabilizer M22 B)).Normal := by
      have he : (m22HexadPointwiseKernel B).subgroupOf (MulAction.stabilizer M22 B) =
          (m22SetAction B).ker := by
        ext x
        constructor
        · rintro ⟨y, hy, he⟩
          exact (Subtype.ext he : y = x) ▸ hy
        · intro hx
          exact ⟨x, hx, rfl⟩
      rw [he]
      infer_instance
    exact (normal_subgroupOf_iff_le_normalizer (m22HexadPointwiseKernel_le B)).mp hn

/-- The ambient pointwise kernel is a two-group. -/
theorem m22HexadPointwiseKernel_isTwoGroup {B : Finset (Fin 22)}
    (hB : B ∈ m22Blocks) : IsPGroup 2 (m22HexadPointwiseKernel B) :=
  (IsPGroup.of_card (n := 4) (by simpa using m22HexadKernel_card hB)).map _

/-- The ambient kernel retains its elementary abelian structure. -/
theorem m22HexadPointwiseKernel_elementaryAbelian {B : Finset (Fin 22)}
    (hB : B ∈ m22Blocks) : IsElementaryAbelian 2 (m22HexadPointwiseKernel B) := by
  let := m22HexadKernel_elementaryAbelian hB
  exact IsElementaryAbelian.map_subtype

/-- The ambient pointwise kernel has order sixteen. -/
theorem m22HexadPointwiseKernel_card {B : Finset (Fin 22)}
    (hB : B ∈ m22Blocks) : Nat.card (m22HexadPointwiseKernel B) = 16 :=
  (card_subtype _ _).trans (m22HexadKernel_card hB)

/-- Every actual hexad stabilizer has self-centralizing intrinsic two-core. -/
theorem m22Hexad_stabilizer_core_selfCentralizing {B : Finset (Fin 22)}
    (hB : B ∈ m22Blocks) :
    centralizer (pCore 2 (MulAction.stabilizer M22 B) :
      Set (MulAction.stabilizer M22 B)) ≤ pCore 2 (MulAction.stabilizer M22 B) :=
  centralizer_pCore_le_of_normalized 2 _ _ (m22HexadPointwiseKernel_isTwoGroup hB)
    (m22HexadPointwiseKernel_le B) (m22HexadPointwiseKernel_normalizer hB ▸ le_rfl)
    (m22HexadPointwiseKernel_selfCentralizing hB)

/-- An involution belongs to the pointwise kernel of its own fixed hexad. -/
theorem m22_mem_fixedPoints_kernel (u : M22) :
    u ∈ m22HexadPointwiseKernel (m22FixedPoints u) := by
  apply (mem_m22HexadPointwiseKernel _ _).mpr
  intro a ha
  exact (mem_m22FixedPoints u a).mp ha

/-- The abelian pointwise kernel centralizes the involution it contains. -/
theorem m22FixedPoints_kernel_le_centralizer (u : M22) (hu : orderOf u = 2) :
    m22HexadPointwiseKernel (m22FixedPoints u) ≤ centralizer ({u} : Set M22) := by
  let := m22HexadPointwiseKernel_elementaryAbelian (m22FixedPoints_mem_blocks u hu)
  intro g hg
  exact mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mul_comm'
      (⟨g, hg⟩ : m22HexadPointwiseKernel (m22FixedPoints u))
      ⟨u, m22_mem_fixedPoints_kernel u⟩))

/-- Normality of the kernel is relative to the involution centralizer. -/
theorem m22FixedPoints_kernel_normal (u : M22) (hu : orderOf u = 2) :
    ((m22HexadPointwiseKernel (m22FixedPoints u)).subgroupOf
      (centralizer ({u} : Set M22))).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer
    (m22FixedPoints_kernel_le_centralizer u hu)).mpr
  rw [m22HexadPointwiseKernel_normalizer (m22FixedPoints_mem_blocks u hu)]
  exact m22_centralizer_le_fixedPoints_stabilizer u

end Sporadic.Mathieu
