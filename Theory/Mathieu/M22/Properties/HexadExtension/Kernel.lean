module

public import Theory.Mathieu.M23.Properties.Simplicity
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.BinaryKernel
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.Order
public import Theory.ElementaryAbelian.Basic

/-!
# The actual pointwise hexad kernel in M22

The degree-22 action is the restriction of the degree-23 action to the
complement of point 9. Augmenting a hexad by that point identifies its
pointwise fixer with the pointwise fixer of a heptad in M23. Conjugacy of
heptads then identifies this group with the certified binary translations.

Source: Aschbacher--Smith, Lemma 2.3.9(7)(f), printed p.525. The model
comparison is the concrete relabelling in M23.Properties.Simplicity; the
binary kernel is constructed in M23.QuasithinGeometry.HeptadStructure.
-/

public section
namespace Sporadic.Mathieu
open scoped Pointwise
open M23Geometry

/-- Restriction of the actual M22 permutations to a set fixed setwise. -/
@[expose] noncomputable def m22SetAction (B : Finset (Fin 22)) :
    MulAction.stabilizer M22 B →* Equiv.Perm B where
  toFun g := g.val.val.subtypePerm (MulAction.mem_stabilizer_finset.mp g.property)
  map_one' := by ext a; rfl
  map_mul' g h := by ext a; rfl

@[simp] theorem m22SetAction_apply (B : Finset (Fin 22))
    (g : MulAction.stabilizer M22 B) (a : B) :
    (m22SetAction B g a).val = (g : M22) • a.val := rfl

/-- The restriction kernel is exactly the pointwise fixer. -/
theorem mem_m22SetAction_ker (B : Finset (Fin 22)) (g : MulAction.stabilizer M22 B) :
    g ∈ (m22SetAction B).ker ↔ ∀ a ∈ B, (g : M22) • a = a := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h a ha
    exact congrArg Subtype.val (Equiv.congr_fun h ⟨a, ha⟩)
  · intro h
    exact Equiv.ext (fun a => Subtype.ext (h a.val a.property))

/-- Compatibility of the M22--M23 equivalence with the original point labels. -/
@[simp] theorem m22PointStabilizerEquiv_apply (g : M22) (a : Fin 22) :
    (m23EquivM22PointStabilizer g : M23) • m22M23PointMap a =
      m22M23PointMap (g • a) := by
  change (Equiv.Perm.viaEmbeddingHom m22M23PointEmbedding g.val)
    (m22M23PointEmbedding a) = m22M23PointEmbedding (g.val a)
  exact Equiv.Perm.viaEmbedding_apply _ _ _

/-- Every hexad augments to an actual heptad through point 9. -/
theorem m22Hexad_augmented_mem {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    m22M23AugmentedBlock B ∈ m23Blocks := by
  have h : m22M23AugmentedBlock B ∈ m22Blocks.image m22M23AugmentedBlock :=
    Finset.mem_image.mpr ⟨B, hB, rfl⟩
  rw [← m23Blocks_through_nine] at h
  exact (Finset.mem_filter.mp h).1

private theorem fixes_augmented_iff (B : Finset (Fin 22)) (g : M22) :
    (∀ a ∈ m22M23AugmentedBlock B, (m23EquivM22PointStabilizer g : M23) • a = a) ↔
      ∀ a ∈ B, g • a = a := by
  constructor
  · intro h a ha
    apply m22M23PointMap_injective
    rw [← m22PointStabilizerEquiv_apply]
    exact h _ (Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨a, ha, rfl⟩))
  · intro h a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact (m23EquivM22PointStabilizer g).property
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp ha
      change (m23EquivM22PointStabilizer g : M23) • m22M23PointMap b = _
      rw [m22PointStabilizerEquiv_apply, h b hb]
      rfl

private noncomputable def kernelForward (B : Finset (Fin 22))
    (u : (m22SetAction B).ker) : (setAction (m22M23AugmentedBlock B)).ker := by
  let g := m23EquivM22PointStabilizer (u.val : M22)
  have hf : ∀ a ∈ m22M23AugmentedBlock B, (g : M23) • a = a :=
    (fixes_augmented_iff B _).mpr ((mem_m22SetAction_ker B u.val).mp u.property)
  have hs : (g : M23) ∈ MulAction.stabilizer M23 (m22M23AugmentedBlock B) := by
    apply MulAction.mem_stabilizer_finset'.mpr
    intro a ha
    rwa [hf a ha]
  exact ⟨⟨g, hs⟩, (mem_setAction_ker _ _).mpr hf⟩

private noncomputable def kernelBackward (B : Finset (Fin 22))
    (u : (setAction (m22M23AugmentedBlock B)).ker) : (m22SetAction B).ker := by
  have hf := (mem_setAction_ker _ u.val).mp u.property
  let g : MulAction.stabilizer M23 (9 : Fin 23) :=
    ⟨u.val.val, hf 9 (Finset.mem_insert_self _ _)⟩
  let k := m23EquivM22PointStabilizer.symm g
  have hk : ∀ a ∈ B, k • a = a := by
    apply (fixes_augmented_iff B k).mp
    simpa only [k, MulEquiv.apply_symm_apply] using hf
  have hs : k ∈ MulAction.stabilizer M22 B := by
    apply MulAction.mem_stabilizer_finset'.mpr
    intro a ha
    rwa [hk a ha]
  exact ⟨⟨k, hs⟩, (mem_m22SetAction_ker B _).mpr hk⟩

/-- The actual pointwise kernel agrees with that of the augmented heptad. -/
noncomputable def m22AugmentedKernelEquiv (B : Finset (Fin 22)) :
    (m22SetAction B).ker ≃* (setAction (m22M23AugmentedBlock B)).ker where
  toFun := kernelForward B
  invFun := kernelBackward B
  left_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    exact m23EquivM22PointStabilizer.symm_apply_apply (u.val : M22)
  right_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun k : MulAction.stabilizer M23 (9 : Fin 23) => (k : M23))
      (m23EquivM22PointStabilizer.apply_symm_apply _)
  map_mul' u v := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun k : MulAction.stabilizer M23 (9 : Fin 23) => (k : M23))
      (m23EquivM22PointStabilizer.map_mul _ _)

@[simp] theorem m22AugmentedKernelEquiv_coe (B : Finset (Fin 22))
    (u : (m22SetAction B).ker) :
    ((m22AugmentedKernelEquiv B u).val : M23) =
      (m23EquivM22PointStabilizer (u.val : M22) : M23) := by rfl

private theorem conjugate_kernel {B : Finset (Fin 23)} {g : M23}
    (hg : g • omega = B) :
    heptadKernel.map (MulAction.stabilizerEquivStabilizer hg.symm).toMonoidHom =
      (setAction B).ker := by
  let e : heptadStabilizer ≃* MulAction.stabilizer M23 B :=
    MulAction.stabilizerEquivStabilizer hg.symm
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    apply (mem_setAction_ker B _).mpr
    intro b hb
    have hb' : b ∈ g • omega := hg.symm ▸ hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_smul_finset.mp hb'
    have hfix := (mem_heptadKernel y).mp hy a ha
    change (MulAut.conj g (y : M23)) • (g • a) = g • a
    simp only [MulAut.conj_apply, mul_smul, inv_smul_smul, hfix]
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply (mem_heptadKernel _).mpr
    intro a ha
    have hfix := (mem_setAction_ker B x).mp hx (g • a)
      (hg ▸ Finset.smul_mem_smul_finset ha)
    change (MulAut.conj g⁻¹ (x : M23)) • a = a
    simp only [MulAut.conj_apply, mul_smul, inv_inv, hfix, inv_smul_smul]

/-- The pointwise hexad kernel is isomorphic to the certified M23 translation kernel. -/
noncomputable def m22HexadKernelEquiv {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (m22SetAction B).ker ≃* heptadKernel := by
  let g := Classical.choose (exists_smul_omega_eq (m22Hexad_augmented_mem hB))
  have hg := Classical.choose_spec (exists_smul_omega_eq (m22Hexad_augmented_mem hB))
  let e := MulAction.stabilizerEquivStabilizer hg.symm
  exact (m22AugmentedKernelEquiv B).trans
    (((e.subgroupMap heptadKernel).trans
      (MulEquiv.subgroupCongr (conjugate_kernel hg))).symm)

/-- The kernel is elementary abelian, by its actual binary translation model. -/
theorem m22HexadKernel_elementaryAbelian {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    IsElementaryAbelian 2 (m22SetAction B).ker := by
  let e := m22HexadKernelEquiv hB
  refine { is_comm := ⟨fun u v => e.injective ?_⟩, exponent_dvd_p := ?_ }
  · rw [map_mul, map_mul]
    exact heptadKernel_mul_comm _ _
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro u
    apply e.injective
    simp only [map_pow, map_one, heptadKernel_sq]

/-- The pointwise hexad kernel has order sixteen. -/
theorem m22HexadKernel_card {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    Nat.card (m22SetAction B).ker = 16 :=
  (Nat.card_congr (m22HexadKernelEquiv hB).toEquiv).trans heptadKernel_card

end Sporadic.Mathieu
