module

public import Theory.Representation.MathieuCodeRestriction.M22.Construction
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.KernelGeometry
public import Theory.Mathieu.M24.LocalGeometry.LinearFourCore

/-!
# Marked hexads and their pointwise octad kernels

Adjoining native coordinates 0 and 9 sends every native M22 hexad to an
actual Witt octad. The image of the original pointwise hexad kernel is exactly
the existing M24 octad restriction kernel, included in M24. For the reverse
inclusion, an octad pointwise fixer fixes the two distinguished points, so it
lifts through the actual M23 and M22 point-stabilizer maps. Both the group
isomorphism and conjugation comparison retain these coordinate maps.

Source: Aschbacher--Smith, H.13.1 and H.14, printed pp.395--398;
marked restriction used in 13.8.21(2), printed p.956.
-/

@[expose] public section

noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open scoped Pointwise
namespace MathieuCode

/-- Adjoin the two distinguished fixed points to the native hexad. -/
def m22AugmentedOctad (B : Finset (Fin 22)) : Finset (Fin 24) :=
  m23AugmentedBlock (m22M23AugmentedBlock B)

theorem m22AugmentedOctad_eq (B : Finset (Fin 22)) :
    m22AugmentedOctad B = insert 0 (insert 9 (B.map m22Coordinates)) := by
  have he : m23PointEmbedding 9 = (9 : Fin 24) := by decide +kernel
  simp [m22AugmentedOctad, m23AugmentedBlock, m23LiftBlock,
    m22M23AugmentedBlock, m22M23LiftBlock, Finset.map_insert, Finset.map_map,
    m22Coordinates, he]

@[simp] theorem mem_m22AugmentedOctad (B : Finset (Fin 22)) (i : Fin 24) :
    i ∈ m22AugmentedOctad B ↔ i = 0 ∨ i = 9 ∨ ∃ a ∈ B, m22Coordinates a = i := by
  rw [m22AugmentedOctad_eq]
  simp

theorem m22AugmentedOctad_mem {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    m22AugmentedOctad B ∈ m24Blocks := by
  have h := m22Hexad_augmented_mem hB
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
  unfold m22AugmentedOctad
  rw [← hi, m23AugmentedBlockAt_eq_m24BlockAt]
  exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

/-- The actual native M24 octad associated to a marked M22 hexad. -/
def m22Octad {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) : Octad :=
  ⟨m22AugmentedOctad B, m22AugmentedOctad_mem hB⟩

/-- Include the existing octad restriction kernel into the ambient M24. -/
def octadPointwiseKernel (O : Octad) : Subgroup M24 :=
  (LinearFourCore.action O).ker.map (octadStabilizer O).subtype

@[simp] theorem mem_octadPointwiseKernel (O : Octad) (g : M24) :
    g ∈ octadPointwiseKernel O ↔ ∀ i ∈ O.val, g • i = i := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (LinearFourCore.mem_action_ker O u).mp hu
  · intro hg
    have hs : g ∈ octadStabilizer O := by
      apply MulAction.mem_stabilizer_finset'.mpr
      intro i hi
      rwa [hg i hi]
    exact ⟨⟨g, hs⟩, (LinearFourCore.mem_action_ker O _).mpr hg, rfl⟩

/-- The pointwise kernels agree under the actual M22-to-M24 embedding. -/
theorem m22HexadPointwiseKernel_map {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (m22HexadPointwiseKernel B).map m22Embedding = octadPointwiseKernel (m22Octad hB) := by
  ext g
  constructor
  · rintro ⟨u, hu, rfl⟩
    apply (mem_octadPointwiseKernel _ _).mpr
    intro i hi
    rcases (mem_m22AugmentedOctad B i).mp hi with rfl | rfl | ⟨a, ha, rfl⟩
    · exact m22Embedding_fixed_zero u
    · exact m22Embedding_fixed_nine u
    · change (m22Embedding u).val (m22Coordinates a) = _
      rw [m22Embedding_apply, (mem_m22HexadPointwiseKernel B u).mp hu a ha]
  · intro hg
    have hf := (mem_octadPointwiseKernel _ g).mp hg
    have hzero : g ∈ MulAction.stabilizer M24 (0 : Fin 24) :=
      hf 0 ((mem_m22AugmentedOctad B 0).mpr (Or.inl rfl))
    rw [← pointEmbedding_range] at hzero
    obtain ⟨u, rfl⟩ := hzero
    have hnine : u ∈ MulAction.stabilizer M23 (9 : Fin 23) := by
      apply m23PointEmbedding.injective
      change m23PointEmbedding (u.val 9) = m23PointEmbedding 9
      rw [← pointEmbedding_apply]
      have he : m23PointEmbedding 9 = (9 : Fin 24) := by decide +kernel
      rw [he]
      exact hf 9 ((mem_m22AugmentedOctad B 9).mpr (Or.inr (Or.inl rfl)))
    let v := m23EquivM22PointStabilizer.symm ⟨u, hnine⟩
    have hv : m22InM23 v = u :=
      congrArg (fun k : MulAction.stabilizer M23 (9 : Fin 23) => (k : M23))
        (m23EquivM22PointStabilizer.apply_symm_apply ⟨u, hnine⟩)
    have hev : m22Embedding v = pointEmbedding u := congrArg pointEmbedding hv
    refine ⟨v, (mem_m22HexadPointwiseKernel B v).mpr ?_, hev⟩
    intro a ha
    apply m22Coordinates.injective
    rw [← m22Embedding_apply, hev]
    exact hf _ ((mem_m22AugmentedOctad B _).mpr (Or.inr (Or.inr ⟨a, ha, rfl⟩)))

/-- The pointwise kernel comparison also retains the individual group elements. -/
def m22OctadKernelEquiv {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    m22HexadPointwiseKernel B ≃* octadPointwiseKernel (m22Octad hB) :=
  (Subgroup.equivMapOfInjective _ m22Embedding m22Embedding_injective).trans
    (MulEquiv.subgroupCongr (m22HexadPointwiseKernel_map hB))

@[simp] theorem m22OctadKernelEquiv_coe {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (g : m22HexadPointwiseKernel B) :
    (m22OctadKernelEquiv hB g).val = m22Embedding g.val := rfl

/-- Marking a conjugate hexad conjugates its augmented octad by the same native map. -/
theorem m22AugmentedOctad_smul (g : M22) (B : Finset (Fin 22)) :
    m22AugmentedOctad (g • B) = m22Embedding g • m22AugmentedOctad B := by
  ext i
  constructor
  · intro hi
    rcases (mem_m22AugmentedOctad _ _).mp hi with rfl | rfl | ⟨a, ha, rfl⟩
    · exact Finset.mem_smul_finset.mpr ⟨0,
        (mem_m22AugmentedOctad B 0).mpr (Or.inl rfl), m22Embedding_fixed_zero g⟩
    · exact Finset.mem_smul_finset.mpr ⟨9,
        (mem_m22AugmentedOctad B 9).mpr (Or.inr (Or.inl rfl)), m22Embedding_fixed_nine g⟩
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_smul_finset.mp ha
      exact Finset.mem_smul_finset.mpr ⟨m22Coordinates b,
        (mem_m22AugmentedOctad B _).mpr (Or.inr (Or.inr ⟨b, hb, rfl⟩)),
        m22Embedding_apply g b⟩
  · rintro hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_smul_finset.mp hi
    rcases (mem_m22AugmentedOctad B j).mp hj with rfl | rfl | ⟨a, ha, rfl⟩
    · change (m22Embedding g).val 0 ∈ _
      rw [m22Embedding_fixed_zero]
      exact (mem_m22AugmentedOctad _ _).mpr (Or.inl rfl)
    · change (m22Embedding g).val 9 ∈ _
      rw [m22Embedding_fixed_nine]
      exact (mem_m22AugmentedOctad _ _).mpr (Or.inr (Or.inl rfl))
    · change (m22Embedding g).val (m22Coordinates a) ∈ _
      rw [m22Embedding_apply]
      exact (mem_m22AugmentedOctad _ _).mpr
        (Or.inr (Or.inr ⟨g • a, Finset.smul_mem_smul_finset ha, rfl⟩))

end MathieuCode
