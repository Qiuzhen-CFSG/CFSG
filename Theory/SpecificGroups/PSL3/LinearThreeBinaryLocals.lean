module

public import Theory.SpecificGroups.PSL3.LinearThreeFlags
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores.Identification
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Symmetric-four identifications for the binary degree-three locals

Over a two-element field the vector and covector stabilizers coincide with
those of the corresponding subspaces. Entrywise field transport identifies
their special-linear preimages with the concrete binary parabolics. Composing
with the actual projective projection and the faithful four-point actions
gives isomorphisms from both original projective local groups to S₄.

Source: Aschbacher–Smith, F.1.12(I)(1), printed pp.262–264.
Field transport uses the attributed ATLAS port in
`Theory.AtlasPort.ExceptionalIsomorphisms.Support`; its source attribution and
ATLAS Research and Attribution License 1.0 notice are retained there.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree
variable {F K : Type*} [Field F] [Field K]

private theorem pointLocalSL_map_field (e : F ≃+* K) :
    (pointLocalSL F).map (Atlas.fieldEquivSL 3 e).toMonoidHom = pointLocalSL K := by
  ext g
  obtain ⟨g, rfl⟩ := (Atlas.fieldEquivSL 3 e).surjective g
  change (Atlas.fieldEquivSL 3 e).toMonoidHom g ∈ _ ↔ _
  rw [mem_map_iff_mem (f := (Atlas.fieldEquivSL 3 e).toMonoidHom) (Atlas.fieldEquivSL 3 e).injective,
    mem_pointLocalSL_iff, mem_pointLocalSL_iff]
  change (g.val 0 0 = 1 ∧ g.val 1 0 = 0 ∧ g.val 2 0 = 0) ↔
    (e (g.val 0 0) = 1 ∧ e (g.val 1 0) = 0 ∧ e (g.val 2 0) = 0)
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨(congrArg e h0).trans (map_one e),
      (congrArg e h1).trans (map_zero e), (congrArg e h2).trans (map_zero e)⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨e.injective (h0.trans (map_one e).symm),
      e.injective (h1.trans (map_zero e).symm), e.injective (h2.trans (map_zero e).symm)⟩

private theorem lineLocalSL_map_field (e : F ≃+* K) :
    (lineLocalSL F).map (Atlas.fieldEquivSL 3 e).toMonoidHom = lineLocalSL K := by
  ext g
  obtain ⟨g, rfl⟩ := (Atlas.fieldEquivSL 3 e).surjective g
  change (Atlas.fieldEquivSL 3 e).toMonoidHom g ∈ _ ↔ _
  rw [mem_map_iff_mem (f := (Atlas.fieldEquivSL 3 e).toMonoidHom) (Atlas.fieldEquivSL 3 e).injective,
    mem_lineLocalSL_iff, mem_lineLocalSL_iff]
  change (g.val 2 0 = 0 ∧ g.val 2 1 = 0 ∧ g.val 2 2 = 1) ↔
    (e (g.val 2 0) = 0 ∧ e (g.val 2 1) = 0 ∧ e (g.val 2 2) = 1)
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨(congrArg e h0).trans (map_zero e),
      (congrArg e h1).trans (map_zero e), (congrArg e h2).trans (map_one e)⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨e.injective (h0.trans (map_zero e).symm),
      e.injective (h1.trans (map_zero e).symm), e.injective (h2.trans (map_one e).symm)⟩

private theorem pointLocalSL_binary_eq :
    pointLocalSL (ZMod 2) = Matrix.PSL3Two.pointParabolicSL := by
  ext g
  rw [mem_pointLocalSL_iff, Matrix.PSL3Two.mem_pointParabolicSL_iff]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  apply (show ∀ x : ZMod 2, x ≠ 0 → x = 1 by decide)
  intro hz
  have hd := g.property
  rw [Matrix.det_fin_three] at hd
  simp [hz, h.1, h.2] at hd

private theorem lineLocalSL_binary_eq :
    lineLocalSL (ZMod 2) = Matrix.PSL3Two.lineParabolicSL := by
  ext g
  rw [mem_lineLocalSL_iff, Matrix.PSL3Two.mem_lineParabolicSL_iff]
  refine ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, ?_⟩⟩
  apply (show ∀ x : ZMod 2, x ≠ 0 → x = 1 by decide)
  intro hz
  have hd := g.property
  rw [Matrix.det_fin_three] at hd
  simp [hz, h.1, h.2] at hd

/-- The actual point local over a two-element field is the symmetric group on four letters. -/
noncomputable def binaryPointLocalEquivS4 (F : Type*) [Field F] [Finite F]
    (hF : Nat.card F = 2) : pointLocal F ≃* Equiv.Perm (Fin 4) := by
  letI : Fintype F := Fintype.ofFinite F
  let e : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  exact (pointLocalProjectEquiv F).symm.trans
    (((Atlas.fieldEquivSL 3 e).subgroupMap (pointLocalSL F)).trans
      ((MulEquiv.subgroupCongr (pointLocalSL_map_field e)).trans
        ((MulEquiv.subgroupCongr pointLocalSL_binary_eq).trans
          (((Matrix.PSL3Two.pointParabolicSL).equivMapOfInjective
            Matrix.PSL3Two.project Matrix.PSL3Two.project_injective).trans
              Matrix.PSL3Two.pointParabolicEquivS4))))

/-- The actual line local over a two-element field is the symmetric group on four letters. -/
noncomputable def binaryLineLocalEquivS4 (F : Type*) [Field F] [Finite F]
    (hF : Nat.card F = 2) : lineLocal F ≃* Equiv.Perm (Fin 4) := by
  letI : Fintype F := Fintype.ofFinite F
  let e : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  exact (lineLocalProjectEquiv F).symm.trans
    (((Atlas.fieldEquivSL 3 e).subgroupMap (lineLocalSL F)).trans
      ((MulEquiv.subgroupCongr (lineLocalSL_map_field e)).trans
        ((MulEquiv.subgroupCongr lineLocalSL_binary_eq).trans
          (((Matrix.PSL3Two.lineParabolicSL).equivMapOfInjective
            Matrix.PSL3Two.project Matrix.PSL3Two.project_injective).trans
              Matrix.PSL3Two.lineParabolicEquivS4))))

end Matrix.PSL3.LinearThree
