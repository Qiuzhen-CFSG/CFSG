module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.PlaneGeneration

/-!
# The actual fifteen-point source plane action

Transport the coset action of N_G(A₂) through the literal residue bijection.
The result agrees on every point with the ambient action on G/N_G(U₁).
Its kernel is the preimage of the specified normal cubic subgroup of
N_G(A₂)/A₂. Thus the permutation image is S₆ and the kernel has order 192.
The image isomorphism retains the original two quotient maps on every element.

This establishes the effective point action of the source plane. Identifying
its incidence with the native sextet, constructing compatible full local
isomorphisms, and proving global generation remain separate obligations.

Source: Aschbacher, *Sporadic Groups* (1994), 41.1–41.4, pp.219–222.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer GraphUniquenessSystem.Cosets
variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z)

/-- The action on the literal ambient point cosets incident with the marked plane. -/
noncomputable def planePointAction : threeSpaceNormalizer F →*
    Equiv.Perm (Residue (threeSpaceNormalizer F) (rowNormalizer F)) :=
  (residueEquiv (threeSpaceNormalizer F) (rowNormalizer F)).permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom (threeSpaceNormalizer F)
      (threeSpaceNormalizer F ⧸ (rowNormalizer F).subgroupOf (threeSpaceNormalizer F)))

/-- The action retains multiplication of the original ambient representatives. -/
theorem planePointAction_representative (g a : threeSpaceNormalizer F) :
    (planePointAction F g
      (residueEquiv (threeSpaceNormalizer F) (rowNormalizer F) (QuotientGroup.mk a))).val =
      vertex (rowNormalizer F) ((g : G) * (a : G)) := by
  change ((residueEquiv (threeSpaceNormalizer F) (rowNormalizer F))
    (g • ((residueEquiv (threeSpaceNormalizer F) (rowNormalizer F)).symm
      (residueEquiv (threeSpaceNormalizer F) (rowNormalizer F) (QuotientGroup.mk a))))).val = _
  rw [Equiv.symm_apply_apply]
  exact residueEquiv_mk _ _ (g * a)

/-- On every incident point the new action is the original ambient left action. -/
theorem planePointAction_ambient (g : threeSpaceNormalizer F)
    (a : Residue (threeSpaceNormalizer F) (rowNormalizer F)) :
    (planePointAction F g a).val = (g : G) • a.val := by
  obtain ⟨q, rfl⟩ := (residueEquiv (threeSpaceNormalizer F) (rowNormalizer F)).surjective a
  induction q using QuotientGroup.induction_on with
  | H a => rw [planePointAction_representative, residueEquiv_mk, smul_vertex]

/-- The action kernel is the normal core of the literal point–plane stabilizer. -/
theorem planePointAction_kernel : (planePointAction F).ker =
    ((rowNormalizer F).subgroupOf (threeSpaceNormalizer F)).normalCore := by
  rw [normalCore_eq_ker]
  ext g
  change (residueEquiv (threeSpaceNormalizer F) (rowNormalizer F)).permCongrHom
    (MulAction.toPermHom (threeSpaceNormalizer F)
      (threeSpaceNormalizer F ⧸ (rowNormalizer F).subgroupOf (threeSpaceNormalizer F)) g) = 1 ↔ _
  exact MulEquiv.map_eq_one_iff _

private theorem core_comap {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (hf : Function.Surjective f) (H : Subgroup Y) :
    (H.comap f).normalCore = H.normalCore.comap f := by
  ext g
  change (∀ x : X, f (x * g * x⁻¹) ∈ H) ↔ ∀ y : Y, y * f g * y⁻¹ ∈ H
  constructor
  · intro h y
    obtain ⟨x, rfl⟩ := hf y
    simpa only [map_mul, map_inv] using h x
  · intro h x
    simpa only [map_mul, map_inv] using h (f x)

variable [Finite G] (D : LocalData F)
include D

/-- The point–plane core is the preimage of the original normal cubic subgroup. -/
theorem plane_point_core :
    ((rowNormalizer F).subgroupOf (threeSpaceNormalizer F)).normalCore =
      D.cubicKernel.comap (QuotientGroup.mk' (F.threeSpace.subgroupOf (threeSpaceNormalizer F))) := by
  let A := F.threeSpace.subgroupOf (threeSpaceNormalizer F)
  let J := (rowNormalizer F).subgroupOf (threeSpaceNormalizer F)
  let q := QuotientGroup.mk' A
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective A
  have hk : q.ker ≤ J := by
    rw [QuotientGroup.ker_mk']
    exact fun a ha => threeSpace_le_row_normalizer F ha
  have hi : (J.map q).index = 15 := by
    rw [index_map_eq _ hq hk]
    exact plane_point_index F D
  let := D.cubicKernel_normal
  have hm := SymmetricSix.CubicExtension.index_fifteen_normalCore_of_cubic
    D.cubicKernel (J.map q) D.cubicKernel_card D.cubicKernel_quotient.some hi
  have he : (J.map q).comap q = J := by rw [comap_map_eq, sup_eq_left.mpr hk]
  change J.normalCore = _
  rw [← he, core_comap q hq, hm]

/-- The full kernel on the fifteen literal points, through the original rectangle quotient. -/
theorem planePointAction_kernel_eq : (planePointAction F).ker =
    D.cubicKernel.comap (QuotientGroup.mk' (F.threeSpace.subgroupOf (threeSpaceNormalizer F))) := by
  rw [planePointAction_kernel, plane_point_core F D]

/-- The source quotient through A₂ and its specified cubic normal subgroup. -/
noncomputable def planeSymmetricQuotient : threeSpaceNormalizer F →* Equiv.Perm (Fin 6) :=
  letI := D.cubicKernel_normal
  D.cubicKernel_quotient.some.toMonoidHom.comp
    ((QuotientGroup.mk' D.cubicKernel).comp
      (QuotientGroup.mk' (F.threeSpace.subgroupOf (threeSpaceNormalizer F))))

omit [Finite G] in
/-- The original successive quotient maps give a surjection onto S₆. -/
theorem planeSymmetricQuotient_surjective : Function.Surjective (planeSymmetricQuotient F D) := by
  let := D.cubicKernel_normal
  exact D.cubicKernel_quotient.some.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))

/-- The specified source quotient has exactly the kernel of the actual plane-point action. -/
theorem planeSymmetricQuotient_kernel :
    (planeSymmetricQuotient F D).ker = (planePointAction F).ker := by
  rw [planePointAction_kernel_eq F D]
  ext g
  let := D.cubicKernel_normal
  change D.cubicKernel_quotient.some
    (QuotientGroup.mk (QuotientGroup.mk g)) = 1 ↔ QuotientGroup.mk g ∈ D.cubicKernel
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

/-- The image of the actual fifteen-point action is S₆, with its map retained below. -/
noncomputable def planePointRangeEquiv : (planePointAction F).range ≃* Equiv.Perm (Fin 6) :=
  (QuotientGroup.quotientKerEquivRange (planePointAction F)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (planeSymmetricQuotient_kernel F D).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (planeSymmetricQuotient F D)
        (planeSymmetricQuotient_surjective F D)))

/-- The permutation-image identification agrees with the literal successive quotient maps. -/
theorem planePointRangeEquiv_apply (g : threeSpaceNormalizer F) :
    planePointRangeEquiv F D ⟨planePointAction F g, ⟨g, rfl⟩⟩ =
      planeSymmetricQuotient F D g := by
  rw [planePointRangeEquiv, MulEquiv.trans_apply]
  have he : (QuotientGroup.quotientKerEquivRange (planePointAction F)).symm
      ⟨planePointAction F g, ⟨g, rfl⟩⟩ = QuotientGroup.mk g := by
    apply (QuotientGroup.quotientKerEquivRange (planePointAction F)).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  rw [he, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

/-- The literal fifteen-point action has image of order 720. -/
theorem planePointAction_range_card : Nat.card (planePointAction F).range = 720 := by
  rw [Nat.card_congr (planePointRangeEquiv F D).toEquiv]
  norm_num [Nat.card_perm, Fintype.card_perm, Nat.factorial]

/-- Its full kernel has order 192, retaining the rectangle and cubic factors. -/
theorem planePointAction_kernel_card : Nat.card (planePointAction F).ker = 192 := by
  have h := (planePointAction F).ker.card_mul_index
  rw [index_ker, planePointAction_range_card F D, threeSpace_normalizer_card F D] at h
  omega

omit D [Finite G] in
/-- The original ambient plane action preserves the source collinearity graph. -/
theorem planePointAction_preserves (g : threeSpaceNormalizer F)
    {a b : Residue (threeSpaceNormalizer F) (rowNormalizer F)}
    (h : (graph F).Adj a.val b.val) :
    (graph F).Adj (planePointAction F g a).val (planePointAction F g b).val := by
  rw [planePointAction_ambient, planePointAction_ambient]
  exact graph_preserves F g h

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
