module

public import Theory.GroupTheory.Recognition.JankoFour.LocalHypotheses
public import Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.Intrinsic
public import Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.LocalSubgroups.Defs
public import Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.LocalSubgroups.CubicCore
public import Mathlib.FieldTheory.Finiteness
public import Theory.ElementaryAbelian.Quotient

/-!
# Algebraic assembly of the marked type-J₄ local subgroups

The cubic lift is the literal O_{2,3}(C_G(z)). For every specified inverse
image under its quotient map, we construct the restricted surjection and the
quotient isomorphism, retaining the original elements and relative kernels.
In particular the point and line outputs from `Defs` contain that same cubic
lift, and their common intersection contains it as well. The point radical
is elementary of order 2¹¹ and is the kernel of the split projection onto M₂₄.
The final index-transfer lemma reduces the source indices 15 and 5 to the
literal native pair–hexad stabilizers; those model indices remain explicit.

These are conditional assembly results. Construction of `PointData` from
`IsTypeJ4` and construction of the compatible `LineData` remain necessary;
no source existence theorem is asserted here.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), §4; exposition (3.1),
pp.16–17. The denominator below is the iterated core of the plane group,
not an assumed iterated core of an intersection.
-/

@[expose] public section

namespace Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.LocalSubgroups

open Subgroup Sporadic.Mathieu

variable {G : Type*} [Group G] [Finite G] {z : G}

section Overlap

variable (e : CubicAutomorphismQuotient ((centralizer z) ⧸ core z))
    (U : Subgroup (centralizer z)) (A : Subgroup (MulAut M22))
    (hU : U = A.comap (CubicLift.projection e))

/-- Restriction of the original quotient map to an actual inverse image. -/
noncomputable def overlapProjection : U →* A where
  toFun u := ⟨CubicLift.projection e u.val, hU.le u.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' u v := Subtype.ext (map_mul _ u.val v.val)

theorem overlapProjection_surjective : Function.Surjective (overlapProjection e U A hU) := by
  intro a
  obtain ⟨u, hu⟩ := CubicLift.projection_surjective e a.val
  have hm : u ∈ U := by
    rw [hU]
    change CubicLift.projection e u ∈ A
    rw [hu]
    exact a.property
  exact ⟨⟨u, hm⟩, Subtype.ext hu⟩

theorem overlapProjection_ker (h : IsTypeJ4 z) :
    (overlapProjection e U A hU).ker = (twoThreeCore (centralizer z)).subgroupOf U := by
  rw [← cubicLift_eq_twoThreeCore h e]
  ext u
  change (⟨CubicLift.projection e u.val, _⟩ : A) = 1 ↔ _
  rw [Subtype.ext_iff]
  rfl

/-- The quotient uses the plane group's cubic lift, restricted to the overlap. -/
noncomputable def overlapQuotientEquiv (h : IsTypeJ4 z) :
    (U ⧸ (twoThreeCore (centralizer z)).subgroupOf U) ≃* A :=
  (QuotientGroup.quotientMulEquivOfEq (overlapProjection_ker e U A hU h).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (overlapProjection_surjective e U A hU))

@[simp] theorem overlapQuotientEquiv_mk (h : IsTypeJ4 z) (u : U) :
    overlapQuotientEquiv e U A hU h (QuotientGroup.mk' _ u) =
      overlapProjection e U A hU u := rfl

include hU in
theorem twoThreeCore_le_overlap (h : IsTypeJ4 z) : twoThreeCore (centralizer z) ≤ U := by
  rw [← cubicLift_eq_twoThreeCore h e, hU]
  intro u hu
  change CubicLift.projection e u ∈ A
  rw [show CubicLift.projection e u = 1 from hu]
  exact A.one_mem

end Overlap

/-- Actual application to the point-plane intersection of the marked witness. -/
noncomputable def PointData.planeQuotientEquiv (P : PointData z) (h : IsTypeJ4 z) :
    (P.M.subgroupOf (centralizer z) ⧸
      (twoThreeCore (centralizer z)).subgroupOf (P.M.subgroupOf (centralizer z))) ≃*
      designStabilizer P.hexad :=
  overlapQuotientEquiv P.cubic _ _ P.overlap h

/-- Actual application to the line-plane intersection, using the same cubic map. -/
noncomputable def LineData.planeQuotientEquiv {P : PointData z} (L : LineData z P)
    (h : IsTypeJ4 z) :
    (L.G₂.subgroupOf (centralizer z) ⧸
      (twoThreeCore (centralizer z)).subgroupOf (L.G₂.subgroupOf (centralizer z))) ≃*
      designStabilizer L.pair :=
  overlapQuotientEquiv P.cubic _ _ L.plane_overlap h

/-- Both overlaps retain the whole cubic lift in the original ambient group. -/
theorem cubicLift_le_triple {P : PointData z} (L : LineData z P) (h : IsTypeJ4 z) :
    ambientTwoThreeCore z ≤ P.M ⊓ L.G₂ ⊓ centralizer z := by
  have hP := twoThreeCore_le_overlap P.cubic _ _ P.overlap h
  have hL := twoThreeCore_le_overlap P.cubic _ _ L.plane_overlap h
  rintro _ ⟨u, hu, rfl⟩
  exact ⟨⟨hP hu, hL hu⟩, u.property⟩


/-- Coordinates on the literal ambient elementary normal subgroup. -/
noncomputable def PointData.vectorEquiv (P : PointData z) : ToddVector ≃* P.E :=
  MulEquiv.ofBijective P.vectorEmbedding.rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr P.vectorEmbedding_injective,
      P.vectorEmbedding.rangeRestrict_surjective⟩

theorem PointData.E_card (P : PointData z) : Nat.card P.E = 2 ^ 11 := by
  rw [← Nat.card_congr P.vectorEquiv.toEquiv]
  change Nat.card MathieuCode.Cocode = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), MathieuCode.finrank_cocode, Nat.card_zmod]

theorem PointData.E_elementary (P : PointData z) : IsElementaryAbelian 2 P.E := by
  let : IsElementaryAbelian 2 ToddVector := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro v
      change (2 : ℕ) • v.toAdd = 0
      rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
      exact zero_smul (ZMod 2) v.toAdd) }
  exact IsElementaryAbelian.of_surjective P.vectorEquiv.toMonoidHom P.vectorEquiv.surjective

noncomputable def PointData.projection (P : PointData z) : P.M →* M24 :=
  SemidirectProduct.rightHom.comp P.toddEquiv.symm.toMonoidHom

theorem PointData.projection_ker (P : PointData z) :
    P.projection.ker = P.E.subgroupOf P.M := by
  ext m
  constructor
  · intro hm
    have he : (P.toddEquiv.symm m).right = 1 := hm
    refine ⟨(P.toddEquiv.symm m).left, ?_⟩
    change (P.toddEquiv (SemidirectProduct.inl (P.toddEquiv.symm m).left) : G) = m.val
    have hh : SemidirectProduct.inl (P.toddEquiv.symm m).left = P.toddEquiv.symm m := by
      ext <;> simp [he]
    rw [hh, P.toddEquiv.apply_symm_apply]
  · rintro ⟨v, hv⟩
    have hm : P.toddEquiv (SemidirectProduct.inl v) = m := Subtype.ext hv
    rw [← hm]
    change (P.toddEquiv.symm (P.toddEquiv (SemidirectProduct.inl v))).right = 1
    rw [P.toddEquiv.symm_apply_apply]
    rfl

theorem PointData.E_normal (P : PointData z) : (P.E.subgroupOf P.M).Normal := by
  rw [← P.projection_ker]
  infer_instance

private theorem overlap_relIndex (e : CubicAutomorphismQuotient ((centralizer z) ⧸ core z))
    (A B : Subgroup (MulAut M22)) :
    ((A.comap (CubicLift.projection e)) ⊓ (B.comap (CubicLift.projection e))).relIndex
      (A.comap (CubicLift.projection e)) = (A ⊓ B).relIndex A := by
  rw [← comap_inf, relIndex_comap, map_comap_eq_self_of_surjective (CubicLift.projection_surjective e)]

/-- Transfer of the two native flag indices to the original ambient intersections. -/
theorem tripleIndices {P : PointData z} (L : LineData z P)
    (hpoint : (designStabilizer P.hexad ⊓ designStabilizer L.pair).relIndex
      (designStabilizer P.hexad) = 15)
    (hline : (designStabilizer P.hexad ⊓ designStabilizer L.pair).relIndex
      (designStabilizer L.pair) = 5) :
    (P.M ⊓ L.G₂ ⊓ centralizer z).relIndex (P.M ⊓ centralizer z) = 15 ∧
      (P.M ⊓ L.G₂ ⊓ centralizer z).relIndex (L.G₂ ⊓ centralizer z) = 5 := by
  have htriple : (P.M ⊓ L.G₂ ⊓ centralizer z).subgroupOf (centralizer z) =
      P.M.subgroupOf (centralizer z) ⊓ L.G₂.subgroupOf (centralizer z) := by
    ext x
    simp only [mem_subgroupOf, mem_inf, x.property, and_true]
  have hpoint' : (P.M ⊓ centralizer z).subgroupOf (centralizer z) =
      P.M.subgroupOf (centralizer z) := by
    ext x
    simp only [mem_subgroupOf, mem_inf, x.property, and_true]
  have hline' : (L.G₂ ⊓ centralizer z).subgroupOf (centralizer z) =
      L.G₂.subgroupOf (centralizer z) := by
    ext x
    simp only [mem_subgroupOf, mem_inf, x.property, and_true]
  constructor
  · rw [← relIndex_subgroupOf (L := centralizer z) inf_le_right,
      htriple, hpoint', P.overlap, L.plane_overlap, overlap_relIndex, hpoint]
  · rw [← relIndex_subgroupOf (L := centralizer z) inf_le_right,
      htriple, hline', P.overlap, L.plane_overlap, inf_comm, overlap_relIndex, inf_comm, hline]

end Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.LocalSubgroups
