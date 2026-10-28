module

public import CFSG.Quasithin.ChapterH.Section13To16.Defs
public import Theory.Mathieu.M24.LocalGeometry.LinearFourCore
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Coverage
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.FixedHeptad
public import Theory.Mathieu.M22.Properties.FixedHexads
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.Fusion
public import Theory.Mathieu.M24.ChapterHStabilizers.PairInvolutions

/-!
# Native stabilizer interfaces for H.14

This module keeps the H.14 geometry in the concrete Witt-design carriers.  The
octad core and the common marked subgroup are mapped through the actual native
point-stabilizer embedding; no abstract Mathieu model is substituted.  The
elementary structure of the common subgroup is unconditional and follows from
the proved native octad-core calculation. The original assembly contracts are
preserved; `Stabilizers.Sextet` and `Stabilizers.CommonFour` now construct them
from the actual native core calculations and compatible Sylow arrangement.

The group-theoretic clauses of H.14.4 are proved here: M24 has exactly two
involution classes, distinguished by two-centrality and their fixed octad or
empty fixed set; M23 and M22 each have one class, fixing a heptad or hexad.
The actual pair stabilizer, identified with Aut(M22), has two outer involution
classes, fixing an octad disjoint from the deleted pair or no points. The
module codimensions and the remaining H.14.1–3 local-action classifications
belong to their separate proofs.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.14.1–H.14.4,
printed pp.396–398 (PDF pp.407–409).
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterH.Section13To16

open Subgroup
open Sporadic.Mathieu
open Sporadic.Mathieu.M23Geometry
open Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24InvolutionCentralizers
open MathieuCode
open scoped Pointwise

/-! ## The common marked subgroup -/

private theorem m23OctadKernel_elementary :
    IsElementaryAbelian 2 (m23OctadKernel standardOctad) := by
  let K : Subgroup M24 := octadKernel standardOctad
  let A : Subgroup M23 := m23OctadKernel standardOctad
  have hK : IsElementaryAbelian 2 K := by
    let _ : IsElementaryAbelian 2 (pCore 2 (octadStabilizer standardOctad)) :=
      (LinearFourCore.octad_core_structure standardOctad).2
    exact IsElementaryAbelian.map_subtype
  have hle : A.map pointEmbedding ≤ K := by
    exact Subgroup.map_comap_le _ _
  let f₀ : A →* A.map pointEmbedding :=
    (pointEmbedding.comp A.subtype).codRestrict _ (by
      intro x
      exact ⟨x, x.property, rfl⟩)
  let f : A →* K := (Subgroup.inclusion hle).comp f₀
  have hf : Function.Injective f := by
    intro x y hxy
    have hxy' : pointEmbedding (x : M23) = pointEmbedding (y : M23) := by
      exact congrArg (fun z : K => (z : M24)) hxy
    exact Subtype.ext (pointEmbedding_injective hxy')
  exact {
    is_comm := ⟨fun x y => hf (by
      simpa only [map_mul] using hK.toIsMulCommutative.is_comm.comm (f x) (f y))⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => hf (by
      simpa only [map_pow, map_one] using
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hK.exponent_dvd_p (f x)))) }

/-- The marked common subgroup is elementary abelian of characteristic two. -/
public theorem m23CommonKernel_elementary :
    IsElementaryAbelian 2 m23CommonKernel := by
  have hsub : m23CommonKernel ≤ m23OctadKernel standardOctad := by
    intro x hx
    exact hx.1
  let f : m23CommonKernel →* m23OctadKernel standardOctad :=
    Subgroup.inclusion hsub
  have hf : Function.Injective f := Subgroup.inclusion_injective hsub
  exact {
    is_comm := ⟨fun x y => hf (by
      simpa only [map_mul] using
        m23OctadKernel_elementary.toIsMulCommutative.is_comm.comm (f x) (f y))⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => hf (by
      simpa only [map_pow, map_one] using
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          m23OctadKernel_elementary.exponent_dvd_p (f x)))) }

public theorem m23CommonKernel_isPGroup : IsPGroup 2 m23CommonKernel :=
  m23CommonKernel_elementary.isPGroup 2 m23CommonKernel

/-! ## Source-correct assembly contracts -/

/-- The native sextet calculation required by H.14.1–H.14.3.

The subgroup in `kernel` is an intrinsic subgroup of the actual standard
sextet stabilizer.  The equality with its two-core is retained explicitly so
that relative normality is not confused with ambient normality. -/
structure NativeSextetCoreData where
  kernel : Subgroup M24
  kernel_le_stabilizer : kernel ≤ sextetStabilizer standardSextet
  kernel_elementary : IsElementaryAbelian 2 kernel
  kernel_card : Nat.card kernel = 64
  kernel_eq_pCore :
    kernel = (pCore 2 (sextetStabilizer standardSextet)).map
      (sextetStabilizer standardSextet).subtype

/-- The compatible M₂₃ common-four calculation.

The coverage clause is the source assertion that every native elementary
abelian subgroup of order sixteen contains a conjugate of the marked common
subgroup.  Its conjugator is in the native M₂₃ carrier. -/
structure NativeM23CommonFourData : Prop where
  common_card : Nat.card m23CommonKernel = 4
  coverage : ∀ A : Subgroup M23, IsElementaryAbelian 2 A → Nat.card A = 16 →
    ∃ g : M23,
      m23CommonKernel.map (MulAut.conj g).toMonoidHom ≤ A

public theorem m23CommonKernel_order_four (h : NativeM23CommonFourData) :
    Nat.card m23CommonKernel = 4 :=
  h.common_card

public theorem m23CommonKernel_isKleinFour (h : NativeM23CommonFourData) :
    IsElementaryAbelian 2 m23CommonKernel ∧ Nat.card m23CommonKernel = 4 :=
  ⟨m23CommonKernel_elementary, h.common_card⟩

public theorem m23_card16_contains_common_conjugate
    (h : NativeM23CommonFourData) (A : Subgroup M23)
    (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 16) :
    ∃ g : M23,
      m23CommonKernel.map (MulAut.conj g).toMonoidHom ≤ A :=
  h.coverage A hA hcard

/-! ## Involutions on the native designs -/

/-- Every native M₂₄ involution is in exactly one of the two checked classes. -/
public theorem m24_involution_classification (x : M24) (hx : orderOf x = 2) :
    IsConj involution2A x ∨ IsConj involution2B x :=
  involution_classes x hx

/-! M₂₃ and M₂₂ fixed-set geometry is already native in their local modules. -/

public theorem m23_involution_has_fixed_heptad (x : M23) (hx : orderOf x = 2) :
    ∃ H ∈ m23Blocks, ∀ a : Fin 23, x • a = a ↔ a ∈ H := by
  refine ⟨fixedHeptad x, fixedHeptad_mem hx, ?_⟩
  intro a
  exact (mem_fixedHeptad x a).symm

public theorem m22_involution_has_fixed_hexad (x : M22) (hx : orderOf x = 2) :
    ∃ H ∈ m22Blocks, ∀ a : Fin 22, x • a = a ↔ a ∈ H :=
  m22_exists_fixed_hexad x hx

/-- The two native M24 classes are distinct, as detected by their fixed sets. -/
public theorem m24_involution_classes_distinct : ¬ IsConj involution2A involution2B :=
  M24ChapterHStabilizers.classes_disjoint

/-- Source two-centrality means centrality in an actual Sylow two-subgroup. -/
public theorem m24_twoCentral_iff_class2A (x : M24) :
    Theory.GroupTheory.IsSylowCentralInvolution x ↔ IsConj involution2A x :=
  M24ChapterHStabilizers.sylowCentral_iff_class2A x

/-- H.14.4(1), with both the Sylow-center condition and the exact fixed-point set. -/
public theorem m24_involution_fixed_set_classification (x : M24) (hx : orderOf x = 2) :
    (Theory.GroupTheory.IsSylowCentralInvolution x ∧
      ∃ O : Octad, ∀ a : Fin 24, x • a = a ↔ a ∈ O.val) ∨
    (¬ Theory.GroupTheory.IsSylowCentralInvolution x ∧ ∀ a : Fin 24, x • a ≠ a) := by
  rcases involution_classes x hx with h | h
  · refine Or.inl ⟨(m24_twoCentral_iff_class2A x).mpr h, ?_⟩
    refine ⟨⟨M24ChapterHStabilizers.fixedPoints x,
      M24ChapterHStabilizers.class2A_fixed_octad h⟩, ?_⟩
    intro a
    exact (M24ChapterHStabilizers.mem_fixedPoints x a).symm
  · refine Or.inr ⟨(M24ChapterHStabilizers.not_sylowCentral_iff_class2B x hx).mpr h, ?_⟩
    intro a ha
    have hm := (M24ChapterHStabilizers.mem_fixedPoints x a).mpr ha
    rw [M24ChapterHStabilizers.class2B_fixed_empty h] at hm
    exact Finset.notMem_empty _ hm

/-- H.14.4(2): native M23 involutions form one conjugacy class. -/
public theorem m23_involutions_conjugate (x y : M23)
    (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y :=
  involutions_isConj x y hx hy

/-- H.14.4(2): native M22 involutions form one conjugacy class. -/
public theorem m22_involutions_conjugate (x y : M22)
    (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y :=
  m22_involutions_isConj x y hx hy

/-- H.14.4(4), group clause: coverage in the actual automorphism group of M22. -/
public theorem m22_outer_involution_classes (r : MulAut M22) (hr : orderOf r = 2)
    (ho : ¬ ∃ g : M22, r = MulAut.conj g) :
    IsConj (M24ChapterHStabilizers.outerAutRepresentative true) r ∨
      IsConj (M24ChapterHStabilizers.outerAutRepresentative false) r :=
  M24ChapterHStabilizers.outer_aut_involution_classes r hr ho

/-- The two outer representatives genuinely define distinct conjugacy classes. -/
public theorem m22_outer_involution_classes_distinct :
    ¬ IsConj (M24ChapterHStabilizers.outerAutRepresentative true)
      (M24ChapterHStabilizers.outerAutRepresentative false) :=
  M24ChapterHStabilizers.outer_aut_classes_disjoint

/-- Both representatives are outer involutions, so both source cases occur. -/
public theorem m22_outer_involution_representatives (a : Bool) :
    orderOf (M24ChapterHStabilizers.outerAutRepresentative a) = 2 ∧
      ¬ ∃ g : M22, M24ChapterHStabilizers.outerAutRepresentative a = MulAut.conj g :=
  ⟨M24ChapterHStabilizers.outerAutRepresentative_order a,
    M24ChapterHStabilizers.outerAutRepresentative_outer a⟩

/-- H.14.4(4), design clause: the octad avoids the marked deleted coordinates.
The fixed set is computed on the original 22 points through their native embedding. -/
public theorem m22_outer_involution_fixed_geometry
    (x : MathieuCode.m22PairStabilizer) (hx : orderOf x = 2)
    (ho : x.val ∉ m22PointwisePairStabilizer) :
    ((M24ChapterHStabilizers.reducedFixedPoints x).image m22Coordinates ∈ m24Blocks ∧
      Disjoint ((M24ChapterHStabilizers.reducedFixedPoints x).image m22Coordinates) m22Pair ∧
      (M24ChapterHStabilizers.reducedFixedPoints x).card = 8) ∨
      M24ChapterHStabilizers.reducedFixedPoints x = ∅ :=
  M24ChapterHStabilizers.outer_pair_reduced_fixed_geometry x hx ho

end CFSG.Quasithin.ChapterH.Section13To16

end
