module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.PlaneGroup
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.PlaneChart
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# Simultaneous plane flags and the original local edges

Every plane isomorphism preserves Q and the literal cubic kernel. Its map
on the full Aut(M₂₂) quotient is inner, because M₂₂ is centerless simple.
Native pair–hexad transitivity supplies a single desired flag conjugator.
Lift the difference between these two quotient actors inside the target
cubic normalizer and compose with its inner automorphism. This aligns both
plane overlaps while retaining the marked involution, core, scalar cubic,
normalizer, and an explicit conjugated six-cover restriction.

The constructed map transports equality of the actual ambient left cosets,
so it carries both pointwise and setwise local edge stabilizers. No native
simplicity, target uniqueness system, or new choice of an edge involution
is used. The same correction also proves the plane automorphism control
needed in (8.2).

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (8.2)–(8.3),
pp.606–607. The Aut(H∩M) classification, agreement with the Todd comparison,
and conjugation on the whole edge fixer in M remain further obligations.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry LocalGeometry.LocalSubgroups Sporadic.Mathieu
open scoped Pointwise
variable {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
variable {z : G} {z' : G'} (h : IsTypeJ4 z) (h' : IsTypeJ4 z')
variable (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
variable (e' : CubicAutomorphismQuotient (centralizer z' ⧸ core z'))

include h h' in
/-- The original plane core is intrinsic. -/
theorem planeEquiv_core_map (E : centralizer z ≃* centralizer z') :
    (core z).map E.toMonoidHom = core z' := by
  rw [h.core_eq_twoCore,h'.core_eq_twoCore]
  exact pCore_map_iso 2 E

include h h' in
/-- The full cubic kernel, before discarding its scalar, is intrinsic. -/
theorem planeEquiv_cubicKernel_map (E : centralizer z ≃* centralizer z') :
    (CubicLift.subgroup e).map E.toMonoidHom = CubicLift.subgroup e' := by
  let F := QuotientGroup.congr (core z) (core z') E (planeEquiv_core_map h h' E)
  have he (x : centralizer z) : E x ∈ CubicLift.subgroup e' ↔ x ∈ CubicLift.subgroup e := by
    change QuotientGroup.mk' (core z') (E x) ∈ e'.projection.ker ↔
      QuotientGroup.mk' (core z) x ∈ e.projection.ker
    rw [cubic_kernel_eq_threeCore e,cubic_kernel_eq_threeCore e']
    change F (QuotientGroup.mk' (core z) x) ∈ pCore 3 _ ↔ _
    rw [←pCore_map_iso 3 F]
    exact mem_map_iff_mem (f := F.toMonoidHom) F.injective
  ext y
  obtain ⟨x,rfl⟩ := E.surjective y
  exact (mem_map_iff_mem (f := E.toMonoidHom) E.injective).trans (he x).symm

include h h' in
/-- The quotient discrepancy of any plane isomorphism is an actual inner actor. -/
theorem planeEquiv_projection_inner (E : centralizer z ≃* centralizer z') :
    ∃ b : MulAut M22, ∀ x, CubicLift.projection e' (E x) =
      b * CubicLift.projection e x * b⁻¹ := by
  let F := QuotientGroup.congr (CubicLift.subgroup e) (CubicLift.subgroup e') E
    (planeEquiv_cubicKernel_map h h' e e' E)
  let α : MulAut (MulAut M22) := (CubicLift.automorphismQuotientEquiv e).symm.trans
    (F.trans (CubicLift.automorphismQuotientEquiv e'))
  let := m22_isSimpleGroup
  obtain ⟨b,hb⟩ := MulAut.automorphismTower_inner_of_isSimpleGroup m22_center_eq_bot α
  refine ⟨b,fun x => ?_⟩
  have he : α (CubicLift.projection e x) = CubicLift.projection e' (E x) := by
    change CubicLift.automorphismQuotientEquiv e' (F
      ((CubicLift.automorphismQuotientEquiv e).symm
        ((CubicLift.automorphismQuotientEquiv e) (QuotientGroup.mk' _ x)))) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  rw [←hb] at he
  exact he.symm
end Theory.GroupTheory.Recognition.JankoFour.SourceComparison

namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry LocalGeometry.LocalSubgroups Sporadic.Mathieu
open scoped Pointwise
variable {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
variable {z : G} {z' : G'} {h : IsTypeJ4 z} {h' : IsTypeJ4 z'}
variable (a : SourceIncidence.LocalData h) (a' : SourceIncidence.LocalData h')

/-- One correction in the cubic normalizer aligns both native plane flags. -/
theorem exists_plane_flag_correction (E : centralizer z ≃* centralizer z') :
    ∃ (n : cubicNormalizerInH a'.e a'.X) (g : m22DesignAut),
      g • a.P.hexad = a'.P.hexad ∧ g • a.L.pair = a'.L.pair ∧
      ∀ x, a'.designProjection (n.val * E x * n.val⁻¹) =
        g * a.designProjection x * g⁻¹ := by
  obtain ⟨b,hb⟩ := planeEquiv_projection_inner h h' a.e a'.e E
  obtain ⟨u,huL,huP⟩ := m22_pair_hexad_flag_conjugacy
    a.L.pair_card a.P.hexad_mem a.L.pair_le_hexad
  obtain ⟨v,hvL,hvP⟩ := m22_pair_hexad_flag_conjugacy
    a'.L.pair_card a'.P.hexad_mem a'.L.pair_le_hexad
  let g : m22DesignAut := M22ValueBound.Concrete.inclusion (v*u⁻¹)
  have hgP : g • a.P.hexad = a'.P.hexad := by
    change (v*u⁻¹) • a.P.hexad = a'.P.hexad
    rw [mul_smul,←huP,inv_smul_smul,hvP]
  have hgL : g • a.L.pair = a'.L.pair := by
    change (v*u⁻¹) • a.L.pair = a'.L.pair
    rw [mul_smul,←huL,inv_smul_smul,hvL]
  obtain ⟨n,hn⟩ := cubicNormalizerProjection_surjective h' a'.e a'.X
    (m22DesignAutToAut g * b⁻¹)
  refine ⟨n,g,hgP,hgL,fun x => ?_⟩
  apply m22DesignAutToAut_injective
  simp only [a'.designProjection_marking,map_mul,map_inv,a.designProjection_marking,
    a'.cubic_eq,a.cubic_eq,hb]
  change cubicNormalizerProjection a'.e a'.X n *
    (b * CubicLift.projection a.e x * b⁻¹) *
      (cubicNormalizerProjection a'.e a'.X n)⁻¹ = _
  rw [hn]
  group

private theorem flag_fixed_iff {B : Type*} [MulAction m22DesignAut B]
    (g k : m22DesignAut) (x y : B) (hg : g • x = y) :
    (g*k*g⁻¹) • y = y ↔ k • x = x := by
  rw [←hg,mul_smul,mul_smul,inv_smul_smul]
  exact (MulAction.injective g).eq_iff

private theorem subgroup_map_of_membership {A B : Type*} [Group A] [Group B]
    (S : Subgroup A) (T : Subgroup B) (E : A ≃* B)
    (he : ∀ x, E x ∈ T ↔ x ∈ S) : S.map E.toMonoidHom = T := by
  ext y
  obtain ⟨x,rfl⟩ := E.surjective y
  exact (mem_map_iff_mem (f := E.toMonoidHom) E.injective).trans (he x).symm

/-- The quotient flag equations give the literal subgroup images in H. -/
theorem planeEquiv_flag_images (E : centralizer z ≃* centralizer z') (g : m22DesignAut)
    (hgP : g • a.P.hexad = a'.P.hexad) (hgL : g • a.L.pair = a'.L.pair)
    (he : ∀ x, a'.designProjection (E x) = g * a.designProjection x * g⁻¹) :
    (a.P.M.subgroupOf (centralizer z)).map E.toMonoidHom =
      a'.P.M.subgroupOf (centralizer z') ∧
    (a.L.G₂.subgroupOf (centralizer z)).map E.toMonoidHom =
      a'.L.G₂.subgroupOf (centralizer z') ∧
    ((a.P.M ⊓ a.L.G₂).subgroupOf (centralizer z)).map E.toMonoidHom =
      (a'.P.M ⊓ a'.L.G₂).subgroupOf (centralizer z') := by
  have hP : (a.P.M.subgroupOf (centralizer z)).map E.toMonoidHom =
      a'.P.M.subgroupOf (centralizer z') := by
    apply subgroup_map_of_membership
    intro x
    change (E x : G') ∈ a'.P.M ↔ (x : G) ∈ a.P.M
    rw [a'.point_plane_overlap,a.point_plane_overlap,he]
    exact flag_fixed_iff g (a.designProjection x) a.P.hexad a'.P.hexad hgP
  have hL : (a.L.G₂.subgroupOf (centralizer z)).map E.toMonoidHom =
      a'.L.G₂.subgroupOf (centralizer z') := by
    apply subgroup_map_of_membership
    intro x
    change (E x : G') ∈ a'.L.G₂ ↔ (x : G) ∈ a.L.G₂
    rw [a'.line_plane_overlap,a.line_plane_overlap,he]
    exact flag_fixed_iff g (a.designProjection x) a.L.pair a'.L.pair hgL
  refine ⟨hP,hL,?_⟩
  change ((a.P.M.subgroupOf (centralizer z)) ⊓ a.L.G₂.subgroupOf (centralizer z)).map
    E.toMonoidHom = (a'.P.M.subgroupOf (centralizer z')) ⊓ a'.L.G₂.subgroupOf (centralizer z')
  rw [Subgroup.map_inf _ _ _ E.injective,hP,hL]

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison

namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry LocalGeometry.LocalSubgroups Sporadic.Mathieu
open GraphUniquenessSystem
open scoped Pointwise
variable {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
variable {z : G} {z' : G'} {h : IsTypeJ4 z} {h' : IsTypeJ4 z'}
variable (a : SourceIncidence.LocalData h) (a' : SourceIncidence.LocalData h')

private theorem plane_point_mem_iff (E : centralizer z ≃* centralizer z')
    (hM : (a.P.M.subgroupOf (centralizer z)).map E.toMonoidHom =
      a'.P.M.subgroupOf (centralizer z')) (x : centralizer z) :
    (E x : G') ∈ a'.P.M ↔ (x : G) ∈ a.P.M := by
  change E x ∈ a'.P.M.subgroupOf (centralizer z') ↔ x ∈ a.P.M.subgroupOf (centralizer z)
  rw [←hM]
  exact mem_map_iff_mem (f := E.toMonoidHom) E.injective

/-- The literal left-coset equality is transported by the plane comparison. -/
theorem planeEquiv_coset_eq_iff (E : centralizer z ≃* centralizer z')
    (hM : (a.P.M.subgroupOf (centralizer z)).map E.toMonoidHom =
      a'.P.M.subgroupOf (centralizer z')) (x y : centralizer z) :
    Cosets.vertex a'.P.M (E x : G') = Cosets.vertex a'.P.M (E y : G') ↔
      Cosets.vertex a.P.M (x : G) = Cosets.vertex a.P.M (y : G) := by
  rw [Cosets.vertex_eq_iff,Cosets.vertex_eq_iff]
  have he := plane_point_mem_iff a a' E hM (x⁻¹*y)
  simpa only [map_mul,map_inv,coe_mul,coe_inv] using he

/-- Both the pointwise and setwise edge groups inside H are transported on
the actual ambient left cosets. The target reversal is the image of the
specified source element; no independent involution is chosen. -/
theorem planeEquiv_local_edge_images (E : centralizer z ≃* centralizer z')
    (hM : (a.P.M.subgroupOf (centralizer z)).map E.toMonoidHom =
      a'.P.M.subgroupOf (centralizer z')) (t : centralizer z) :
    ((edgeFixer G (Cosets.vertex a.P.M 1) (Cosets.vertex a.P.M (t : G))).subgroupOf
      (centralizer z)).map E.toMonoidHom =
      (edgeFixer G' (Cosets.vertex a'.P.M 1) (Cosets.vertex a'.P.M (E t : G'))).subgroupOf
        (centralizer z') ∧
    ((edgeStabilizer G (Cosets.vertex a.P.M 1) (Cosets.vertex a.P.M (t : G))).subgroupOf
      (centralizer z)).map E.toMonoidHom =
      (edgeStabilizer G' (Cosets.vertex a'.P.M 1) (Cosets.vertex a'.P.M (E t : G'))).subgroupOf
        (centralizer z') := by
  have he (x y : centralizer z) := planeEquiv_coset_eq_iff a a' E hM x y
  have hb (x : centralizer z) :
      (E x : G') • Cosets.vertex a'.P.M 1 = Cosets.vertex a'.P.M 1 ↔
      (x : G) • Cosets.vertex a.P.M 1 = Cosets.vertex a.P.M 1 := by
    simpa only [Cosets.smul_vertex,mul_one,map_one,coe_one] using he x 1
  have hy (x : centralizer z) :
      (E x : G') • Cosets.vertex a'.P.M (E t : G') = Cosets.vertex a'.P.M (E t : G') ↔
      (x : G) • Cosets.vertex a.P.M (t : G) = Cosets.vertex a.P.M (t : G) := by
    simpa only [Cosets.smul_vertex,map_mul,coe_mul] using he (x*t) t
  have hxy (x : centralizer z) :
      (E x : G') • Cosets.vertex a'.P.M 1 = Cosets.vertex a'.P.M (E t : G') ↔
      (x : G) • Cosets.vertex a.P.M 1 = Cosets.vertex a.P.M (t : G) := by
    simpa only [Cosets.smul_vertex,mul_one] using he x t
  have hyx (x : centralizer z) :
      (E x : G') • Cosets.vertex a'.P.M (E t : G') = Cosets.vertex a'.P.M 1 ↔
      (x : G) • Cosets.vertex a.P.M (t : G) = Cosets.vertex a.P.M 1 := by
    simpa only [Cosets.smul_vertex,map_mul,map_one,coe_mul,coe_one] using he (x*t) 1
  constructor
  · apply subgroup_map_of_membership
    intro x
    change (_ ∧ _) ↔ (_ ∧ _)
    exact and_congr (hb x) (hy x)
  · apply subgroup_map_of_membership
    intro x
    change ((_ ∧ _) ∨ (_ ∧ _)) ↔ ((_ ∧ _) ∨ (_ ∧ _))
    exact or_congr (and_congr (hb x) (hy x)) (and_congr (hxy x) (hyx x))

/-- Construct the simultaneous plane comparison, with both central attachments,
its six-cover restriction, and every original local edge retained. -/
theorem exists_plane_flag_equiv (d : CubicNormalizerData a) (d' : CubicNormalizerData a') :
    ∃ (g : m22DesignAut)
      (φ : cubicCentralizerInH a.e a.X ≃* cubicCentralizerInH a'.e a'.X)
      (n : cubicNormalizerInH a'.e a'.X) (E : centralizer z ≃* centralizer z'),
      g • a.P.hexad = a'.P.hexad ∧ g • a.L.pair = a'.L.pair ∧
      (∀ c, cubicNativeProjection h' a'.e a'.X (φ c) = cubicNativeProjection h a.e a.X c) ∧
      E planeMarker = planeMarker ∧
      (∀ c : cubicCentralizerInH a.e a.X,
        E c.val = (cubicNormalizerAction a'.e a'.X n (φ c)).val) ∧
      (core z).map E.toMonoidHom = core z' ∧
      (cubicSylowImage a.e a.X).map E.toMonoidHom = cubicSylowImage a'.e a'.X ∧
      (cubicNormalizerInH a.e a.X).map E.toMonoidHom = cubicNormalizerInH a'.e a'.X ∧
      (∀ x, a'.designProjection (E x) = g * a.designProjection x * g⁻¹) ∧
      (a.P.M.subgroupOf (centralizer z)).map E.toMonoidHom =
        a'.P.M.subgroupOf (centralizer z') ∧
      (a.L.G₂.subgroupOf (centralizer z)).map E.toMonoidHom =
        a'.L.G₂.subgroupOf (centralizer z') ∧
      ((a.P.M ⊓ a.L.G₂).subgroupOf (centralizer z)).map E.toMonoidHom =
        (a'.P.M ⊓ a'.L.G₂).subgroupOf (centralizer z') ∧
      (∀ t : centralizer z,
        ((edgeFixer G (Cosets.vertex a.P.M 1) (Cosets.vertex a.P.M (t : G))).subgroupOf
          (centralizer z)).map E.toMonoidHom =
          (edgeFixer G' (Cosets.vertex a'.P.M 1) (Cosets.vertex a'.P.M (E t : G'))).subgroupOf
            (centralizer z') ∧
        ((edgeStabilizer G (Cosets.vertex a.P.M 1) (Cosets.vertex a.P.M (t : G))).subgroupOf
          (centralizer z)).map E.toMonoidHom =
          (edgeStabilizer G' (Cosets.vertex a'.P.M 1) (Cosets.vertex a'.P.M (E t : G'))).subgroupOf
            (centralizer z')) := by
  obtain ⟨φ,E₀,hφ,hz,hc,_,hA,hN⟩ := exists_plane_equiv_marked h a.e a.X h' a'.e a'.X
    d.perfect d'.perfect ⟨d.s,d.s_mem⟩ (Subtype.ext d.s_sq) d.s_not_mem
    ⟨d'.s,d'.s_mem⟩ (Subtype.ext d'.s_sq) d'.s_not_mem
  obtain ⟨n,g,hgP,hgL,he⟩ := exists_plane_flag_correction a a' E₀
  let E := E₀.trans (MulAut.conj n.val)
  have hEz : E planeMarker = planeMarker := by
    change n.val * E₀ planeMarker * n.val⁻¹ = planeMarker
    rw [hz,mem_center_iff.mp planeMarker_central n.val,mul_inv_cancel_right]
  have hEc (c : cubicCentralizerInH a.e a.X) :
      E c.val = (cubicNormalizerAction a'.e a'.X n (φ c)).val := by
    change n.val * E₀ c.val * n.val⁻¹ = n.val * (φ c).val * n.val⁻¹
    rw [hc]
  have hEA : (cubicSylowImage a.e a.X).map E.toMonoidHom = cubicSylowImage a'.e a'.X := by
    change (cubicSylowImage a.e a.X).map
      ((MulAut.conj n.val).toMonoidHom.comp E₀.toMonoidHom) = _
    rw [←map_map,hA]
    exact mem_normalizer_iff_map_conj_eq.mp n.property
  have hEN : (cubicNormalizerInH a.e a.X).map E.toMonoidHom = cubicNormalizerInH a'.e a'.X := by
    change (cubicNormalizerInH a.e a.X).map
      ((MulAut.conj n.val).toMonoidHom.comp E₀.toMonoidHom) = _
    rw [←map_map,hN]
    exact mem_normalizer_iff_map_conj_eq.mp (le_normalizer n.property)
  have hf := planeEquiv_flag_images a a' E g hgP hgL he
  exact ⟨g,φ,n,E,hgP,hgL,hφ,hEz,hEc,planeEquiv_core_map h h' E,hEA,hEN,he,
    hf.1,hf.2.1,hf.2.2,planeEquiv_local_edge_images a a' E hf.1⟩

/-- Every automorphism of the plane group is an inner automorphism followed
by one preserving both members of the literal flag. -/
theorem planeAut_flag_control (E : MulAut (centralizer z)) :
    ∃ n : cubicNormalizerInH a.e a.X,
      (a.P.M.subgroupOf (centralizer z)).map (E.trans (MulAut.conj n.val)).toMonoidHom =
        a.P.M.subgroupOf (centralizer z) ∧
      (a.L.G₂.subgroupOf (centralizer z)).map (E.trans (MulAut.conj n.val)).toMonoidHom =
        a.L.G₂.subgroupOf (centralizer z) := by
  obtain ⟨n,g,hgP,hgL,he⟩ := exists_plane_flag_correction a a E
  have hh := planeEquiv_flag_images a a (E.trans (MulAut.conj n.val)) g hgP hgL he
  exact ⟨n,hh.1,hh.2.1⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
