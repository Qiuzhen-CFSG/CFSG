module

public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Flags
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Input
public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups.LocalClassification.NativeOrders

/-!
# The literal hexad–pair chart of an AS91 plane

The original cubic projection is transported through the proved natural
Aut(M₂₂) marking. Its two specified inverse-image stabilizers identify
incident ambient point cosets with hexads and line cosets with pairs.
Flag transitivity and native pair–hexad conjugacy prove both directions
of incidence. Both bijections remain equivariant for that same projection
and send the original flag to its specified hexad and pair.

This constructs the unchanged `SourceCycleBase.PlaneChart` field; it does
not assert ambient uniqueness of a plane through a nonadjacent point pair.
Source: Aschbacher–Segev, Invent. Math. 105 (1991), §§4–5, especially
(5.2)–(5.3), pp.599–600, DOI 10.1007/BF01232280.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
open LocalGeometry LocalGeometry.LocalSubgroups SourceCycleBase GraphUniquenessSystem
variable {G : Type*} [Group G] [Finite G] {z : G}

section Chart
variable (A B : Subgroup G) {β : Type*} (q : A → β)
  (heq : ∀ m n : A, q m = q n ↔ (m : G)⁻¹ * n ∈ B)
  (hs : Function.Surjective q)

private def quotientChart : (A ⧸ B.subgroupOf A) → β :=
  Quotient.lift q (by
    intro m n hmn
    have hh : (m⁻¹ * n : A) ∈ B.subgroupOf A := QuotientGroup.leftRel_apply.mp hmn
    exact (heq m n).mpr hh)

include hs in
omit [Finite G] in
private theorem quotientChart_bijective : Function.Bijective (quotientChart A B q heq) := by
  constructor
  · intro m n
    induction m using QuotientGroup.induction_on with
    | H m =>
      induction n using QuotientGroup.induction_on with
      | H n =>
        intro hmn
        exact QuotientGroup.eq.mpr ((heq m n).mp hmn)
  · intro b
    obtain ⟨m,rfl⟩ := hs b
    exact ⟨QuotientGroup.mk m,rfl⟩

private noncomputable def cosetChart : Cosets.Residue A B ≃ β :=
  (Cosets.residueEquiv A B).symm.trans
    (Equiv.ofBijective (quotientChart A B q heq) (quotientChart_bijective A B q heq hs))

omit [Finite G] in
private theorem cosetChart_apply (r : Cosets.Residue A B) (m : A)
    (hm : Cosets.vertex B m = r.val) : cosetChart A B q heq hs r = q m := by
  have hr : Cosets.residueEquiv A B (QuotientGroup.mk m) = r := Subtype.ext (by simpa only [Cosets.residueEquiv_mk] using hm)
  rw [←hr]
  simp only [cosetChart,Equiv.trans_apply,Equiv.symm_apply_apply]
  rfl
end Chart

open Sporadic.Mathieu
open Sporadic.Mathieu.M22ValueBound.Concrete

namespace LocalData
variable {h : IsTypeJ4 z} (a : LocalData h)

noncomputable def designProjection : centralizer z →* m22DesignAut :=
  (MulEquiv.ofBijective m22DesignAutToAut
    ⟨m22DesignAutToAut_injective,m22DesignAutToAut_surjective⟩).symm.toMonoidHom.comp
      (CubicLift.projection a.P.cubic)

theorem designProjection_marking (g : centralizer z) :
    m22DesignAutToAut (a.designProjection g) = CubicLift.projection a.P.cubic g := by
  exact (MulEquiv.ofBijective m22DesignAutToAut
    ⟨m22DesignAutToAut_injective,m22DesignAutToAut_surjective⟩).apply_symm_apply _

theorem designProjection_surjective : Function.Surjective a.designProjection := by
  intro g
  obtain ⟨n,hn⟩ := CubicLift.projection_surjective a.P.cubic (m22DesignAutToAut g)
  exact ⟨n,m22DesignAutToAut_injective ((a.designProjection_marking n).trans hn)⟩

private theorem design_mem_iff (B : Finset (Fin 22)) (n : centralizer z) :
    CubicLift.projection a.P.cubic n ∈ designStabilizer B ↔
      a.designProjection n • B = B := by
  rw [←a.designProjection_marking,designStabilizer,
    mem_map_iff_mem m22DesignAutToAut_injective]
  rfl

theorem point_plane_overlap (n : centralizer z) :
    (n : G) ∈ a.P.M ↔ a.designProjection n • a.P.hexad = a.P.hexad := by
  change n ∈ a.P.M.subgroupOf (centralizer z) ↔ _
  rw [a.P.overlap]
  exact a.design_mem_iff _ _

theorem line_plane_overlap (n : centralizer z) :
    (n : G) ∈ a.L.G₂ ↔ a.designProjection n • a.L.pair = a.L.pair := by
  change n ∈ a.L.G₂.subgroupOf (centralizer z) ↔ _
  rw [a.L.plane_overlap]
  exact a.design_mem_iff _ _

private theorem design_block (g : m22DesignAut) (B : Finset (Fin 22))
    (hB : B ∈ m22Blocks) : g • B ∈ m22Blocks := by
  have hg : (g : Equiv.Perm (Fin 22)) ∈ m22DesignAut := g.property
  change (g : Equiv.Perm (Fin 22)) ∈ m22WittDesign.aut at hg
  rw [Theory.GroupTheory.SteinerSystem.mem_aut_iff] at hg
  have hB' : B ∈ (m22WittDesign.blocks : Set (Finset (Fin 22))) := by
    simpa [m22WittDesign] using hB
  have hh := Set.smul_mem_smul_set (a := g.val) hB'
  rw [hg] at hh
  change (g : Equiv.Perm (Fin 22)) • B ∈ m22Blocks
  simpa [m22WittDesign] using hh

private noncomputable def hexadOrbit (g : centralizer z) : Hexad :=
  ⟨a.designProjection g • a.P.hexad,design_block _ _ a.P.hexad_mem⟩

private noncomputable def pairOrbit (g : centralizer z) : Pair :=
  ⟨a.designProjection g • a.L.pair,by simpa using a.L.pair_card⟩

private theorem action_eq_iff {A B : Type*} [Group A] [Group B] {C : Type*}
    [MulAction B C] (f : A →* B) (c : C) (m n : A) :
    f m • c = f n • c ↔ f (m⁻¹*n) • c = c := by
  rw [map_mul,map_inv,mul_smul,inv_smul_eq_iff]
  exact eq_comm

private theorem hexadOrbit_eq (m n : centralizer z) :
    a.hexadOrbit m = a.hexadOrbit n ↔ (m : G)⁻¹ * n ∈ a.P.M := by
  rw [Subtype.ext_iff]
  change a.designProjection m • a.P.hexad = a.designProjection n • a.P.hexad ↔ _
  rw [action_eq_iff,←a.point_plane_overlap]
  rfl

private theorem pairOrbit_eq (m n : centralizer z) :
    a.pairOrbit m = a.pairOrbit n ↔ (m : G)⁻¹ * n ∈ a.L.G₂ := by
  rw [Subtype.ext_iff]
  change a.designProjection m • a.L.pair = a.designProjection n • a.L.pair ↔ _
  rw [action_eq_iff,←a.line_plane_overlap]
  rfl

private theorem hexadOrbit_surjective : Function.Surjective a.hexadOrbit := by
  intro B
  obtain ⟨g,hg⟩ := exists_smul_m22Hexad123_eq a.P.hexad_mem
  obtain ⟨k,hk⟩ := exists_smul_m22Hexad123_eq B.property
  obtain ⟨n,hn⟩ := a.designProjection_surjective (inclusion (k*g⁻¹))
  refine ⟨n,Subtype.ext ?_⟩
  change a.designProjection n • a.P.hexad = B.val
  rw [hn]
  change (k*g⁻¹) • a.P.hexad = B.val
  rw [←hg,mul_smul,inv_smul_smul,hk]

private theorem pairOrbit_surjective : Function.Surjective a.pairOrbit := by
  intro B
  obtain ⟨g,hg⟩ := M22SolvableSylow.LocalClassification.exists_smul_pair_eq_standard a.L.pair_card
  obtain ⟨k,hk⟩ := M22SolvableSylow.LocalClassification.exists_smul_pair_eq_standard B.property
  obtain ⟨n,hn⟩ := a.designProjection_surjective (inclusion (k⁻¹*g))
  refine ⟨n,Subtype.ext ?_⟩
  change a.designProjection n • a.L.pair = B.val
  rw [hn]
  change (k⁻¹*g) • a.L.pair = B.val
  rw [mul_smul,hg,←hk,inv_smul_smul]

/-- The original plane's points are the actual native hexads. -/
noncomputable def planePoints :
    {x : Point a.P // OnPlane a.P x (Cosets.vertex (centralizer z) 1)} ≃ Hexad :=
  (show {x : Point a.P // OnPlane a.P x (Cosets.vertex (centralizer z) 1)} ≃
      Cosets.Residue (centralizer z) a.P.M from
    { toFun x := ⟨x.val,by obtain ⟨g,hg,hg'⟩ := x.property; exact ⟨g,hg',hg⟩⟩
      invFun x := ⟨x.val,by obtain ⟨g,hg,hg'⟩ := x.property; exact ⟨g,hg',hg⟩⟩
      left_inv _ := rfl
      right_inv _ := rfl }).trans
    (cosetChart (centralizer z) a.P.M a.hexadOrbit a.hexadOrbit_eq a.hexadOrbit_surjective)

/-- The original plane's lines are the actual native pairs. -/
noncomputable def planeLines :
    {l : Line a.L // LineOnPlane a.L l (Cosets.vertex (centralizer z) 1)} ≃ Pair :=
  (show {l : Line a.L // LineOnPlane a.L l (Cosets.vertex (centralizer z) 1)} ≃
      Cosets.Residue (centralizer z) a.L.G₂ from
    { toFun x := ⟨x.val,by obtain ⟨g,hg,hg'⟩ := x.property; exact ⟨g,hg',hg⟩⟩
      invFun x := ⟨x.val,by obtain ⟨g,hg,hg'⟩ := x.property; exact ⟨g,hg',hg⟩⟩
      left_inv _ := rfl
      right_inv _ := rfl }).trans
    (cosetChart (centralizer z) a.L.G₂ a.pairOrbit a.pairOrbit_eq a.pairOrbit_surjective)

theorem planePoints_apply (x) (g : centralizer z) (hg : Cosets.vertex a.P.M g = x.val) :
    (a.planePoints x).val = a.designProjection g • a.P.hexad := by
  exact congrArg Subtype.val (cosetChart_apply (centralizer z) a.P.M a.hexadOrbit a.hexadOrbit_eq a.hexadOrbit_surjective _ g hg)

theorem planeLines_apply (l) (g : centralizer z) (hg : Cosets.vertex a.L.G₂ g = l.val) :
    (a.planeLines l).val = a.designProjection g • a.L.pair := by
  exact congrArg Subtype.val (cosetChart_apply (centralizer z) a.L.G₂ a.pairOrbit a.pairOrbit_eq a.pairOrbit_surjective _ g hg)


/-- The plane chart preserves the actual ambient incidence relation. -/
theorem plane_incidence (x) (l) :
    OnLine a.L x.val l.val ↔ (a.planeLines l).val ⊆ (a.planePoints x).val := by
  constructor
  · intro hxl
    obtain ⟨g,hgx,hgl,hgπ⟩ := a.flag_transitive x.val l.val _ hxl l.property
    let n : centralizer z := ⟨g,(Cosets.vertex_eq_base _ _).mp hgπ⟩
    rw [a.planePoints_apply x n hgx,a.planeLines_apply l n hgl]
    exact Finset.smul_finset_subset_smul_finset a.L.pair_le_hexad
  · intro hxl
    obtain ⟨g,hgp,hgb⟩ := m22_pair_hexad_flag_conjugacy
      a.L.pair_card a.P.hexad_mem a.L.pair_le_hexad
    obtain ⟨k,hkp,hkb⟩ := m22_pair_hexad_flag_conjugacy
      (a.planeLines l).property (a.planePoints x).property hxl
    obtain ⟨n,hn⟩ := a.designProjection_surjective (inclusion (k*g⁻¹))
    have hp : a.designProjection n • a.L.pair = (a.planeLines l).val := by
      rw [hn]
      change (k*g⁻¹) • a.L.pair = _
      rw [←hgp,mul_smul,inv_smul_smul,hkp]
    have hb : a.designProjection n • a.P.hexad = (a.planePoints x).val := by
      rw [hn]
      change (k*g⁻¹) • a.P.hexad = _
      rw [←hgb,mul_smul,inv_smul_smul,hkb]
    let x' : {x : Point a.P // OnPlane a.P x (Cosets.vertex (centralizer z) 1)} :=
      ⟨Cosets.vertex a.P.M n,⟨n,rfl,(Cosets.vertex_eq_base _ _).mpr n.property⟩⟩
    let l' : {l : Line a.L // LineOnPlane a.L l (Cosets.vertex (centralizer z) 1)} :=
      ⟨Cosets.vertex a.L.G₂ n,⟨n,rfl,(Cosets.vertex_eq_base _ _).mpr n.property⟩⟩
    have hx : x' = x := a.planePoints.injective (Subtype.ext (by
      rw [a.planePoints_apply x' n rfl]; exact hb))
    have hl : l' = l := a.planeLines.injective (Subtype.ext (by
      rw [a.planeLines_apply l' n rfl]; exact hp))
    exact ⟨n,congrArg Subtype.val hx,congrArg Subtype.val hl⟩

/-- A plane representative transforms under the same original cubic map. -/
theorem planePoints_equivariant (g : centralizer z) (b : m22DesignAut)
    (hb : CubicLift.projection a.P.cubic g = m22DesignAutToAut b)
    (x x') (hx : (g : G) • x.val = x'.val) :
    (a.planePoints x').val = b • (a.planePoints x).val := by
  obtain ⟨n,hn,hnH⟩ := x.property
  let n' : centralizer z := ⟨n,(Cosets.vertex_eq_base _ _).mp hnH⟩
  have hgg : a.designProjection g = b :=
    m22DesignAutToAut_injective ((a.designProjection_marking g).trans hb)
  have hx' : Cosets.vertex a.P.M (g*n') = x'.val := by
    rw [←hx,←hn]; rfl
  rw [a.planePoints_apply x' (g*n') hx',a.planePoints_apply x n' hn,
    map_mul,mul_smul,hgg]

/-- The line chart uses the same cubic map as the point chart. -/
theorem planeLines_equivariant (g : centralizer z) (b : m22DesignAut)
    (hb : CubicLift.projection a.P.cubic g = m22DesignAutToAut b)
    (l l') (hl : (g : G) • l.val = l'.val) :
    (a.planeLines l').val = b • (a.planeLines l).val := by
  obtain ⟨n,hn,hnH⟩ := l.property
  let n' : centralizer z := ⟨n,(Cosets.vertex_eq_base _ _).mp hnH⟩
  have hgg : a.designProjection g = b :=
    m22DesignAutToAut_injective ((a.designProjection_marking g).trans hb)
  have hl' : Cosets.vertex a.L.G₂ (g*n') = l'.val := by
    rw [←hl,←hn]; rfl
  rw [a.planeLines_apply l' (g*n') hl',a.planeLines_apply l n' hn,
    map_mul,mul_smul,hgg]

/-- The full unchanged Input plane chart, constructed from the literal overlaps. -/
noncomputable def planeChart : PlaneChart a.P a.L where
  points := a.planePoints
  lines := a.planeLines
  incidence := a.plane_incidence
  point_marking := by rw [a.planePoints_apply _ 1 rfl,map_one,one_smul]
  line_marking := by rw [a.planeLines_apply _ 1 rfl,map_one,one_smul]
  points_equivariant := a.planePoints_equivariant
  lines_equivariant := a.planeLines_equivariant

end LocalData

end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
