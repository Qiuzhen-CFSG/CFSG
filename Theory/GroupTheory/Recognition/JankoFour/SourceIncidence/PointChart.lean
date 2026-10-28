module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.PlaneChart
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Markers
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Native.FlagIncidence

/-!
# The original Todd point-residue chart

The two stabilizers are inverse images under one Todd projection because its
kernel E lies in both overlaps. The original cubic triple intersection gives
native index fifteen; the checked native orbit bound then forces the marked
trio and sextet to be incident. Their M₂₄ orbits identify the actual ambient
line and plane cosets, and flag transitivity proves both directions of
incidence. The resulting chart is equivariant for the original projection.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), §5, especially (5.2)(1),
pp.599–600, DOI 10.1007/BF01232280. This supplies the unchanged point-residue
field without assuming native incidence or any geometric chart.
-/

public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
open LocalGeometry LocalGeometry.LocalSubgroups SourceCycleBase GraphUniquenessSystem
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
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

namespace LocalData
variable {h : IsTypeJ4 z} (a : LocalData h)

private theorem E_le_plane : a.P.E ≤ centralizer z := by
  let := a.P.E_elementary
  intro u hu
  exact mem_centralizer_singleton_iff.mpr
    (((Commute.all (⟨u,hu⟩ : a.P.E) ⟨z,a.marker_mem_E⟩).map a.P.E.subtype).eq)

private theorem ker_le_line : a.P.projection.ker ≤ a.L.G₂.subgroupOf a.P.M := by
  rw [a.P.projection_ker]
  exact fun _ hu => a.E_le_line hu

private theorem ker_le_plane : a.P.projection.ker ≤ (centralizer z).subgroupOf a.P.M := by
  rw [a.P.projection_ker]
  exact fun _ hu => a.E_le_plane hu

/-- The marked trio is the exact inverse image under the original Todd map. -/
theorem point_line_overlap (m : a.P.M) :
    (m : G) ∈ a.L.G₂ ↔ a.P.projection m • a.trio.parts = a.trio.parts := by
  have he := comap_map_eq_self a.ker_le_line
  rw [a.line_image] at he
  change m ∈ a.L.G₂.subgroupOf a.P.M ↔ _
  rw [←he]
  rfl

/-- The marked sextet uses precisely the same Todd map. -/
theorem point_plane_todd_overlap (m : a.P.M) :
    (m : G) ∈ centralizer z ↔ a.P.projection m • a.sextet.parts = a.sextet.parts := by
  have he := comap_map_eq_self a.ker_le_plane
  rw [a.plane_image] at he
  change m ∈ (centralizer z).subgroupOf a.P.M ↔ _
  rw [←he]
  rfl

/-- The original triple intersection has native index fifteen. -/
theorem native_flag_index : (trioStabilizer a.trio).relIndex (sextetStabilizer a.sextet) = 15 := by
  rw [←a.line_image,←a.plane_image,relIndex_map_map,
    sup_of_le_left a.ker_le_line,sup_of_le_left a.ker_le_plane]
  change (a.L.G₂.comap a.P.M.subtype).relIndex ((centralizer z).subgroupOf a.P.M) = 15
  rw [relIndex_comap,subgroupOf_map_subtype]
  have ht := a.triple_indices.1
  have he : a.P.M ⊓ a.L.G₂ ⊓ centralizer z = a.L.G₂ ⊓ (a.P.M ⊓ centralizer z) := by ac_rfl
  rw [he,inf_relIndex_right] at ht
  simpa only [inf_comm] using ht

/-- Incidence of the earlier-source markings is a consequence, not an input. -/
theorem native_flag : Native.Incident a.trio a.sextet :=
  NativeFlags.incident_of_index _ _ a.native_flag_index

private noncomputable def trioOrbit (m : a.P.M) : Native.Line := a.P.projection m • a.trio
private noncomputable def sextetOrbit (m : a.P.M) : Native.Plane := a.P.projection m • a.sextet

private theorem action_eq_iff {A B : Type*} [Group A] [Group B] {C : Type*}
    [MulAction B C] (f : A →* B) (c : C) (m n : A) :
    f m • c = f n • c ↔ f (m⁻¹*n) • c = c := by
  rw [map_mul,map_inv,mul_smul,inv_smul_eq_iff]
  exact eq_comm

private theorem trioOrbit_eq (m n : a.P.M) :
    a.trioOrbit m = a.trioOrbit n ↔ (m : G)⁻¹*n ∈ a.L.G₂ := by
  rw [←Native.line_parts_injective.eq_iff]
  change a.P.projection m • a.trio.parts = a.P.projection n • a.trio.parts ↔ _
  rw [action_eq_iff,←a.point_line_overlap]
  rfl

private theorem sextetOrbit_eq (m n : a.P.M) :
    a.sextetOrbit m = a.sextetOrbit n ↔ (m : G)⁻¹*n ∈ centralizer z := by
  rw [←Native.plane_parts_injective.eq_iff]
  change a.P.projection m • a.sextet.parts = a.P.projection n • a.sextet.parts ↔ _
  rw [action_eq_iff,←a.point_plane_todd_overlap]
  rfl

private theorem trioOrbit_surjective : Function.Surjective a.trioOrbit := by
  intro l
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M24 a.trio l
  obtain ⟨m,hm⟩ := a.projection_surjective g
  exact ⟨m,by change a.P.projection m • a.trio = l; rw [hm,hg]⟩

private theorem sextetOrbit_surjective : Function.Surjective a.sextetOrbit := by
  intro π
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M24 a.sextet π
  obtain ⟨m,hm⟩ := a.projection_surjective g
  exact ⟨m,by change a.P.projection m • a.sextet = π; rw [hm,hg]⟩

/-- Lines at the actual point are the trios under its original Todd marking. -/
noncomputable def residueLines :
    {l : Line a.L // OnLine a.L (Cosets.vertex a.P.M 1) l} ≃ Native.Line :=
  cosetChart a.P.M a.L.G₂ a.trioOrbit a.trioOrbit_eq a.trioOrbit_surjective

/-- Planes at that same point are the sextets under the same Todd marking. -/
noncomputable def residuePlanes :
    {π : Plane z // OnPlane a.P (Cosets.vertex a.P.M 1) π} ≃ Native.Plane :=
  cosetChart a.P.M (centralizer z) a.sextetOrbit a.sextetOrbit_eq a.sextetOrbit_surjective

theorem residueLines_apply (l) (m : a.P.M) (hm : Cosets.vertex a.L.G₂ m = l.val) :
    (a.residueLines l).parts = a.P.projection m • a.trio.parts := by
  exact congrArg Trio.parts (cosetChart_apply a.P.M a.L.G₂ a.trioOrbit a.trioOrbit_eq a.trioOrbit_surjective l m hm)

theorem residuePlanes_apply (π) (m : a.P.M) (hm : Cosets.vertex (centralizer z) m = π.val) :
    (a.residuePlanes π).parts = a.P.projection m • a.sextet.parts := by
  exact congrArg Sextet.parts (cosetChart_apply a.P.M (centralizer z) a.sextetOrbit a.sextetOrbit_eq a.sextetOrbit_surjective π m hm)

/-- Native incidence agrees with the literal ambient line–plane incidence. -/
theorem residue_incidence (l) (π) :
    LineOnPlane a.L l.val π.val ↔ Native.Incident (a.residueLines l) (a.residuePlanes π) := by
  constructor
  · intro hlπ
    obtain ⟨g,hgx,hgl,hgπ⟩ := a.flag_transitive _ _ _ l.property hlπ
    let m : a.P.M := ⟨g,(Cosets.vertex_eq_base _ _).mp hgx⟩
    exact Native.incident_transport (a.P.projection m)
      (a.residueLines_apply l m hgl) (a.residuePlanes_apply π m hgπ) a.native_flag
  · intro hi
    obtain ⟨g,hgl,hgπ⟩ := NativeFlags.flag_transitive _ _ _ _ a.native_flag hi
    obtain ⟨m,hm⟩ := a.projection_surjective g
    let l' : {l : Line a.L // OnLine a.L (Cosets.vertex a.P.M 1) l} :=
      ⟨Cosets.vertex a.L.G₂ m,⟨m,(Cosets.vertex_eq_base _ _).mpr m.property,rfl⟩⟩
    let π' : {π : Plane z // OnPlane a.P (Cosets.vertex a.P.M 1) π} :=
      ⟨Cosets.vertex (centralizer z) m,⟨m,(Cosets.vertex_eq_base _ _).mpr m.property,rfl⟩⟩
    have hl : l' = l := a.residueLines.injective (Native.line_parts_injective (by
      rw [a.residueLines_apply l' m rfl,hm,hgl]))
    have hπ : π' = π := a.residuePlanes.injective (Native.plane_parts_injective (by
      rw [a.residuePlanes_apply π' m rfl,hm,hgπ]))
    exact ⟨m,congrArg Subtype.val hl,congrArg Subtype.val hπ⟩

theorem residueLines_equivariant (m : a.P.M) (l l') (hl : (m : G) • l.val = l'.val) :
    (a.residueLines l').parts = a.P.projection m • (a.residueLines l).parts := by
  obtain ⟨n,hnM,hn⟩ := l.property
  let n' : a.P.M := ⟨n,(Cosets.vertex_eq_base _ _).mp hnM⟩
  have hl' : Cosets.vertex a.L.G₂ (m*n') = l'.val := by rw [←hl,←hn]; rfl
  rw [a.residueLines_apply l' (m*n') hl',a.residueLines_apply l n' hn,map_mul,mul_smul]

theorem residuePlanes_equivariant (m : a.P.M) (π π') (hπ : (m : G) • π.val = π'.val) :
    (a.residuePlanes π').parts = a.P.projection m • (a.residuePlanes π).parts := by
  obtain ⟨n,hnM,hn⟩ := π.property
  let n' : a.P.M := ⟨n,(Cosets.vertex_eq_base _ _).mp hnM⟩
  have hπ' : Cosets.vertex (centralizer z) (m*n') = π'.val := by rw [←hπ,←hn]; rfl
  rw [a.residuePlanes_apply π' (m*n') hπ',a.residuePlanes_apply π n' hn,map_mul,mul_smul]

/-- The complete unchanged point-residue chart, with its literal Todd projection. -/
noncomputable def residueChart : ResidueChart a.P a.L where
  lines := a.residueLines
  planes := a.residuePlanes
  incidence := a.residue_incidence
  lines_equivariant := a.residueLines_equivariant
  planes_equivariant := a.residuePlanes_equivariant

end LocalData
end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
