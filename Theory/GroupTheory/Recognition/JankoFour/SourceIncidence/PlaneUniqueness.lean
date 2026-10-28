module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.PlaneNonneighbors
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.PointChart
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Native.SextetMaximal
/-!
# Ambient uniqueness of the plane through a nonadjacent pair

The native sextet maximality pulls back to M ∩ H maximal in M. The normalizer
in M of W = E ∩ Q contains this overlap. It cannot be all of M: W has order
128 and contains z, whereas the orbit of z under M has 1771 elements. Thus
N_M(W) = M ∩ H. The already proved literal nonneighbor stabilizer in E is W,
so the ambient two-point stabilizer M ∩ G_u lies in H. Radical transitivity
then compares any other plane through the pair and proves ambient uniqueness.

The argument keeps E ∩ G_u distinct from E ∩ coreAt(u); the latter intersection
is a separate source obligation and is not asserted by this module.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (5.3)(2), p.600,
DOI 10.1007/BF01232280.
-/
public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LocalData
open LocalGeometry LocalGeometry.LocalSubgroups SourceCycleBase GraphUniquenessSystem
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z} (a : LocalData h)

theorem vertex_maximal : IsCoatom ((centralizer z).subgroupOf a.P.M) := by
  have he : (centralizer z).subgroupOf a.P.M =
      (sextetStabilizer a.sextet).comap a.P.projection := by
    ext m
    exact a.point_plane_todd_overlap m
  rw [he]
  exact isCoatom_comap_of_surjective a.projection_surjective
    (NativeSextets.sextet_maximal a.sextet)

private theorem kernel_not_normalized :
    ¬ a.P.M ≤ normalizer ((a.P.E ⊓ ambientCore z : Subgroup G) : Set G) := by
  intro hn
  let W := a.P.E ⊓ ambientCore z
  let f : Native.Plane → W := fun S =>
    ⟨marker (a.residuePlanes.symm S).val,by
      obtain ⟨m,hm,hπ⟩ := (a.residuePlanes.symm S).property
      rw [←hπ,marker_vertex]
      exact (mem_normalizer_iff.mp (hn ((Cosets.vertex_eq_base _ _).mp hm)) z).mp
        ⟨a.marker_mem_E,marker_mem_ambientCore z⟩⟩
  have hf : Function.Injective f := by
    intro S T he
    apply a.residuePlanes.symm.injective
    apply Subtype.ext
    exact marker_injective (congrArg Subtype.val he)
  have hc := Nat.card_le_card_of_injective f hf
  rw [Native.plane_card] at hc
  change 1771 ≤ Nat.card (a.P.E ⊓ ambientCore z : Subgroup G) at hc
  rw [a.radical_core_card] at hc
  omega

/-- The order-128 kernel recovers the original plane inside the point group. -/
theorem radical_core_normalizer :
    a.P.M ⊓ normalizer ((a.P.E ⊓ ambientCore z : Subgroup G) : Set G) =
      a.P.M ⊓ centralizer z := by
  let N := (normalizer ((a.P.E ⊓ ambientCore z : Subgroup G) : Set G)).subgroupOf a.P.M
  have hle : (centralizer z).subgroupOf a.P.M ≤ N := by
    intro m hm
    have hmE : (m : G) ∈ normalizer (a.P.E : Set G) := a.point_normalizer.symm ▸ m.property
    have hmQ : (m : G) ∈ normalizer (ambientCore z : Set G) := (normalizer_ambientCore h).symm ▸ hm
    exact mem_normalizer_iff.mpr fun v =>
      and_congr (mem_normalizer_iff.mp hmE v) (mem_normalizer_iff.mp hmQ v)
  have hnt : N ≠ ⊤ := by
    intro he
    apply a.kernel_not_normalized
    intro m hm
    have hh : (⟨m,hm⟩ : a.P.M) ∈ N := he ▸ mem_top _
    exact hh
  have he := (a.vertex_maximal.le_iff_eq hnt).mp hle
  have he' := congrArg (fun D : Subgroup a.P.M => D.map a.P.M.subtype) he
  simpa only [N,subgroupOf_map_subtype,inf_comm] using he'

/-- The ambient stabilizer of a nonadjacent pair in the base plane fixes that plane. -/
theorem nonneighbor_stabilizer_le_plane (u : Point a.P)
    (hu : OnPlane a.P u (Cosets.vertex (centralizer z) 1))
    (hne : u ≠ Cosets.vertex a.P.M 1) (hn : ¬ Adj a.L (Cosets.vertex a.P.M 1) u) :
    a.P.M ⊓ MulAction.stabilizer G u ≤ centralizer z := by
  intro m hm
  have hh : m ∈ a.P.M ⊓ normalizer ((a.P.E ⊓ ambientCore z : Subgroup G) : Set G) :=
    ⟨hm.1,a.nonneighbor_stabilizer_normalizes_kernel u hu hne hn hm⟩
  rw [a.radical_core_normalizer] at hh
  exact hh.2

private theorem unique_plane_base (u : Point a.P)
    (hu : OnPlane a.P u (Cosets.vertex (centralizer z) 1))
    (hne : u ≠ Cosets.vertex a.P.M 1) (hn : ¬ Adj a.L (Cosets.vertex a.P.M 1) u)
    (σ : Plane z) (hxσ : OnPlane a.P (Cosets.vertex a.P.M 1) σ)
    (huσ : OnPlane a.P u σ) : σ = Cosets.vertex (centralizer z) 1 := by
  obtain ⟨m,hm,rfl⟩ := hxσ
  have hmM := (Cosets.vertex_eq_base _ _).mp hm
  have hmx : m⁻¹ • Cosets.vertex a.P.M 1 = Cosets.vertex a.P.M 1 := by
    rw [Cosets.smul_vertex,mul_one]
    exact (Cosets.vertex_eq_base _ _).mpr (a.P.M.inv_mem hmM)
  have hmu : OnPlane a.P (m⁻¹ • u) (Cosets.vertex (centralizer z) 1) := by
    simpa only [OnPlane,Cosets.smul_vertex,inv_mul_cancel] using incident_smul m⁻¹ huσ
  have hne' : m⁻¹ • u ≠ Cosets.vertex a.P.M 1 := by
    rw [←hmx]
    exact fun he => hne (MulAction.injective m⁻¹ he)
  have hn' : ¬ Adj a.L (Cosets.vertex a.P.M 1) (m⁻¹ • u) := by
    intro hh
    rw [←hmx] at hh
    have hh' := adj_smul m hh
    exact hn (by simpa only [smul_inv_smul] using hh')
  obtain ⟨e,he⟩ := a.radical_nonneighbor_transitive u (m⁻¹ • u) hu hmu hne hne' hn hn'
  have hk : m*(e : G) ∈ a.P.M ⊓ MulAction.stabilizer G u := by
    refine ⟨a.P.M.mul_mem hmM (a.P.E_le e.property),?_⟩
    change (m*(e : G)) • u = u
    rw [mul_smul,he,smul_inv_smul]
  have hkH := a.nonneighbor_stabilizer_le_plane u hu hne hn hk
  have hmH : m ∈ centralizer z := by
    have hh := (centralizer z).mul_mem hkH ((centralizer z).inv_mem (a.radical_le_plane e.property))
    simpa only [mul_inv_cancel_right] using hh
  exact (Cosets.vertex_eq_base _ _).mpr hmH

/-- AS91 (5.3)(2): uniqueness is among all ambient planes. -/
theorem unique_plane (π : Plane z) (x y : Point a.P)
    (hx : OnPlane a.P x π) (hy : OnPlane a.P y π) (hne : x ≠ y)
    (hn : ¬ Adj a.L x y) (σ : Plane z)
    (hxσ : OnPlane a.P x σ) (hyσ : OnPlane a.P y σ) : σ = π := by
  obtain ⟨g,rfl,rfl⟩ := hx
  have hxy : g⁻¹ • Cosets.vertex a.P.M g = Cosets.vertex a.P.M 1 := by
    rw [Cosets.smul_vertex,inv_mul_cancel]
  have hgπ : g⁻¹ • Cosets.vertex (centralizer z) g = Cosets.vertex (centralizer z) 1 := by
    rw [Cosets.smul_vertex,inv_mul_cancel]
  have hy' : OnPlane a.P (g⁻¹ • y) (Cosets.vertex (centralizer z) 1) := by
    have hh := incident_smul g⁻¹ hy
    rwa [hgπ] at hh
  have hne' : g⁻¹ • y ≠ Cosets.vertex a.P.M 1 := by
    rw [←hxy]
    exact fun he => hne (MulAction.injective g⁻¹ he).symm
  have hn' : ¬ Adj a.L (Cosets.vertex a.P.M 1) (g⁻¹ • y) := by
    intro hh
    rw [←hxy] at hh
    have hh' := adj_smul g hh
    exact hn (by simpa only [smul_inv_smul] using hh')
  have hxσ' : OnPlane a.P (Cosets.vertex a.P.M 1) (g⁻¹ • σ) := by
    have hh := incident_smul g⁻¹ hxσ
    rwa [hxy] at hh
  have he := a.unique_plane_base (g⁻¹ • y) hy' hne' hn' (g⁻¹ • σ) hxσ'
    (incident_smul g⁻¹ hyσ)
  have hh := congrArg (g • ·) he
  simpa only [smul_inv_smul,Cosets.smul_vertex,mul_one] using hh
end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LocalData
