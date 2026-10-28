module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.PlaneRadical
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Native.DisjointHexads
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.PlaneOrbits
/-!
# The radical action on the original plane's nonneighbors

The original plane chart transports the regular action of the literal native
hexad kernel on disjoint hexads. Since the point radical maps onto that kernel,
it is transitive on the sixteen nonneighbors and its stabilizer is exactly E∩Q,
of order 128. This gives the source supplement I = E I_u for I = M∩H.
Every ambient two-point stabilizer M∩G_u normalizes this same kernel.
Its further containment in H is not inferred here: that is the remaining
stabilizer argument needed for the global unique-plane clause.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*,
Invent. Math. 105 (1991), (5.3)(2), p.600, DOI 10.1007/BF01232280.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LocalData
open LocalGeometry LocalGeometry.LocalSubgroups SourceCycleBase GraphUniquenessSystem
open Sporadic.Mathieu
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z} (a : LocalData h)

private theorem radical_fixes_base_plane (e : a.P.E) :
    (e : G) • Cosets.vertex (centralizer z) 1 = Cosets.vertex (centralizer z) 1 := by
  rw [Cosets.smul_vertex,mul_one]
  exact (Cosets.vertex_eq_base _ _).mpr (a.radical_le_plane e.property)

private theorem radical_plane_action (e : a.P.E)
    (u v : {u : Point a.P // OnPlane a.P u (Cosets.vertex (centralizer z) 1)}) :
    (e : G) • u.val = v.val ↔
      a.radicalDesign e • (a.planePoints u).val = (a.planePoints v).val := by
  constructor
  · intro he
    exact (a.planePoints_equivariant ⟨e,a.radical_le_plane e.property⟩ _
      (a.designProjection_marking _).symm u v he).symm
  · intro he
    let w : {u : Point a.P // OnPlane a.P u (Cosets.vertex (centralizer z) 1)} :=
      ⟨(e : G) • u.val,by
        have hh := incident_smul (e : G) u.property
        rwa [a.radical_fixes_base_plane e] at hh⟩
    have hw : (a.planePoints w).val = a.radicalDesign e • (a.planePoints u).val :=
      a.planePoints_equivariant ⟨e,a.radical_le_plane e.property⟩ _
        (a.designProjection_marking _).symm u w rfl
    exact congrArg Subtype.val (a.planePoints.injective (Subtype.ext (hw.trans he)))

private theorem nonneighbor_hexad (u : Point a.P)
    (hu : OnPlane a.P u (Cosets.vertex (centralizer z) 1))
    (hne : u ≠ Cosets.vertex a.P.M 1) (hn : ¬ Adj a.L (Cosets.vertex a.P.M 1) u) :
    ((a.planePoints ⟨u,hu⟩).val ∩ a.P.hexad).card=0 := by
  have hh := (a.plane_nonneighbor_iff ⟨_,⟨1,rfl,rfl⟩⟩ ⟨u,hu⟩).mp ⟨hne,hn⟩
  have hb := a.planePoints_apply ⟨Cosets.vertex a.P.M 1,⟨1,rfl,rfl⟩⟩ 1 rfl
  simp only [map_one,one_smul] at hb
  rw [hb] at hh
  exact hh

/-- The original point radical is transitive on the sixteen nonneighbors in
its original plane, through the same cubic projection. -/
theorem radical_nonneighbor_transitive (u v : Point a.P)
    (hu : OnPlane a.P u (Cosets.vertex (centralizer z) 1))
    (hv : OnPlane a.P v (Cosets.vertex (centralizer z) 1))
    (hux : u ≠ Cosets.vertex a.P.M 1) (hvx : v ≠ Cosets.vertex a.P.M 1)
    (hnu : ¬ Adj a.L (Cosets.vertex a.P.M 1) u)
    (hnv : ¬ Adj a.L (Cosets.vertex a.P.M 1) v) :
    ∃ e : a.P.E, (e : G) • u = v := by
  let A : Hexad := ⟨a.P.hexad,a.P.hexad_mem⟩
  let B := a.planePoints ⟨u,hu⟩
  let C := a.planePoints ⟨v,hv⟩
  obtain ⟨g,hg⟩ := (NativeHexads.kernel_disjoint_regular A B
    (a.nonneighbor_hexad u hu hux hnu)).surjective
      ⟨C,a.nonneighbor_hexad v hv hvx hnv⟩
  have him : M22ValueBound.Concrete.inclusion g.val ∈ a.radicalDesign.range := by
    rw [a.radicalDesign_range_eq]
    exact ⟨g.val,g.property,rfl⟩
  obtain ⟨e,he⟩ := him
  refine ⟨e,(a.radical_plane_action e ⟨u,hu⟩ ⟨v,hv⟩).mpr ?_⟩
  rw [he]
  exact congrArg (fun D => D.val.val) hg

/-- On the nonneighbor orbit the literal stabilizer in E is exactly E ∩ Q,
not the intersection with the other point radical. -/
theorem radical_nonneighbor_fixes_iff (u : Point a.P)
    (hu : OnPlane a.P u (Cosets.vertex (centralizer z) 1))
    (hne : u ≠ Cosets.vertex a.P.M 1) (hn : ¬ Adj a.L (Cosets.vertex a.P.M 1) u)
    (e : a.P.E) : (e : G) • u = u ↔ (e : G) ∈ ambientCore z := by
  rw [a.radical_plane_action e ⟨u,hu⟩ ⟨u,hu⟩]
  have hker : a.radicalDesign e = 1 ↔ (e : G) ∈ ambientCore z := by
    change e ∈ a.radicalDesign.ker ↔ _
    rw [a.radicalDesign_ker]
    rfl
  constructor
  · intro he
    apply hker.mp
    have him : a.radicalDesign e ∈ (m22HexadPointwiseKernel a.P.hexad).map
        M22ValueBound.Concrete.inclusion := a.radicalDesign_range_eq ▸ ⟨e,rfl⟩
    obtain ⟨g,hg,hge⟩ := him
    have hg1 := NativeHexads.kernel_disjoint_fixer ⟨a.P.hexad,a.P.hexad_mem⟩
      (a.planePoints ⟨u,hu⟩) (a.nonneighbor_hexad u hu hne hn) ⟨g,hg⟩
      (by rw [←hge] at he; exact he)
    have hg1' : g=1 := congrArg Subtype.val hg1
    rw [←hge,hg1',map_one]
  · intro he
    rw [hker.mpr he,one_smul]

theorem radical_nonneighbor_stabilizer (u : Point a.P)
    (hu : OnPlane a.P u (Cosets.vertex (centralizer z) 1))
    (hne : u ≠ Cosets.vertex a.P.M 1) (hn : ¬ Adj a.L (Cosets.vertex a.P.M 1) u) :
    (MulAction.stabilizer G u).subgroupOf a.P.E = (ambientCore z).subgroupOf a.P.E := by
  ext e
  exact a.radical_nonneighbor_fixes_iff u hu hne hn e

theorem radical_nonneighbor_stabilizer_card (u : Point a.P)
    (hu : OnPlane a.P u (Cosets.vertex (centralizer z) 1))
    (hne : u ≠ Cosets.vertex a.P.M 1) (hn : ¬ Adj a.L (Cosets.vertex a.P.M 1) u) :
    Nat.card ((MulAction.stabilizer G u).subgroupOf a.P.E) = 128 := by
  rw [a.radical_nonneighbor_stabilizer u hu hne hn,←a.radicalDesign_ker]
  exact a.radicalDesign_ker_card

/-- The binary kernel of dimension seven inside the ambient plane core. -/
theorem radical_core_card : Nat.card (a.P.E ⊓ ambientCore z : Subgroup G) = 128 := by
  rw [inf_comm,←subgroupOf_map_subtype,card_map_of_injective a.P.E.subtype_injective,
    ←a.radicalDesign_ker]
  exact a.radicalDesign_ker_card

/-- The overlap is supplemented by the radical and the stabilizer of a
nonneighbor, as required in the source's two-point stabilizer argument. -/
theorem nonneighbor_overlap_supplement (u : Point a.P)
    (hu : OnPlane a.P u (Cosets.vertex (centralizer z) 1))
    (hne : u ≠ Cosets.vertex a.P.M 1) (hn : ¬ Adj a.L (Cosets.vertex a.P.M 1) u)
    (m : G) (hm : m ∈ a.P.M ⊓ centralizer z) :
    ∃ e : a.P.E, ∃ k ∈ a.P.M ⊓ centralizer z ⊓ MulAction.stabilizer G u,
      m = (e : G)*k := by
  have hmx : m • Cosets.vertex a.P.M 1 = Cosets.vertex a.P.M 1 := by
    rw [Cosets.smul_vertex,mul_one]
    exact (Cosets.vertex_eq_base _ _).mpr hm.1
  have hmπ : m • Cosets.vertex (centralizer z) 1 = Cosets.vertex (centralizer z) 1 := by
    rw [Cosets.smul_vertex,mul_one]
    exact (Cosets.vertex_eq_base _ _).mpr hm.2
  have hmu : OnPlane a.P (m • u) (Cosets.vertex (centralizer z) 1) := by
    have hh := incident_smul m hu
    rwa [hmπ] at hh
  have hmune : m • u ≠ Cosets.vertex a.P.M 1 := by
    rw [←hmx]
    exact fun hh => hne (MulAction.injective m hh)
  have hmun : ¬ Adj a.L (Cosets.vertex a.P.M 1) (m • u) := by
    intro hh
    rw [←hmx] at hh
    have hh' := adj_smul m⁻¹ hh
    exact hn (by simpa only [inv_smul_smul] using hh')
  obtain ⟨e,he⟩ := a.radical_nonneighbor_transitive (m • u) u hmu hu hmune hne hmun hn
  refine ⟨e⁻¹,(e : G)*m,⟨⟨a.P.M.mul_mem (a.P.E_le e.property) hm.1,
    (centralizer z).mul_mem (a.radical_le_plane e.property) hm.2⟩,?_⟩,?_⟩
  · change ((e : G)*m) • u = u
    rwa [mul_smul]
  · simp

/-- Every ambient two-point stabilizer normalizes the same order-128 kernel.
The further source implication that it lies in H remains a separate step. -/
theorem nonneighbor_stabilizer_normalizes_kernel (u : Point a.P)
    (hu : OnPlane a.P u (Cosets.vertex (centralizer z) 1))
    (hne : u ≠ Cosets.vertex a.P.M 1) (hn : ¬ Adj a.L (Cosets.vertex a.P.M 1) u) :
    a.P.M ⊓ MulAction.stabilizer G u ≤ normalizer ((a.P.E ⊓ ambientCore z : Subgroup G) : Set G) := by
  have he : a.P.E ⊓ MulAction.stabilizer G u = a.P.E ⊓ ambientCore z := by
    have hh := congrArg (fun D : Subgroup a.P.E => D.map a.P.E.subtype)
      (a.radical_nonneighbor_stabilizer u hu hne hn)
    simpa only [subgroupOf_map_subtype,inf_comm] using hh
  rw [←he]
  intro m hm
  apply mem_normalizer_iff.mpr
  intro v
  have hmE : m ∈ normalizer (a.P.E : Set G) := a.point_normalizer.symm ▸ hm.1
  have hmu : m ∈ normalizer (MulAction.stabilizer G u : Set G) :=
    (MulAction.stabilizer G u).le_normalizer hm.2
  exact and_congr (mem_normalizer_iff.mp hmE v) (mem_normalizer_iff.mp hmu v)

end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LocalData
