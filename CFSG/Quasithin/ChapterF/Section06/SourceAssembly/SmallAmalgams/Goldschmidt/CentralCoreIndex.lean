module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.ArcIndexBounds
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.WeissEven

/-!
# The two-core bound inside the terminal edge stabilizer

The intrinsic two-core of a vertex stabilizer lies in every incident edge
stabilizer, since these are Sylow two-subgroups. At an endpoint of the fixed
interval the involution lies outside that core: it moves the next track
vertex. The edge-to-edge index estimate bounds its core centralizer index by
`2^margin`, and reversing the track supplies the other endpoint.

This proves the two-core estimate used in Goldschmidt (6.3), p.397. The index
comparison is inside the terminal edge; a comparison with the entire vertex
stabilizer would include the initial factor three.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

theorem CubicTreeAction.vertexTwoCore_le_edge (h : CubicTreeAction F)
    {a b : RankTwo.Vertex F} (hab : (RankTwo.graph F).Adj a b) :
    (pCore 2 (RankTwo.stabilizer F b)).map (RankTwo.stabilizer F b).subtype ≤
      RankTwo.stabilizer F a ⊓ RankTwo.stabilizer F b := by
  let : ∀ i, Finite (F i) := h.finite
  let H := RankTwo.stabilizer F b
  let B := (RankTwo.stabilizer F a ⊓ RankTwo.stabilizer F b).subgroupOf H
  have hp : IsPGroup 2 B := (h.edgeStabilizer_isPGroup hab).comap_subtype
  have hi : B.index = 3 := h.edge_vertex_relIndex hab
  let P : Sylow 2 H := hp.toSylow (by rw [hi]; decide)
  have hle : pCore 2 H ≤ B := pCore_isPGroup.le_sylow_of_normal P
  rintro g ⟨x, hx, rfl⟩
  exact hle hx

theorem CubicTreeAction.centralizer_core_relIndex_le_rightMargin (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) {z : G} (d : t.CentralInterval z) :
    (centralizer ({z} : Set G)).relIndex
      ((pCore 2 (RankTwo.stabilizer F (t.vertex d.fixedRight))).map
        (RankTwo.stabilizer F (t.vertex d.fixedRight)).subtype) ≤ 2 ^ d.rightMargin := by
  have hlt := d.central_lt
  have hz := d.central (d.centralRight - 1) (by omega) (by omega)
  apply h.centralizer_relIndex_le_pow_of_edge t hz d.rightMargin
  have he : d.centralRight - 1 + (d.rightMargin : ℤ) = d.fixedRight - 1 := by
    rw [d.rightMargin_cast]
    omega
  rw [he]
  have hadj : (RankTwo.graph F).Adj (t.vertex (d.fixedRight - 1)) (t.vertex d.fixedRight) := by
    simpa only [sub_add_cancel] using t.adjacent (d.fixedRight - 1)
  have ha := h.vertexTwoCore_le_edge hadj
  simpa only [Track.edgeStabilizer, sub_add_cancel] using ha

theorem CubicTreeAction.centralInvolution_not_mem_rightCore (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) {z : G} (d : t.CentralInterval z) :
    z ∉ (pCore 2 (RankTwo.stabilizer F (t.vertex d.fixedRight))).map
      (RankTwo.stabilizer F (t.vertex d.fixedRight)).subtype := by
  intro hz
  have hle := h.vertexTwoCore_le_edge (t.adjacent d.fixedRight).symm
  have hfix : z • t.vertex (d.fixedRight + 1) = t.vertex (d.fixedRight + 1) :=
    (hle hz).1
  have hh := (d.fixed_iff _).1 hfix
  omega

theorem CubicTreeAction.centralizer_core_relIndex_le_leftMargin (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) {z : G} (d : t.CentralInterval z) :
    (centralizer ({z} : Set G)).relIndex
      ((pCore 2 (RankTwo.stabilizer F (t.vertex d.fixedLeft))).map
        (RankTwo.stabilizer F (t.vertex d.fixedLeft)).subtype) ≤ 2 ^ d.leftMargin := by
  have hb := h.centralizer_core_relIndex_le_rightMargin t.reverse d.reverse
  have hm : d.reverse.rightMargin = d.leftMargin := by
    change (-d.fixedLeft - -d.centralLeft).toNat = (d.centralLeft - d.fixedLeft).toNat
    congr 1
    omega
  rw [hm] at hb
  change (centralizer ({z} : Set G)).relIndex
    ((pCore 2 (RankTwo.stabilizer F (t.vertex (- -d.fixedLeft)))).map
      (RankTwo.stabilizer F (t.vertex (- -d.fixedLeft))).subtype) ≤ 2 ^ d.leftMargin at hb
  let P : ℤ → Prop := fun j => (centralizer ({z} : Set G)).relIndex
    ((pCore 2 (RankTwo.stabilizer F (t.vertex j))).map
      (RankTwo.stabilizer F (t.vertex j)).subtype) ≤ 2 ^ d.leftMargin
  exact (congrArg P (neg_neg d.fixedLeft)).mp hb

theorem CubicTreeAction.centralInvolution_not_mem_leftCore (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) {z : G} (d : t.CentralInterval z) :
    z ∉ (pCore 2 (RankTwo.stabilizer F (t.vertex d.fixedLeft))).map
      (RankTwo.stabilizer F (t.vertex d.fixedLeft)).subtype := by
  intro hz
  have hadj : (RankTwo.graph F).Adj (t.vertex (d.fixedLeft - 1)) (t.vertex d.fixedLeft) := by
    simpa only [sub_add_cancel] using t.adjacent (d.fixedLeft - 1)
  have hfix : z • t.vertex (d.fixedLeft - 1) = t.vertex (d.fixedLeft - 1) :=
    (h.vertexTwoCore_le_edge hadj hz).1
  have hh := (d.fixed_iff _).1 hfix
  omega

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
