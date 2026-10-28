module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Source

/-!
# The two selections at the start of MS93 (4.4.1)(1)

A moving seed retains an actual element of Z_a and the common neighbor of
(a,c). Its existence follows from the original noncontainment. `EdgeData`
adds the two displacement identities and the kernel centralizer identity;
these are outputs still to be proved from the opposite natural frame.

`PathPlacement` is the separate geometric selection. It retains the local
conjugator at c, its image of the first edge, an actual critical path, and
the centralizer bound for this chosen conjugate. Its existence is not
asserted here. The assembly owner must discharge both selection obligations.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1), printed pp.890--891,
from the choice of x to the selected C_(T_(a+3)) bound.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection
variable {M : Type*} [Group M] {R : Subgroup M}

/-- The actual moving element and its two-edge neighborhood. -/
structure MovingSeed (a c : Vertex R) where
  neighbor : Vertex R
  adjacent_start : Adjacent R a neighbor
  adjacent_center : Adjacent R c neighbor
  element : FreeAmalgam R
  element_mem : element ∈ Z R a
  moving : ¬ ⁅zpowers element, Q R c⁆ ≤ fixedCore R c

/-- The original noncontainment already supplies the moving seed. -/
theorem movingSeed_nonempty {a c : Vertex R}
    (hd : (cosetGraph R).dist a c = 2)
    (hn : ¬ ⁅Z R a, Q R c⁆ ≤ fixedCore R c) : Nonempty (MovingSeed a c) := by
  obtain ⟨t, hat, hct⟩ := exists_common_neighbor_of_dist_two R a c hd
  obtain ⟨x, hx, hmove⟩ := exists_moving_generator hn
  exact ⟨⟨t, hat, hct, x, hx, hmove⟩⟩

/-- The local algebra selected on p.891, before placing it on a critical path.
The producer must establish these identities, including the relative product. -/
structure EdgeData (a c : Vertex R) extends MovingSeed a c where
  displacement : ⁅zpowers element, Q R c⁆ = edgeCommutator R a neighbor
  edge_eq : edgeCommutator R a neighbor = edgeCommutator R c neighbor
  kernel_product : Q R a ⊔ Q R c =
    Q R neighbor ⊓ centralizer (edgeCommutator R a neighbor : Set (FreeAmalgam R))

/-- A geometric placement of the original edge. Only this selected conjugate
satisfies the displayed third-vertex bound. -/
structure PathPlacement (geometry : Geometry R) (a c t : Vertex R) where
  start : Vertex R
  endpoint : Vertex R
  path : CriticalPath R geometry start endpoint
  conjugator : FreeAmalgam R
  local_conjugator : conjugator ∈ stabilizer R c
  start_image : act R conjugator a = start
  center_eq : path.walk.getVert 2 = c
  first_image : act R conjugator t = path.walk.getVert 1
  centralizer_selection : Q R (path.walk.getVert 3) ⊓ centralizer
    ((edgeCommutator R a t).map (MulAut.conj conjugator⁻¹).toMonoidHom :
      Set (FreeAmalgam R)) ≤ Q R c

variable [Finite M]

/-- The moving cyclic displacement stays inside the actual initial edge. -/
theorem MovingSeed.displacement_le_edge {a c : Vertex R} (s : MovingSeed a c)
    (ha : color R a = false) :
    ⁅zpowers s.element, Q R c⁆ ≤ edgeCommutator R a s.neighbor := by
  have ht : color R s.neighbor = true := by
    have hne := adjacent_color_ne R s.adjacent_start
    cases h : color R s.neighbor <;> simp_all
  exact commutator_mono (zpowers_le.mpr s.element_mem)
    (Q_le_adjacent_h R ht s.adjacent_center)

/-- Both endpoint kernels are normal in the actual common edge kernel. -/
theorem endpoint_kernels_normal {a c t : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) (hct : Adjacent R c t) :
    Q R a ≤ Q R t ∧ Q R c ≤ Q R t ∧
      ((Q R a).subgroupOf (Q R t)).Normal ∧
      ((Q R c).subgroupOf (Q R t)).Normal := by
  have ht : color R t = true := by
    have hne := adjacent_color_ne R hat
    cases h : color R t <;> simp_all
  have hta : Q R t ≤ stabilizer R a := by
    rw [Q_h_eq_edge R ht hat]
    exact inf_le_left
  have htc : Q R t ≤ stabilizer R c := by
    rw [Q_h_eq_edge R ht hct]
    exact inf_le_left
  exact ⟨Q_le_adjacent_h R ht hat, Q_le_adjacent_h R ht hct,
    normal_subgroupOf_of_le_normalizer (hta.trans (Q_normalized R a)),
    normal_subgroupOf_of_le_normalizer (htc.trans (Q_normalized R c))⟩

/-- The join in the kernel identity is precisely the source's setwise product. -/
theorem kernel_join_eq_mul {a c t : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) (hct : Adjacent R c t) :
    (↑(Q R a ⊔ Q R c) : Set (FreeAmalgam R)) =
      (Q R a : Set (FreeAmalgam R)) * (Q R c : Set (FreeAmalgam R)) := by
  have ht : color R t = true := by
    have hne := adjacent_color_ne R hat
    cases h : color R t <;> simp_all
  have htc : Q R t ≤ stabilizer R c := by
    rw [Q_h_eq_edge R ht hct]
    exact inf_le_left
  exact coe_mul_of_left_le_normalizer_right _ _
    ((Q_le_adjacent_h R ht hat).trans (htc.trans (Q_normalized R c)))

/-- Literal-product reading of the selected kernel centralizer identity. -/
theorem EdgeData.kernel_product_set {a c : Vertex R} (s : EdgeData a c)
    (ha : color R a = false) :
    (↑(Q R s.neighbor ⊓ centralizer
      (edgeCommutator R a s.neighbor : Set (FreeAmalgam R))) : Set (FreeAmalgam R)) =
      (Q R a : Set (FreeAmalgam R)) * (Q R c : Set (FreeAmalgam R)) := by
  rw [← s.kernel_product]
  exact kernel_join_eq_mul ha s.adjacent_start s.adjacent_center

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection
