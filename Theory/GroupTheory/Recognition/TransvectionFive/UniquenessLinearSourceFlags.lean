module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceGraph
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceRowGeometry
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.LinePlane

/-!
# Local flag factorization and vertex generation in the linear source geometry

The centralizer of the intersection of the two rectangles lies in the marked
Sylow. Weak closure identifies its ambient normalizer with the line–plane
intersection. The tensor action then gives the literal factorization
G₂ = G₁₂G₂₃, common representatives for every incident source flag, and an
edge reversal in G₃. The pointwise edge fixer escapes G₃, so maximality of the
row parabolic proves the vertex-generation identity.

This supplies local geometry in Aschbacher, *Sporadic Groups* (1994),
41.1–41.4, pp.219–222, directly from the linear fusion counts. The internal
import reuses independent matrix and tensor lemmas from the shared geometry;
no Mathieu local-data record is assumed. Global generation, local generation
and the compatible source comparison remain separate obligations.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear.SourceGeometry
open PlaneTensor PlaneCensus
open UniquenessMathieu.OctadSource
  (Point Line Plane PointLineIncident PointPlaneIncident
   plane_element_mem_threeSpace_iff tensor_decomposition tensor_intersection)
variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z)

/-- The stabilizer of the literal rectangle intersection preserves both
rectangles. Their weak closure is applied inside the actual source Sylow. -/
theorem planes_intersection_normalizer [Finite G] :
    normalizer ((F.plane ⊓ F.threeSpace : Subgroup G) : Set G) =
      sourcePlaneNormalizer F ⊓ sourceThreeSpaceNormalizer F := by
  apply le_antisymm ?_ inf_normalizer_le_normalizer_inf
  intro g hg
  have hC := normalizer_le_normalizer_centralizer (F.plane ⊓ F.threeSpace) hg
  have hA : F.plane ≤ Subgroup.centralizer ((F.plane ⊓ F.threeSpace : Subgroup G) : Set G) := by
    intro a ha
    have hc := (source_plane_centralizer F).symm ▸ ha
    exact mem_centralizer_iff.mpr fun b hb => mem_centralizer_iff.mp hc b hb.1
  have hB : F.threeSpace ≤ Subgroup.centralizer ((F.plane ⊓ F.threeSpace : Subgroup G) : Set G) := by
    intro a ha
    have hc := (source_threeSpace_centralizer F).symm ▸ ha
    exact mem_centralizer_iff.mpr fun b hb => mem_centralizer_iff.mp hc b hb.2
  constructor
  · apply mem_normalizer_iff_map_conj_eq.mpr
    apply source_plane_weakly_closed F g
    rintro _ ⟨a, ha, rfl⟩
    exact UniquenessMathieu.OctadSource.planes_centralizer_le F ((mem_normalizer_iff.mp hC a).mp (hA ha))
  · apply mem_normalizer_iff_map_conj_eq.mpr
    apply source_threeSpace_weakly_closed F g
    rintro _ ⟨a, ha, rfl⟩
    exact UniquenessMathieu.OctadSource.planes_centralizer_le F ((mem_normalizer_iff.mp hC a).mp (hB ha))

variable [Finite G] (hlinear : F.LinearFusion)

/-- A line element acting trivially on the three-dimensional tensor factor
preserves the actual marked plane, through the original rectangle intersection. -/
theorem line_tensor_scalar_mem_plane (n : sourcePlaneNormalizer F)
    (hn : (linearPlaneQuotientEquiv F hlinear (QuotientGroup.mk n)).1 = 1) :
    (n : G) ∈ sourceThreeSpaceNormalizer F := by
  have hI : (n : G) ∈ normalizer ((F.plane ⊓ F.threeSpace : Subgroup G) : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨a, ha, rfl⟩
      obtain ⟨x, hx⟩ := (sourceEquiv F).surjective ⟨a, ha.1⟩
      have hxa : element F x = a := congrArg Subtype.val hx
      obtain ⟨v, w, hvw, hzero⟩ := tensor_decomposition x
      have hz := hzero.mp ((plane_element_mem_threeSpace_iff F x).mp (hxa.symm ▸ ha.2))
      have hact (i : Fin 3) (v : Fin 3 → ZMod 2) :
          (n : G) * element F (tensorCode i v) * (n : G)⁻¹ =
            element F (tensorCode (lineAction F hlinear n i) v) := by
        rw [← lineAction_tensor F hlinear n, hn]
        rfl
      have he : (n : G) * a * (n : G)⁻¹ =
          element F (tensorCode (lineAction F hlinear n 0) v) *
            element F (tensorCode (lineAction F hlinear n 1) w) := by
        rw [← hxa, ← hvw, element_xor]
        calc
          _ = ((n : G) * element F (tensorCode 0 v) * (n : G)⁻¹) *
              ((n : G) * element F (tensorCode 1 w) * (n : G)⁻¹) := by group
          _ = _ := by rw [hact, hact]
      refine ⟨(mem_normalizer_iff.mp n.property a).mp ha.1, ?_⟩
      change (n : G) * a * (n : G)⁻¹ ∈ F.threeSpace
      rw [he]
      exact F.threeSpace.mul_mem
        ((plane_element_mem_threeSpace_iff F _).mpr ((tensor_intersection _ _).mpr hz.1))
        ((plane_element_mem_threeSpace_iff F _).mpr ((tensor_intersection _ _).mpr hz.2))
    · rw [card_map_of_injective (MulAut.conj (n : G)).injective]
  rw [planes_intersection_normalizer F] at hI
  exact hI.2

/-- Every permutation of the three actual line points is realized inside
the literal line–plane stabilizer G₂₃. -/
theorem exists_line_plane_permutation (p : Equiv.Perm (Fin 3)) :
    ∃ n : sourcePlaneNormalizer F, (n : G) ∈ sourceThreeSpaceNormalizer F ∧ lineAction F hlinear n = p := by
  obtain ⟨q, hq⟩ := (linearPlaneQuotientEquiv F hlinear).surjective (1, p)
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨n, line_tensor_scalar_mem_plane F hlinear n (congrArg Prod.fst hq),
    congrArg Prod.snd hq⟩

include hlinear in
/-- The literal product G₂ = G₁₂G₂₃ in source 41.1. Both factors retain
the original ambient normalizers and the product is ordered as printed. -/
theorem line_flag_factorization (g : G) (hg : g ∈ sourcePlaneNormalizer F) :
    ∃ a ∈ rowNormalizer F ⊓ sourcePlaneNormalizer F,
      ∃ b ∈ sourcePlaneNormalizer F ⊓ sourceThreeSpaceNormalizer F, a * b = g := by
  let n : sourcePlaneNormalizer F := ⟨g, hg⟩
  obtain ⟨q, hqP, hq⟩ := exists_line_plane_permutation F hlinear ((lineAction F hlinear n)⁻¹)
  have hfix : lineAction F hlinear (n * q) 0 = 0 := by
    rw [map_mul, hq, mul_inv_cancel]
    rfl
  refine ⟨(n : G) * (q : G), ⟨(lineAction_fix_iff F hlinear (n * q)).mp hfix,
    (sourcePlaneNormalizer F).mul_mem hg q.property⟩,
    (q : G)⁻¹, ⟨(sourcePlaneNormalizer F).inv_mem q.property,
      (sourceThreeSpaceNormalizer F).inv_mem hqP⟩, ?_⟩
  exact mul_inv_cancel_right _ _

include hlinear in
/-- The line's two flag stabilizers generate its full ambient stabilizer. -/
theorem line_flag_generate :
    (rowNormalizer F ⊓ sourcePlaneNormalizer F) ⊔
      (sourcePlaneNormalizer F ⊓ sourceThreeSpaceNormalizer F) = sourcePlaneNormalizer F := by
  apply le_antisymm (sup_le inf_le_right inf_le_left)
  intro g hg
  obtain ⟨a, ha, b, hb, rfl⟩ := line_flag_factorization F hlinear g hg
  exact Subgroup.mul_mem _ (mem_sup_left ha) (mem_sup_right hb)

open GraphUniquenessSystem GraphUniquenessSystem.Cosets

/-- Source line–plane incidence uses the literal ambient normalizers. -/
abbrev LinePlaneIncident : Line F → Plane F → Prop :=
  Incident (sourcePlaneNormalizer F) (sourceThreeSpaceNormalizer F)

include hlinear in
/-- Every point of a line is incident with every plane containing that line.
The proof produces the common representative, giving the string condition. -/
theorem flag_representative {x : Point F} {l : Line F} {p : Plane F}
    (hxl : PointLineIncident F x l) (hlp : LinePlaneIncident F l p) :
    ∃ g : G, vertex (rowNormalizer F) g = x ∧
      vertex (sourcePlaneNormalizer F) g = l ∧ vertex (sourceThreeSpaceNormalizer F) g = p := by
  obtain ⟨a, hax, hal⟩ := hxl
  obtain ⟨b, hbl, hbp⟩ := hlp
  have hab : a⁻¹ * b ∈ sourcePlaneNormalizer F :=
    (vertex_eq_iff _ _ _).mp (hal.trans hbl.symm)
  obtain ⟨c, hc, d, hd, he⟩ := line_flag_factorization F hlinear (a⁻¹ * b) hab
  have hb : b = a * c * d := by rw [mul_assoc, he, mul_inv_cancel_left]
  refine ⟨a * c, ?_, ?_, ?_⟩
  · exact ((vertex_eq_iff _ _ _).mpr (by simpa using (rowNormalizer F).inv_mem hc.1)).trans hax
  · exact ((vertex_eq_iff _ _ _).mpr (by simpa using (sourcePlaneNormalizer F).inv_mem hc.2)).trans hal
  · apply Eq.trans ?_ hbp
    apply (vertex_eq_iff _ _ _).mpr
    rw [hb]
    rw [inv_mul_cancel_left]
    exact hd.2

include hlinear in
/-- The global ambient flag-transitivity assertion, now for the literal
coset incidence relation rather than only the previously identified row orbit. -/
theorem flag_transitive {x : Point F} {l : Line F} {p : Plane F}
    (hxl : PointLineIncident F x l) (hlp : LinePlaneIncident F l p) :
    ∃ g : G, g • vertex (rowNormalizer F) 1 = x ∧
      g • vertex (sourcePlaneNormalizer F) 1 = l ∧ g • vertex (sourceThreeSpaceNormalizer F) 1 = p := by
  obtain ⟨g, hx, hl, hp⟩ := flag_representative F hlinear hxl hlp
  exact ⟨g, by simpa using hx, by simpa using hl, by simpa using hp⟩

include hlinear in
/-- The three normalizers in the source generation argument are already
generated by the point and plane stabilizers. Global generation is still required. -/
theorem normalizer_span_eq :
    (rowNormalizer F ⊔ sourcePlaneNormalizer F) ⊔ sourceThreeSpaceNormalizer F =
      rowNormalizer F ⊔ sourceThreeSpaceNormalizer F := by
  apply le_antisymm ?_ (sup_le (le_sup_of_le_left le_sup_left) le_sup_right)
  apply sup_le (sup_le le_sup_left ?_) le_sup_right
  intro g hg
  obtain ⟨a, ha, b, hb, rfl⟩ := line_flag_factorization F hlinear g hg
  exact Subgroup.mul_mem _ (mem_sup_left ha.1) (mem_sup_right hb.2)

/-- A chosen edge reversal lying in both the actual line and plane stabilizers. -/
def planeSwap : sourcePlaneNormalizer F :=
  Classical.choose (exists_line_plane_permutation F hlinear (Equiv.swap 0 1))

theorem planeSwap_mem : (planeSwap F hlinear : G) ∈ sourceThreeSpaceNormalizer F :=
  (Classical.choose_spec (exists_line_plane_permutation F hlinear (Equiv.swap 0 1))).1

theorem planeSwap_action : lineAction F hlinear (planeSwap F hlinear) = Equiv.swap 0 1 :=
  (Classical.choose_spec (exists_line_plane_permutation F hlinear (Equiv.swap 0 1))).2

/-- The chosen plane edge has exactly the already identified second line point. -/
theorem planeSwap_vertex : vertex (rowNormalizer F) (planeSwap F hlinear : G) =
    vertex (rowNormalizer F) (lineSwap F hlinear : G) := by
  apply (lineAction_eq_iff F hlinear _ _).mp
  rw [planeSwap_action, lineSwap_action]

theorem planeSwap_not_row : (planeSwap F hlinear : G) ∉ rowNormalizer F := by
  intro h
  have h0 := (lineAction_fix_iff F hlinear _).mpr h
  rw [planeSwap_action] at h0
  simp at h0

theorem planeSwap_square_mem : (planeSwap F hlinear : G) * (planeSwap F hlinear : G) ∈ rowNormalizer F := by
  change ((planeSwap F hlinear * planeSwap F hlinear : sourcePlaneNormalizer F) : G) ∈ rowNormalizer F
  apply (lineAction_fix_iff F hlinear _).mp
  rw [map_mul, planeSwap_action]
  simp

include hlinear in
private theorem line_not_le_plane : ¬ sourcePlaneNormalizer F ≤ sourceThreeSpaceNormalizer F := by
  intro h
  have hh : (sourcePlaneNormalizer F).subgroupOf (rowNormalizer F) ≤
      (sourceThreeSpaceNormalizer F).subgroupOf (rowNormalizer F) := fun _ ha => h ha
  rcases (line_flag_maximal F hlinear).le_iff.mp hh with he | he
  · exact (plane_flag_maximal F hlinear).ne_top he
  · exact line_plane_flag_ne F hlinear he.symm

/-- The actual pointwise edge fixer has an element outside the marked plane
stabilizer. The proof uses the full line action and the distinct row parabolics. -/
theorem edgeFixer_not_le_plane :
    ¬ edgeFixer G (vertex (rowNormalizer F) 1)
      (vertex (rowNormalizer F) (planeSwap F hlinear : G)) ≤ sourceThreeSpaceNormalizer F := by
  rw [planeSwap_vertex]
  intro h
  apply line_not_le_plane F hlinear
  intro g hg
  let n : sourcePlaneNormalizer F := ⟨g, hg⟩
  obtain ⟨q, hqP, hq⟩ := exists_line_plane_permutation F hlinear (lineAction F hlinear n)
  have hker : lineAction F hlinear (n * q⁻¹) = 1 := by
    rw [map_mul, map_inv, hq, mul_inv_cancel]
  have hedge := (line_edgeFixer_iff F hlinear (n * q⁻¹)).mpr hker
  have hh := (sourceThreeSpaceNormalizer F).mul_mem (h hedge) hqP
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right, n] using hh

/-- The vertex-generation identity of the actual source uniqueness system. -/
theorem vertex_generate :
    edgeFixer G (vertex (rowNormalizer F) 1)
      (vertex (rowNormalizer F) (planeSwap F hlinear : G)) ⊔
        (sourceThreeSpaceNormalizer F ⊓ MulAction.stabilizer G (vertex (rowNormalizer F) 1)) =
      MulAction.stabilizer G (vertex (rowNormalizer F) 1) := by
  rw [stabilizer_base]
  let B := edgeFixer G (vertex (rowNormalizer F) 1)
    (vertex (rowNormalizer F) (planeSwap F hlinear : G))
  have hB : B ≤ rowNormalizer F := by
    change MulAction.stabilizer G _ ⊓ MulAction.stabilizer G _ ≤ _
    rw [stabilizer_base]
    exact inf_le_left
  have hmax := plane_flag_maximal F hlinear
  have hle : B ⊔ (sourceThreeSpaceNormalizer F ⊓ rowNormalizer F) ≤ rowNormalizer F :=
    sup_le hB inf_le_right
  have hi : (sourceThreeSpaceNormalizer F).subgroupOf (rowNormalizer F) ≤
      (B ⊔ (sourceThreeSpaceNormalizer F ⊓ rowNormalizer F)).subgroupOf (rowNormalizer F) :=
    fun a ha => mem_sup_right ⟨ha, a.property⟩
  have htop : (B ⊔ (sourceThreeSpaceNormalizer F ⊓ rowNormalizer F)).subgroupOf (rowNormalizer F) = ⊤ := by
    apply (hmax.ne_iff_eq_top hi).mp
    intro he
    apply edgeFixer_not_le_plane F hlinear
    intro b hb
    have hm : (⟨b, hB hb⟩ : rowNormalizer F) ∈
        (B ⊔ (sourceThreeSpaceNormalizer F ⊓ rowNormalizer F)).subgroupOf (rowNormalizer F) := mem_sup_left hb
    rw [he] at hm
    exact hm
  apply le_antisymm hle
  intro a ha
  have hm : (⟨a, ha⟩ : rowNormalizer F) ∈
      (B ⊔ (sourceThreeSpaceNormalizer F ⊓ rowNormalizer F)).subgroupOf (rowNormalizer F) := by
    rw [htop]; trivial
  exact hm

end Theory.GroupTheory.TransvectionFive.UniquenessLinear.SourceGeometry
