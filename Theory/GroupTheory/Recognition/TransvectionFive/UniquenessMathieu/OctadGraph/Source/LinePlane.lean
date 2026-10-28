module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.Graph
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Catalogue
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceIntersections
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Intersections.Model
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceTensorProduct
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourcePlaneCoordinates
import Mathlib.Tactic.FinCases

/-!
# Source line–plane flags and vertex generation

The centralizer of A₁ ∩ A₂ lies in the marked Sylow subgroup. Weak closure
therefore identifies its full ambient normalizer with G₂ ∩ G₃. The natural
tensor action of G₂ lifts every permutation of the three line points into
this intersection. Hence G₂ = G₁₂G₂₃, giving the string condition, actual
ambient flag transitivity, and the exact incidence relation in the row residue.

The resulting edge reversal lies in the marked plane stabilizer. Distinct
row parabolics and the full three-point line action then show that its
pointwise fixer has an element outside the plane stabilizer; maximality
proves the vertex-generation identity required by the source uniqueness system.
Global generation, plane-local generation, and the source/model comparison
remain separate obligations.

The internal imports reuse the existing matrix entry calculations and hide
the six-bit tensor encodings behind proved coordinate statements. No private
name occurs in the public conclusions.

Source: Aschbacher, *Sporadic Groups* (1994), 39.1(3), 39.6(1–4), and
41.1–41.4, printed pp.213–215 and 219–222.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer PlaneTensor PlaneCensus

private theorem model_planes_centralizer_le_upper :
    Subgroup.centralizer ((Model.plane ⊓ Model.threeSpace : Subgroup SL) : Set SL) ≤ upper := by
  intro g hg
  have hr (i j : Fin 5) (hi : i.val < 2) (hj : 3 ≤ j.val) :
      root (show i < j from by omega) * g = g * root (show i < j from by omega) := by
    apply mem_centralizer_iff.mp hg
    exact ⟨subset_closure ⟨i, j, by omega, hi, by omega, rfl⟩,
      subset_closure ⟨i, j, by omega, by omega, hj, rfl⟩⟩
  have hc (i k : Fin 5) (hi : i.val < 2) :
      g k i = if k = i then g 4 4 else 0 :=
    root_commuting_column g i 4 (by omega) (hr i 4 hi (by decide)) k
  have h44 : g 4 4 = 1 := by
    have hn : g 4 4 ≠ 0 := by
      intro he
      apply g.det_ne_zero
      apply Matrix.det_eq_zero_of_column_eq_zero 0
      intro k
      simp [hc 0 k (by decide), he]
    exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hn
  have h00 : g 0 0 = 1 := by simpa [h44] using hc 0 0 (by decide)
  have hrow (i k : Fin 5) (hi : 3 ≤ i.val) :
      g i k = if i = k then 1 else 0 := by
    rw [root_commuting_row g 0 i (by omega) (hr 0 i (by decide) hi), h00]
    simp only [eq_comm]
  have htri : g.val.IsUpperTriangular := by
    intro i j hij
    change j < i at hij
    by_cases hj : j.val < 2
    · rw [hc j i hj, if_neg (ne_of_gt hij)]
    · rw [hrow i j (by omega), if_neg (ne_of_gt hij)]
  have hd (i : Fin 5) : g i i = 1 := by
    have hdet := g.property
    rw [Matrix.det_of_isUpperTriangular htri] at hdet
    have hn : g i i ≠ 0 := Finset.prod_ne_zero_iff.mp
      (show (∏ j, g j j) ≠ 0 by rw [hdet]; exact one_ne_zero) i (Finset.mem_univ i)
    exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hn
  rw [model_upper_eq_unipotent]
  exact (Theory.SpecificGroups.LinearSylowNormalizers.mem_unipotent _ _ g).mpr
    ⟨(Theory.SpecificGroups.LinearSylowNormalizers.mem_borel _ _ g).mpr htri, hd⟩

variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z)

private theorem planes_centralizer_le [Finite G] :
    Subgroup.centralizer ((F.plane ⊓ F.threeSpace : Subgroup G) : Set G) ≤
      (sourceSylow F : Subgroup G) := by
  intro g hg
  have hz : g ∈ Subgroup.centralizer ({z} : Set G) :=
    mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_iff.mp hg z ⟨point_mem_plane F, point_mem_threeSpace F⟩).symm)
  rw [sourceSylow_eq_pullback_upper]
  apply (F.mem_pullback_iff upper ⟨g, hz⟩).mpr
  apply model_planes_centralizer_le_upper
  apply mem_centralizer_iff.mpr
  intro a ha
  let aC : centralizer := ⟨a, Model.plane_le_centralizer ha.1⟩
  let b := F.equiv.symm aC
  have hb : (b : G) ∈ F.plane ⊓ F.threeSpace := by
    constructor
    · apply (F.mem_pullback_iff Model.plane b).mpr
      change (F.equiv (F.equiv.symm aC) : SL) ∈ Model.plane
      rw [F.equiv.apply_symm_apply]
      exact ha.1
    · apply (F.mem_pullback_iff Model.threeSpace b).mpr
      change (F.equiv (F.equiv.symm aC) : SL) ∈ Model.threeSpace
      rw [F.equiv.apply_symm_apply]
      exact ha.2
  have hc : b * ⟨g, hz⟩ = (⟨g, hz⟩ : Subgroup.centralizer ({z} : Set G)) * b :=
    Subtype.ext (mem_centralizer_iff.mp hg b hb)
  have he := congrArg (fun c => (F.equiv c : SL)) hc
  simpa only [map_mul, Subgroup.coe_mul, b, F.equiv.apply_symm_apply, aC] using he

/-- The stabilizer of the literal rectangle intersection preserves both
rectangles. Their weak closure is applied inside the actual source Sylow. -/
theorem planes_intersection_normalizer [Finite G] (hfusion : F.MathieuFusion) :
    normalizer ((F.plane ⊓ F.threeSpace : Subgroup G) : Set G) =
      planeNormalizer F ⊓ threeSpaceNormalizer F := by
  apply le_antisymm ?_ inf_normalizer_le_normalizer_inf
  intro g hg
  have hC := normalizer_le_normalizer_centralizer (F.plane ⊓ F.threeSpace) hg
  have hA : F.plane ≤ Subgroup.centralizer ((F.plane ⊓ F.threeSpace : Subgroup G) : Set G) := by
    intro a ha
    have hc := (plane_centralizer_eq F).symm ▸ ha
    exact mem_centralizer_iff.mpr fun b hb => mem_centralizer_iff.mp hc b hb.1
  have hB : F.threeSpace ≤ Subgroup.centralizer ((F.plane ⊓ F.threeSpace : Subgroup G) : Set G) := by
    intro a ha
    have hc := (threeSpace_centralizer_eq F).symm ▸ ha
    exact mem_centralizer_iff.mpr fun b hb => mem_centralizer_iff.mp hc b hb.2
  constructor
  · apply plane_weakly_closed F hfusion g
    rintro _ ⟨a, ha, rfl⟩
    exact planes_centralizer_le F ((mem_normalizer_iff.mp hC a).mp (hA ha))
  · apply threeSpace_weakly_closed F hfusion g
    rintro _ ⟨a, ha, rfl⟩
    exact planes_centralizer_le F ((mem_normalizer_iff.mp hC a).mp (hB ha))

/-- The marked four-dimensional intersection is the two-by-two tensor block. -/
theorem plane_element_mem_threeSpace_iff (x : Code) :
    element F x ∈ F.threeSpace ↔ ∀ i : Fin 2, decode x i 0 = 0 := by
  rw [F.mem_pullback_iff Model.threeSpace ⟨element F x, F.pullback_le _ (element_mem F x)⟩,
    element_model, plane_mem_threeSpace_iff]
  rw [modelPlaneCoordinates.apply_symm_apply]
  rfl

private theorem tensor_decomposition : ∀ x : Code, ∃ v w : Fin 3 → ZMod 2,
    tensorCode 0 v ^^^ tensorCode 1 w = x ∧
      ((∀ i : Fin 2, decode x i 0 = 0) ↔ v 0 = 0 ∧ w 0 = 0) := by decide

private theorem tensor_intersection : ∀ (i : Fin 3) (v : Fin 3 → ZMod 2),
    (∀ j : Fin 2, decode (tensorCode i v) j 0 = 0) ↔ v 0 = 0 := by decide

variable [Finite G] (D : LocalData F)

/-- A line element acting trivially on the three-dimensional tensor factor
preserves the actual marked plane, through the original rectangle intersection. -/
theorem line_tensor_scalar_mem_plane (n : planeNormalizer F)
    (hn : (planeQuotientEquiv F D.orientation.1 (QuotientGroup.mk n)).1 = 1) :
    (n : G) ∈ threeSpaceNormalizer F := by
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
            element F (tensorCode (lineAction F D n i) v) := by
        rw [← lineAction_tensor F D n, hn]
        rfl
      have he : (n : G) * a * (n : G)⁻¹ =
          element F (tensorCode (lineAction F D n 0) v) *
            element F (tensorCode (lineAction F D n 1) w) := by
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
  rw [planes_intersection_normalizer F (Or.inl D.orientation)] at hI
  exact hI.2

/-- Every permutation of the three actual line points is realized inside
the literal line–plane stabilizer G₂₃. -/
theorem exists_line_plane_permutation (p : Equiv.Perm (Fin 3)) :
    ∃ n : planeNormalizer F, (n : G) ∈ threeSpaceNormalizer F ∧ lineAction F D n = p := by
  obtain ⟨q, hq⟩ := (planeQuotientEquiv F D.orientation.1).surjective (1, p)
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨n, line_tensor_scalar_mem_plane F D n (congrArg Prod.fst hq),
    congrArg Prod.snd hq⟩

include D in
/-- The literal product G₂ = G₁₂G₂₃ in source 41.1. Both factors retain
the original ambient normalizers and the product is ordered as printed. -/
theorem line_flag_factorization (g : G) (hg : g ∈ planeNormalizer F) :
    ∃ a ∈ rowNormalizer F ⊓ planeNormalizer F,
      ∃ b ∈ planeNormalizer F ⊓ threeSpaceNormalizer F, a * b = g := by
  let n : planeNormalizer F := ⟨g, hg⟩
  obtain ⟨q, hqP, hq⟩ := exists_line_plane_permutation F D ((lineAction F D n)⁻¹)
  have hfix : lineAction F D (n * q) 0 = 0 := by
    rw [map_mul, hq, mul_inv_cancel]
    rfl
  refine ⟨(n : G) * (q : G), ⟨(lineAction_fix_iff F D (n * q)).mp hfix,
    (planeNormalizer F).mul_mem hg q.property⟩,
    (q : G)⁻¹, ⟨(planeNormalizer F).inv_mem q.property,
      (threeSpaceNormalizer F).inv_mem hqP⟩, ?_⟩
  exact mul_inv_cancel_right _ _

include D in
/-- The line's two flag stabilizers generate its full ambient stabilizer. -/
theorem line_flag_generate :
    (rowNormalizer F ⊓ planeNormalizer F) ⊔
      (planeNormalizer F ⊓ threeSpaceNormalizer F) = planeNormalizer F := by
  apply le_antisymm (sup_le inf_le_right inf_le_left)
  intro g hg
  obtain ⟨a, ha, b, hb, rfl⟩ := line_flag_factorization F D g hg
  exact Subgroup.mul_mem _ (mem_sup_left ha) (mem_sup_right hb)

open GraphUniquenessSystem GraphUniquenessSystem.Cosets

/-- Source line–plane incidence uses the literal ambient normalizers. -/
abbrev LinePlaneIncident : Line F → Plane F → Prop :=
  Incident (planeNormalizer F) (threeSpaceNormalizer F)

include D in
/-- Every point of a line is incident with every plane containing that line.
The proof produces the common representative, giving the string condition. -/
theorem flag_representative {x : Point F} {l : Line F} {p : Plane F}
    (hxl : PointLineIncident F x l) (hlp : LinePlaneIncident F l p) :
    ∃ g : G, vertex (rowNormalizer F) g = x ∧
      vertex (planeNormalizer F) g = l ∧ vertex (threeSpaceNormalizer F) g = p := by
  obtain ⟨a, hax, hal⟩ := hxl
  obtain ⟨b, hbl, hbp⟩ := hlp
  have hab : a⁻¹ * b ∈ planeNormalizer F :=
    (vertex_eq_iff _ _ _).mp (hal.trans hbl.symm)
  obtain ⟨c, hc, d, hd, he⟩ := line_flag_factorization F D (a⁻¹ * b) hab
  have hb : b = a * c * d := by rw [mul_assoc, he, mul_inv_cancel_left]
  refine ⟨a * c, ?_, ?_, ?_⟩
  · exact ((vertex_eq_iff _ _ _).mpr (by simpa using (rowNormalizer F).inv_mem hc.1)).trans hax
  · exact ((vertex_eq_iff _ _ _).mpr (by simpa using (planeNormalizer F).inv_mem hc.2)).trans hal
  · apply Eq.trans ?_ hbp
    apply (vertex_eq_iff _ _ _).mpr
    rw [hb]
    rw [inv_mul_cancel_left]
    exact hd.2

include D in
/-- The global ambient flag-transitivity assertion, now for the literal
coset incidence relation rather than only the previously identified row orbit. -/
theorem flag_transitive {x : Point F} {l : Line F} {p : Plane F}
    (hxl : PointLineIncident F x l) (hlp : LinePlaneIncident F l p) :
    ∃ g : G, g • vertex (rowNormalizer F) 1 = x ∧
      g • vertex (planeNormalizer F) 1 = l ∧ g • vertex (threeSpaceNormalizer F) 1 = p := by
  obtain ⟨g, hx, hl, hp⟩ := flag_representative F D hxl hlp
  exact ⟨g, by simpa using hx, by simpa using hl, by simpa using hp⟩

include D in
/-- The local residue flags are exactly the actual incident line–plane pairs. -/
theorem residue_incidence_iff
    (p : {p : Plane F // PointPlaneIncident F (vertex (rowNormalizer F) 1) p})
    (l : {l : Line F // PointLineIncident F (vertex (rowNormalizer F) 1) l}) :
    LinePlaneIncident F l.val p.val ↔
      (planeResidueEquiv F D p).val ≤ (lineResidueEquiv F D l).val := by
  rw [← row_residue_flag_iff F D p l]
  constructor
  · intro h
    obtain ⟨g, hg, hl, hp⟩ := flag_representative F D l.property h
    exact ⟨⟨g, (vertex_eq_base _ _).mp hg⟩, hp, hl⟩
  · rintro ⟨g, hp, hl⟩
    exact ⟨g, hl, hp⟩

include D in
/-- The three normalizers in the source generation argument are already
generated by the point and plane stabilizers. Global generation is still required. -/
theorem normalizer_span_eq :
    (rowNormalizer F ⊔ planeNormalizer F) ⊔ threeSpaceNormalizer F =
      rowNormalizer F ⊔ threeSpaceNormalizer F := by
  apply le_antisymm ?_ (sup_le (le_sup_of_le_left le_sup_left) le_sup_right)
  apply sup_le (sup_le le_sup_left ?_) le_sup_right
  intro g hg
  obtain ⟨a, ha, b, hb, rfl⟩ := line_flag_factorization F D g hg
  exact Subgroup.mul_mem _ (mem_sup_left ha.1) (mem_sup_right hb.2)

/-- A chosen edge reversal lying in both the actual line and plane stabilizers. -/
def planeSwap : planeNormalizer F :=
  Classical.choose (exists_line_plane_permutation F D (Equiv.swap 0 1))

theorem planeSwap_mem : (planeSwap F D : G) ∈ threeSpaceNormalizer F :=
  (Classical.choose_spec (exists_line_plane_permutation F D (Equiv.swap 0 1))).1

theorem planeSwap_action : lineAction F D (planeSwap F D) = Equiv.swap 0 1 :=
  (Classical.choose_spec (exists_line_plane_permutation F D (Equiv.swap 0 1))).2

/-- The chosen plane edge has exactly the already identified second line point. -/
theorem planeSwap_vertex : vertex (rowNormalizer F) (planeSwap F D : G) =
    vertex (rowNormalizer F) (lineSwap F D : G) := by
  apply (lineAction_eq_iff F D _ _).mp
  rw [planeSwap_action, lineSwap_action]

theorem planeSwap_not_row : (planeSwap F D : G) ∉ rowNormalizer F := by
  intro h
  have h0 := (lineAction_fix_iff F D _).mpr h
  rw [planeSwap_action] at h0
  simp at h0

theorem planeSwap_square_mem : (planeSwap F D : G) * (planeSwap F D : G) ∈ rowNormalizer F := by
  change ((planeSwap F D * planeSwap F D : planeNormalizer F) : G) ∈ rowNormalizer F
  apply (lineAction_fix_iff F D _).mp
  rw [map_mul, planeSwap_action]
  simp

omit [Finite G] in
include D in
private theorem line_not_le_plane : ¬ planeNormalizer F ≤ threeSpaceNormalizer F := by
  intro h
  have hh : (planeNormalizer F).subgroupOf (rowNormalizer F) ≤
      (threeSpaceNormalizer F).subgroupOf (rowNormalizer F) := fun _ ha => h ha
  rcases (line_flag_maximal F D).le_iff.mp hh with he | he
  · exact (plane_flag_maximal F D).ne_top he
  · exact line_plane_flag_ne F D he.symm

/-- The actual pointwise edge fixer has an element outside the marked plane
stabilizer. The proof uses the full line action and the distinct row parabolics. -/
theorem edgeFixer_not_le_plane :
    ¬ edgeFixer G (vertex (rowNormalizer F) 1)
      (vertex (rowNormalizer F) (planeSwap F D : G)) ≤ threeSpaceNormalizer F := by
  rw [planeSwap_vertex]
  intro h
  apply line_not_le_plane F D
  intro g hg
  let n : planeNormalizer F := ⟨g, hg⟩
  obtain ⟨q, hqP, hq⟩ := exists_line_plane_permutation F D (lineAction F D n)
  have hker : lineAction F D (n * q⁻¹) = 1 := by
    rw [map_mul, map_inv, hq, mul_inv_cancel]
  have hedge := (line_edgeFixer_iff F D (n * q⁻¹)).mpr hker
  have hh := (threeSpaceNormalizer F).mul_mem (h hedge) hqP
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right, n] using hh

/-- The vertex-generation identity of the actual source uniqueness system. -/
theorem vertex_generate :
    edgeFixer G (vertex (rowNormalizer F) 1)
      (vertex (rowNormalizer F) (planeSwap F D : G)) ⊔
        (threeSpaceNormalizer F ⊓ MulAction.stabilizer G (vertex (rowNormalizer F) 1)) =
      MulAction.stabilizer G (vertex (rowNormalizer F) 1) := by
  rw [stabilizer_base]
  let B := edgeFixer G (vertex (rowNormalizer F) 1)
    (vertex (rowNormalizer F) (planeSwap F D : G))
  have hB : B ≤ rowNormalizer F := by
    change MulAction.stabilizer G _ ⊓ MulAction.stabilizer G _ ≤ _
    rw [stabilizer_base]
    exact inf_le_left
  have hmax := plane_flag_maximal F D
  have hle : B ⊔ (threeSpaceNormalizer F ⊓ rowNormalizer F) ≤ rowNormalizer F :=
    sup_le hB inf_le_right
  have hi : (threeSpaceNormalizer F).subgroupOf (rowNormalizer F) ≤
      (B ⊔ (threeSpaceNormalizer F ⊓ rowNormalizer F)).subgroupOf (rowNormalizer F) :=
    fun a ha => mem_sup_right ⟨ha, a.property⟩
  have htop : (B ⊔ (threeSpaceNormalizer F ⊓ rowNormalizer F)).subgroupOf (rowNormalizer F) = ⊤ := by
    apply (hmax.ne_iff_eq_top hi).mp
    intro he
    apply edgeFixer_not_le_plane F D
    intro b hb
    have hm : (⟨b, hB hb⟩ : rowNormalizer F) ∈
        (B ⊔ (threeSpaceNormalizer F ⊓ rowNormalizer F)).subgroupOf (rowNormalizer F) := mem_sup_left hb
    rw [he] at hm
    exact hm
  apply le_antisymm hle
  intro a ha
  have hm : (⟨a, ha⟩ : rowNormalizer F) ∈
      (B ⊔ (threeSpaceNormalizer F ⊓ rowNormalizer F)).subgroupOf (rowNormalizer F) := by
    rw [htop]; trivial
  exact hm

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
