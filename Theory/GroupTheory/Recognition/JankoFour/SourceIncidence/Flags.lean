module

public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Cardinalities

/-!
# Flag transitivity for the actual AS91 cosets

The original cubic pair–hexad overlaps have triple-intersection indices
15 and 5. The latter equals the degree of the line's point action, so H∩N
already reaches every point on the base line. Transporting this fact gives
one common ambient representative for each point–line–plane flag.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), opening of §5 and
(5.2)(1), pp.599–600, DOI 10.1007/BF01232280. Ambient connectedness still
requires the separate generation assertion (6.5).
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
open LocalGeometry LocalGeometry.LocalSubgroups SourceRecognition
open SourceCycleBase GraphUniquenessSystem
variable {G : Type*} [Group G] [Finite G] {z : G}

private def inclusionCosets (A B C : Subgroup G) (hCB : C ≤ B) :
    (C ⧸ A.subgroupOf C) → (B ⧸ A.subgroupOf B) :=
  Quotient.map' (inclusion hCB) (by
    intro c d hcd
    apply QuotientGroup.leftRel_apply.mpr
    have hc : ((c : C)⁻¹ * d : C) ∈ A.subgroupOf C :=
      QuotientGroup.leftRel_apply.mp hcd
    change ((c : G)⁻¹ * d : G) ∈ A at hc
    change (((inclusion hCB c : B)⁻¹ * inclusion hCB d : B) : G) ∈ A
    simpa using hc)

omit [Finite G] in
private theorem inclusionCosets_injective (A B C : Subgroup G) (hCB : C ≤ B) :
    Function.Injective (inclusionCosets A B C hCB) := by
  intro q r
  induction q using QuotientGroup.induction_on with
  | H c =>
    induction r using QuotientGroup.induction_on with
    | H d =>
      intro he
      change QuotientGroup.mk (inclusion hCB c) = QuotientGroup.mk (inclusion hCB d) at he
      apply QuotientGroup.eq.mpr
      have hc : ((inclusion hCB c : B)⁻¹ * inclusion hCB d : B) ∈ A.subgroupOf B :=
        QuotientGroup.eq.mp he
      change ((c : G)⁻¹ * d : G) ∈ A
      change (((inclusion hCB c : B)⁻¹ * inclusion hCB d : B) : G) ∈ A at hc
      simpa using hc

private theorem exists_representative_of_index (A B C : Subgroup G) (hCB : C ≤ B)
    (hindex : A.relIndex C = A.relIndex B) (b : B) :
    ∃ c : C, Cosets.vertex A c = Cosets.vertex A b := by
  have hs : Function.Surjective (inclusionCosets A B C hCB) :=
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨inclusionCosets_injective A B C hCB, hindex⟩).2
  obtain ⟨q,hq⟩ := hs (QuotientGroup.mk b)
  induction q using QuotientGroup.induction_on with
  | H c =>
    change QuotientGroup.mk (inclusion hCB c) = QuotientGroup.mk b at hq
    refine ⟨c, (Cosets.vertex_eq_iff A _ _).mpr ?_⟩
    have hc : ((inclusion hCB c : B)⁻¹ * b : B) ∈ A.subgroupOf B :=
      QuotientGroup.eq.mp hq
    change ((c : G)⁻¹ * b : G) ∈ A
    change (((inclusion hCB c : B)⁻¹ * b : B) : G) ∈ A at hc
    simpa using hc

namespace LocalData
variable {h : IsTypeJ4 z} (a : LocalData h)

/-- The two literal triple-intersection indices, from the original cubic marking. -/
theorem triple_indices :
    (a.P.M ⊓ a.L.G₂ ⊓ centralizer z).relIndex (a.P.M ⊓ centralizer z) = 15 ∧
    (a.P.M ⊓ a.L.G₂ ⊓ centralizer z).relIndex (a.L.G₂ ⊓ centralizer z) = 5 := by
  obtain ⟨hp,hl⟩ := native_design_flag_indices a.L.pair_card a.P.hexad_mem a.L.pair_le_hexad
  exact tripleIndices a.L hp hl

/-- H∩N is transitive on all five points of the original line. -/
theorem line_point_representative (x : Point a.P)
    (hx : OnLine a.L x (Cosets.vertex a.L.G₂ 1)) :
    ∃ g ∈ a.L.G₂ ⊓ centralizer z, Cosets.vertex a.P.M g = x := by
  obtain ⟨n,hn,hnN⟩ := hx
  have hnmem := (Cosets.vertex_eq_base a.L.G₂ n).mp hnN
  have hi : a.P.M.relIndex (a.L.G₂ ⊓ centralizer z) = a.P.M.relIndex a.L.G₂ := by
    have ht := a.triple_indices.2
    have he : a.P.M ⊓ a.L.G₂ ⊓ centralizer z =
        a.P.M ⊓ (a.L.G₂ ⊓ centralizer z) := by rw [inf_assoc]
    rw [he, inf_relIndex_right] at ht
    exact ht.trans a.point_line_index.symm
  obtain ⟨g,hg⟩ := exists_representative_of_index a.P.M a.L.G₂
    (a.L.G₂ ⊓ centralizer z) inf_le_left hi ⟨n,hnmem⟩
  exact ⟨g,g.property,hg.trans hn⟩

/-- A line-plane flag has a common representative with every point on that line.
This proves flag transitivity without assuming a geometry chart. -/
theorem flag_transitive (x : Point a.P) (l : Line a.L) (π : Plane z)
    (hx : OnLine a.L x l) (hπ : LineOnPlane a.L l π) :
    ∃ g : G, Cosets.vertex a.P.M g = x ∧ Cosets.vertex a.L.G₂ g = l ∧
      Cosets.vertex (centralizer z) g = π := by
  obtain ⟨g,rfl,rfl⟩ := hπ
  have hx' : OnLine a.L (g⁻¹ • x) (Cosets.vertex a.L.G₂ 1) := by
    simpa only [OnLine, Cosets.smul_vertex, inv_mul_cancel] using incident_smul g⁻¹ hx
  obtain ⟨k,hk,hkx⟩ := a.line_point_representative _ hx'
  refine ⟨g*k, ?_, ?_, ?_⟩
  · have he := congrArg (g • ·) hkx
    simpa only [Cosets.smul_vertex, smul_inv_smul] using he
  · exact (Cosets.vertex_eq_iff a.L.G₂ _ _).mpr (by simpa using a.L.G₂.inv_mem hk.1)
  · exact (Cosets.vertex_eq_iff (centralizer z) _ _).mpr
      (by simpa using (centralizer z).inv_mem hk.2)

end LocalData
end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
