module
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.LocalAction
public import Theory.SpecificGroups.DihedralSolvable
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

/-!
# The edge stabilizer of the seventeen-point coset graph

An outside involution in H₂ cannot normalize H₁: otherwise the whole
group would be a solvable extension of the solvable H₁, contradicting
the actual A₅ × C₂ subgroup H₃. The index-two overlap is normalized by
the involution, and its maximality in H₁ forces the edge stabilizer to
be exactly H₁ ∩ H₂. The graph is consequently connected, faithful,
locally doubly transitive and of valency sixteen, all from the source data.

The final degree and order conclusions below still retain the cubic-word
input used to produce a triangle. Its construction from H₃, and the later
embedding-uniqueness/recognition argument, are not asserted in this file.

Source: Baumeister, *A geometry for groups of J₃-type* (2007),
Lemma 2.7, p.497.
-/

@[expose] public noncomputable section
open Subgroup MulAction
open scoped IsMulCommutative
namespace Sporadic.Janko3.SourceRecognition.Seventeen.SourceData
variable {G : Type*} [Group G] (S : SourceData G)

theorem point_solvable : Group.IsSolvable S.H1 := by
  let : Group.IsSolvable (DihedralGroup 5) := GLS3.Chapter5.dihedralGroup_isSolvable 5
  let : Group.IsSolvable (Plane ⋊[S.action] Complement) :=
    Group.isSolvable_of_ker_le_range SemidirectProduct.inl SemidirectProduct.rightHom
      (le_of_eq SemidirectProduct.range_inl_eq_ker_rightHom.symm)
  exact Group.isSolvable_of_isSolvable_injective (f := S.pointEquiv.toMonoidHom)
    S.pointEquiv.injective

include S in
theorem not_solvable : ¬ Group.IsSolvable G := by
  intro hG
  let : Group.IsSolvable G := hG
  let : Group.IsSolvable TriangleGroup :=
    Group.isSolvable_of_surjective (f := S.triangleEquiv.toMonoidHom) S.triangleEquiv.surjective
  let : Group.IsSolvable (alternatingGroup (Fin 5)) :=
    Group.isSolvable_of_surjective (f := MonoidHom.fst _ (Multiplicative (ZMod 2)))
      (fun x => ⟨(x, 1), rfl⟩)
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5)) inferInstance

theorem outside_not_normalizes (b : G) (hb : b*b=1) (hbout : b ∉ S.H1) (hb2 : b ∈ S.H2) :
    b ∉ normalizer (S.H1 : Set G) := by
  intro hnorm
  have hgen := CosetGraph.generation_of_index_two (cosetData S b hb hbout) S.H2 hb2
    (overlap_index_two S) S.generated
  have hn : normalizer (S.H1 : Set G) = ⊤ :=
    top_unique (hgen ▸ sup_le S.H1.le_normalizer (zpowers_le.mpr hnorm))
  let : S.H1.Normal := normalizer_eq_top_iff.mp hn
  let q := QuotientGroup.mk' S.H1
  have hqgen : zpowers (q b) = ⊤ := by
    have hm := congrArg (fun K : Subgroup G => K.map q) hgen
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, q.range_eq_top_of_surjective
      (QuotientGroup.mk'_surjective _)] at hm
    have hk : S.H1.map q = ⊥ := by
      apply bot_unique
      rintro _ ⟨x, hx, rfl⟩
      exact (QuotientGroup.eq_one_iff x).mpr hx
    rwa [hk, bot_sup_eq] at hm
  let : IsCyclic (G ⧸ S.H1) := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨q b, hqgen⟩
  let : Group.IsSolvable (G ⧸ S.H1) := Group.isSolvable_of_comm (fun x y => mul_comm x y)
  exact not_solvable S ((Group.isSolvable_iff_subgroup_quotient S.H1).mpr
    ⟨point_solvable S, inferInstance⟩)

theorem edge_stabilizer
    (b : G) (hb : b * b = 1) (hbout : b ∉ S.H1) (hb2 : b ∈ S.H2) :
    CosetGraph.edgeStabilizer (cosetData S b hb hbout) = S.H2.subgroupOf S.H1 := by
  let D := cosetData S b hb hbout
  let E := CosetGraph.edgeStabilizer D
  have he (x : S.H1) : x ∈ E ↔ b⁻¹ * (x : G) * b ∈ S.H1 := by
    change ((x : G) • (b : G ⧸ S.H1) = (b : G ⧸ S.H1)) ↔ _
    rw [eq_comm]
    change (((b : G) : G ⧸ S.H1) = (((x : G) * b : G) : G ⧸ S.H1)) ↔ _
    rw [QuotientGroup.eq, mul_assoc]
  have hCE : S.H2.subgroupOf S.H1 ≤ E := by
    intro x hx
    apply (he x).mpr
    let C := S.H1.subgroupOf S.H2
    let : C.Normal := normal_of_index_eq_two (overlap_index_two S)
    have hh : (⟨b, hb2⟩ : S.H2)⁻¹ * ⟨x, hx⟩ * (⟨b, hb2⟩ : S.H2) ∈ C := by
      simpa only [inv_inv] using (inferInstance : C.Normal).conj_mem
        (⟨x, hx⟩ : S.H2) x.property (⟨b, hb2⟩ : S.H2)⁻¹
    exact hh
  rcases (overlap_maximal S).le_iff.mp hCE with htop | hsame
  · exfalso
    apply outside_not_normalizes S b hb hbout hb2
    have hi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hh := (he ⟨x, hx⟩).mp (htop ▸ mem_top _)
      simpa only [hi] using hh
    · intro hx
      have hh := (he ⟨b*x*b⁻¹, hx⟩).mp (htop ▸ mem_top _)
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, inv_mul_cancel, mul_one] using hh
  · exact hsame

theorem graph_properties
    (b : G) (hb : b * b = 1) (hbout : b ∉ S.H1) (hb2 : b ∈ S.H2) :
    let D := cosetData S b hb hbout
    (CosetGraph.graph D).Connected ∧ FaithfulSMul G (CosetGraph.Vertex D) ∧
      (∀ x : CosetGraph.Vertex D, Nat.card ((CosetGraph.graph D).neighborSet x) = 16) ∧
      CosetGraph.NeighborTwoTransitive D := by
  have he := edge_stabilizer S b hb hbout hb2
  have hecard : Nat.card (CosetGraph.edgeStabilizer (cosetData S b hb hbout)) = 30 := by
    rw [he, ← inf_subgroupOf_left, Nat.card_congr (subgroupOfEquivOfLe
      (show S.H1 ⊓ S.H2 ≤ S.H1 from inf_le_left)).toEquiv]
    exact overlap_card S
  exact ⟨connected S b hb hbout hb2, faithful_of_edge S b hb hbout he,
    CosetGraph.valency_sixteen _ (point_card S) hecard,
    neighbor_two_transitive_of_edge S b hb hbout he⟩

theorem consequences_of_cube
    (b : G) (hb : b * b = 1) (hbout : b ∉ S.H1) (hb2 : b ∈ S.H2)
    (h : G) (hh : h ∈ S.H1) (hcube : (b * h)^3 ∈ S.H1) :
    let D := cosetData S b hb hbout
    FaithfulSMul G (CosetGraph.Vertex D) ∧
      (CosetGraph.graph D).Connected ∧ CosetGraph.graph D = ⊤ ∧
      (∀ x : CosetGraph.Vertex D, Nat.card ((CosetGraph.graph D).neighborSet x) = 16) ∧
      Nat.card (CosetGraph.Vertex D) = 17 ∧
      IsMultiplyPretransitive G (CosetGraph.Vertex D) 3 ∧ Nat.card G = 8160 :=
  geometric_consequences_of_edge_cube S b hb hbout hb2 (edge_stabilizer S b hb hbout hb2)
    h hh hcube

theorem exists_graph_properties :
    ∃ (b : G) (hb : b * b = 1) (hbout : b ∉ S.H1), b ∈ S.H2 ∧ b ∈ S.H3 ∧
      let D := cosetData S b hb hbout
      (CosetGraph.graph D).Connected ∧ FaithfulSMul G (CosetGraph.Vertex D) ∧
        (∀ x : CosetGraph.Vertex D, Nat.card ((CosetGraph.graph D).neighborSet x) = 16) ∧
        CosetGraph.NeighborTwoTransitive D := by
  obtain ⟨b, hb, hb2, hb3, hbout⟩ := exists_outside_involution S
  exact ⟨b, hb, hbout, hb2, hb3, graph_properties S b hb hbout hb2⟩

end Sporadic.Janko3.SourceRecognition.Seventeen.SourceData
