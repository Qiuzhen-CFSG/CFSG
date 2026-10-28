module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.PolygonParameters.Geometry
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.SimpleCoordinates
public import Theory.GroupAction.RankTwoCosetGeometry.Valence
public import Theory.Combinatorics.SimpleGraph.OctagonShortPaths.NeighborSums

public noncomputable section
open Subgroup
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.PolygonParameters
open DihedralGeometry RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}

private def neighborQuotientMap {G : Type*} [Group G] (F : Fin 2 → Subgroup G)
    (i j : Fin 2) (hij : i ≠ j) :
    (F i ⧸ (F j).subgroupOf (F i)) → (graph F).neighborSet (CosetGeometry.base F i) :=
  Quotient.lift (fun a : F i =>
    ⟨⟨j, (a : G)⟩, by
      refine ⟨hij, ?_⟩
      apply (CosetGeometry.incident_base_iff F i _).mpr
      exact ⟨a,a.property,rfl⟩⟩) (by
        intro a b hab
        apply Subtype.ext
        apply congrArg (CosetGeometry.Vertex.mk j)
        apply QuotientGroup.eq.mpr
        have hh : a⁻¹ * b ∈ (F j).subgroupOf (F i) :=
          QuotientGroup.leftRel_apply.mp hab
        exact hh)

private theorem neighborQuotientMap_bijective {G : Type*} [Group G]
    (F : Fin 2 → Subgroup G) (i j : Fin 2) (hij : i ≠ j) :
    Function.Bijective (neighborQuotientMap F i j hij) := by
  constructor
  · intro x y hxy
    obtain ⟨a,rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b,rfl⟩ := QuotientGroup.mk_surjective y
    apply QuotientGroup.eq.mpr
    have hh := congrArg Subtype.val hxy
    change CosetGeometry.Vertex.mk j ((a : G) : G ⧸ F j) =
      CosetGeometry.Vertex.mk j ((b : G) : G ⧸ F j) at hh
    have he : ((a : G) : G ⧸ F j) = ((b : G) : G ⧸ F j) := by
      simpa only [CosetGeometry.Vertex.mk.injEq,heq_eq_eq,true_and] using hh
    change (a : G)⁻¹ * b ∈ F j
    exact QuotientGroup.eq.mp he
  · rintro ⟨⟨k,c⟩,hadj⟩
    have hk : k = j := by
      have hki : i ≠ k := hadj.1
      omega
    subst k
    obtain ⟨a,ha,hq⟩ := (CosetGeometry.incident_base_iff F i _).mp hadj.2
    refine ⟨((⟨a,ha⟩ : F i) : F i ⧸ (F j).subgroupOf (F i)),?_⟩
    apply Subtype.ext
    exact congrArg (CosetGeometry.Vertex.mk j) hq

theorem neighbor_base_card {G : Type*} [Group G]
    (F : Fin 2 → Subgroup G) (i j : Fin 2) (hij : i ≠ j) :
    Nat.card ((graph F).neighborSet (CosetGeometry.base F i)) =
      ((F j).subgroupOf (F i)).index := by
  rw [← Nat.card_congr (Equiv.ofBijective (neighborQuotientMap F i j hij)
    (neighborQuotientMap_bijective F i j hij))]
  rfl

theorem source_neighbor_base_card (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (i : Fin 2) :
    Nat.card ((graph (endpointParabolics Q)).neighborSet
      (CosetGeometry.base (endpointParabolics Q) i)) =
      1 + Nat.card (simpleRoot Q split i) := by
  have hne : i ≠ i.rev := by fin_cases i <;> decide
  rw [neighbor_base_card (endpointParabolics Q) i i.rev hne]
  have hI : endpointParabolics Q i ⊓ endpointParabolics Q i.rev = Q.tits.B := by
    fin_cases i
    · exact Q.standard_intersection
    · change Q.tits.standardParabolic {Q.simple 1} ⊓
        Q.tits.standardParabolic {Q.simple 0} = Q.tits.B
      rw [inf_comm]
      exact Q.standard_intersection
  have hsub : (endpointParabolics Q i.rev).subgroupOf (endpointParabolics Q i) =
      Q.tits.B.subgroupOf (endpointParabolics Q i) := by
    ext x
    change (x : X ⧸ Q.D) ∈ endpointParabolics Q i.rev ↔ (x : X ⧸ Q.D) ∈ Q.tits.B
    rw [←hI]
    exact ⟨fun h => ⟨x.property,h⟩, fun h => h.2⟩
  rw [hsub]
  exact singleton_parabolic_root_index Q split i

private def translationIso {G : Type*} [Group G] (F : Fin 2 → Subgroup G) (g : G) :
    graph F ≃g graph F where
  toFun v := g • v
  invFun v := g⁻¹ • v
  left_inv v := inv_smul_smul g v
  right_inv v := smul_inv_smul g v
  map_rel_iff' := by
    intro v w
    change (v.type ≠ w.type ∧ CosetGeometry.Incident F (g • v) (g • w)) ↔ _
    rw [CosetGeometry.incident_smul_iff]
    rfl

theorem source_neighbor_card (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (v : CosetGeometry.Vertex (endpointParabolics Q)) :
    Nat.card ((graph (endpointParabolics Q)).neighborSet v) =
      1 + Nat.card (simpleRoot Q split v.type) := by
  obtain ⟨g,hg⟩ := CosetGeometry.exists_smul_base (endpointParabolics Q) v
  have he := Nat.card_congr ((translationIso (endpointParabolics Q) g).mapNeighborSet
    (CosetGeometry.base (endpointParabolics Q) v.type))
  change Nat.card ((graph _).neighborSet _) = Nat.card ((graph _).neighborSet (g • _)) at he
  rw [hg] at he
  rw [←he]
  exact source_neighbor_base_card Q split v.type

theorem simpleRoot_card_gt_one (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (i : Fin 2) : 1 < Nat.card (simpleRoot Q split i) := by
  have : Nontrivial (simpleRoot Q split i) :=
    (simpleRoot Q split i).nontrivial_iff_ne_bot.mpr (simpleRoot_ne_bot Q split i)
  exact Finite.one_lt_card

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.PolygonParameters
