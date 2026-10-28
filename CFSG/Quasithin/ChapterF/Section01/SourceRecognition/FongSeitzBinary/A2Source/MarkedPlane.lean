module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Source.MarkedCoreTransport
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Source.QuotientPlane
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearThreePresentation

/-!
# The affine plane on an independently marked A₂ quotient

The full amalgam marking preserves both endpoint indices. The same m=3
BN geometry therefore makes the two actual parabolic coset fibers a plane
of the original natural field order. Source overlap faithfulness makes its
action faithful. The two transported cores lie in the marked common Borel;
normality makes them fix their respective neighborhoods. Their common
nontrivial elements are thus elations. Conjugacy by the original natural
actor makes the entire centerfree core act regularly on affine points.

The resulting one-field affine chart evaluates through the supplied full
endpoint marking. It uses no homomorphism from the original ambient carrier
to the independent quotient, and no perfectness premise, including q=2,4.
Affine line equations and the six-root application are subsequent steps.
Source: DGS, Groups and Graphs, 10.5 and Theorem D, printed pp.156,224.
-/

@[expose] public noncomputable section
open Subgroup Configuration Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source.MarkedPlane
open DGS85 DGS85.NoncommutingProfile Subgroup.CosetGeometry.RankTwo
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open MarkedCoreTransport
variable {G X : Type*} [Group G] [Group X] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  {P : Fin 2 → Subgroup X} (d : MarkedQuotient P)
  (mark : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    d.standardAmalgam)
  (h : HypothesisF11 L S)

/-- The whole two marked parabolics generate this independent quotient. -/
theorem generate : TriangleGeometry.family d false ⊔ TriangleGeometry.family d true = ⊤ := by
  apply top_unique
  rw [←d.tits.standardParabolic_S]
  apply d.tits.standardParabolic_le
  · exact (d.tits.B_le_standardParabolic {d.simple 0}).trans le_sup_left
  · intro s hs
    obtain ⟨i,rfl⟩ := d.simple_range ▸ hs
    fin_cases i
    · intro x hx
      exact (le_sup_left : TriangleGeometry.family d false ≤ _ )
        (d.tits.bruhatCell_subset_standardParabolic_of_mem (Set.mem_singleton (d.simple 0)) hx)
    · intro x hx
      exact (le_sup_right : TriangleGeometry.family d true ≤ _ )
        (d.tits.bruhatCell_subset_standardParabolic_of_mem (Set.mem_singleton (d.simple 1)) hx)

include mark h in
/-- The actual full-overlap marking makes the independent quotient action faithful. -/
theorem faithful : FaithfulSMul (X ⧸ d.D) (Vertex (TriangleGeometry.family d)) := by
  apply faithfulSMul_iff.mpr
  intro g hg
  have hk : g ∈ (MulAction.toPermHom (X ⧸ d.D) (Vertex (TriangleGeometry.family d))).ker :=
    Equiv.Perm.ext hg
  rw [global_kernel] at hk
  change g ∈ (d.tits.standardParabolic {d.simple 0} ⊓ d.tits.standardParabolic {d.simple 1}).normalCore at hk
  rw [d.standard_intersection,LinearThreePresentation.borel_core_eq_bot d mark h] at hk
  exact hk

include mark in
/-- The independent marking preserves each complete vertex valence. -/
theorem base_neighbor_card (i : Bool) :
    Nat.card ((graph (TriangleGeometry.family d)).neighborSet (base (TriangleGeometry.family d) i)) =
    Nat.card ((graph (fullFamily L S)).neighborSet (base (fullFamily L S) i)) := by
  rw [card_neighbor_base,card_neighbor_base]
  have ht : ((TriangleGeometry.family d (!i)).subgroupOf (TriangleGeometry.family d i)).index =
      (d.tits.B.subgroupOf (TriangleGeometry.family d i)).index := by
    change (TriangleGeometry.family d (!i)).relIndex (TriangleGeometry.family d i) = _
    cases i
    · change (d.tits.standardParabolic {d.simple 1}).relIndex
        (d.tits.standardParabolic {d.simple 0}) = _
      rw [←inf_relIndex_left, d.standard_intersection]
      rfl
    · change (d.tits.standardParabolic {d.simple 0}).relIndex
        (d.tits.standardParabolic {d.simple 1}) = _
      rw [←inf_relIndex_right, d.standard_intersection]
      rfl
  rw [ht]
  have hs : ((fullFamily L S (!i)).subgroupOf (fullFamily L S i)).index =
      ((parabolic L S 0 ⊓ parabolic L S 1).subgroupOf
        (parabolic L S (if i then 1 else 0))).index := by
    change (fullFamily L S (!i)).relIndex (fullFamily L S i) = _
    cases i
    · change ((parabolic L S 1).comap (generated L S).subtype).relIndex
        ((parabolic L S 0).subgroupOf (generated L S)) = _
      rw [relIndex_comap,map_subgroupOf_eq_of_le (parabolic_le_generated 0),←inf_relIndex_left]
      rfl
    · change ((parabolic L S 0).comap (generated L S).subtype).relIndex
        ((parabolic L S 1).subgroupOf (generated L S)) = _
      rw [relIndex_comap,map_subgroupOf_eq_of_le (parabolic_le_generated 1),←inf_relIndex_right]
      rfl
  rw [hs]
  cases i
  · change (d.tits.B.subgroupOf (d.tits.standardParabolic {d.simple 0})).index =
      ((parabolic L S 0 ⊓ parabolic L S 1).subgroupOf (parabolic L S 0)).index
    simpa only [RankTwoAmalgam.ofSubgroups,inclusion_range] using
      (RootCoordinates.marked_amalgam_left_index d mark).symm
  · change (d.tits.B.subgroupOf (d.tits.standardParabolic {d.simple 1})).index =
      ((parabolic L S 0 ⊓ parabolic L S 1).subgroupOf (parabolic L S 1)).index
    simpa only [RankTwoAmalgam.ofSubgroups,inclusion_range] using
      (RootCoordinates.marked_amalgam_right_index d mark).symm

variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
local instance markedPlaneFieldAlgebra {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2
variable
  (c₀ : BOneActionData (fullFamily L S) (base (fullFamily L S) false)
    (base (fullFamily L S) true) k₀ W₀)
  (c₁ : BOneActionData (fullFamily L S) (base (fullFamily L S) true)
    (base (fullFamily L S) false) k₁ W₁)
  (hn₀ : (commonBorel L S).subgroupOf (generated L S) ≤ normalizer (c₀.actor : Set (generated L S)))
  (hn₁ : (commonBorel L S).subgroupOf (generated L S) ≤ normalizer (c₁.actor : Set (generated L S)))
  (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))

include mark h c₀ c₁ hn₀ hn₁ E₀ in
/-- Both quotient vertex orbits have the order of the same original natural field. -/
theorem neighbor_card (v : Vertex (TriangleGeometry.family d)) :
    Nat.card ((graph (TriangleGeometry.family d)).neighborSet v) = Nat.card k₁ + 1 := by
  obtain ⟨g,hg⟩ := CosetGeometry.exists_smul_base (TriangleGeometry.family d) v
  have he := Nat.card_congr ((CosetGeometry.translationGraphIso (TriangleGeometry.family d) g).mapNeighborSet
    (base (TriangleGeometry.family d) v.type))
  change Nat.card ((graph (TriangleGeometry.family d)).neighborSet (base (TriangleGeometry.family d) v.type)) =
    Nat.card ((graph (TriangleGeometry.family d)).neighborSet (g • base (TriangleGeometry.family d) v.type)) at he
  rw [hg] at he
  rw [←he,base_neighbor_card d mark]
  exact (neighbor_card_of_actions h.generatedLocallyRankOneTriple c₀ c₁ hn₀ hn₁ E₀ _).trans
    (congrArg (· + 1) (paired_field_orders_eq h.generatedLocallyRankOneTriple c₀ c₁ E₀))

variable (hm : RootCoordinates.rotationOrder d = 3)

/-- The projective plane on the independent quotient, without an ambient descent map. -/
@[instance_reducible] def plane :
    ProjectivePlane (Point (TriangleGeometry.family d)) (Line (TriangleGeometry.family d)) :=
  projectivePlaneOfGeometry (TriangleGeometry.family d) (generate d)
    (TriangleGeometry.uniqueGeodesicsBelow d hm) (TriangleGeometry.diameter_le_three d hm)
    (Nat.card k₁) Finite.one_lt_card (neighbor_card d mark h c₀ c₁ hn₀ hn₁ E₀)

/-- Its order is the original chosen natural field order. -/
theorem plane_order :
    let := plane d mark h c₀ c₁ hn₀ hn₁ E₀ hm
    ProjectivePlane.order (Point (TriangleGeometry.family d)) (Line (TriangleGeometry.family d)) = Nat.card k₁ := by
  let := plane d mark h c₀ c₁ hn₀ hn₁ E₀ hm
  have hc : pointCount (Point (TriangleGeometry.family d)) (QuotientPlane.axis d) = Nat.card k₁ + 1 :=
    (Nat.card_congr (pointsOnLineEquivNeighbors (TriangleGeometry.family d) (QuotientPlane.axis d))).trans
      (neighbor_card d mark h c₀ c₁ hn₀ hn₁ E₀ (QuotientPlane.axis d).val)
  rw [ProjectivePlane.pointCount_eq] at hc
  omega

variable (split : SplitData d.tits)
include mark h c₀ c₁ split in
/-- The transported full parabolic core fixes the actual radius-one neighborhood. -/
theorem core_le_ballKernel (i : Bool) :
    (TriangleGeometry.family d i).pCoreIn 2 ≤ ballKernel (TriangleGeometry.family d)
      (base (TriangleGeometry.family d) i) 1 := by
  let F := TriangleGeometry.family d
  have hU : (F i).pCoreIn 2 ≤ split.U := by
    rw [←original_core_sup_eq_unipotent d mark h c₀ c₁ split]
    cases i
    · exact le_sup_left
    · exact le_sup_right
  have hB : (F i).pCoreIn 2 ≤ d.tits.B := hU.trans split.U_le
  have hc : (F i).pCoreIn 2 ≤ F false ⊓ F true := by
    change _ ≤ d.tits.standardParabolic {d.simple 0} ⊓ d.tits.standardParabolic {d.simple 1}
    rw [d.standard_intersection]
    exact hB
  have hs (j : Bool) : stabilizer F (base F j) = F j := CosetGeometry.stabilizer_base F j
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide, CosetGeometry.incident_base _ _ _⟩
  rw [ballKernel_one_eq_map_normalCore F hadj,hs i,hs (!i)]
  apply map_mono
  apply normal_le_normalCore.mpr
  intro a ha
  have hh : (a : X ⧸ d.D) ∈ (F i).pCoreIn 2 := mem_map_of_mem (F i).subtype ha
  have hi := hc hh
  change (a : X ⧸ d.D) ∈ F i ⊓ F (!i)
  cases i
  · exact ⟨hi.1,hi.2⟩
  · exact ⟨hi.2,hi.1⟩


include mark h c₀ c₁ split in
/-- The common actual core gives an elation, with movement certified by source faithfulness. -/
theorem intersection_isElation (z : X ⧸ d.D)
    (hz : z ∈ (TriangleGeometry.family d true).pCoreIn 2 ⊓
      (TriangleGeometry.family d false).pCoreIn 2) (hne : z ≠ 1) :
    IsElation z (QuotientPlane.centerPoint d) (QuotientPlane.axis d) := by
  refine ⟨⟨Bool.false_ne_true,CosetGeometry.incident_base _ _ _⟩,?_,?_,?_⟩
  · intro p hp
    apply Subtype.ext
    exact core_le_ballKernel d mark h c₀ c₁ split true hz.1 p.val
      ((mem_ball_one _ _ _).mpr (Or.inl hp.symm))
  · intro l hl
    apply Subtype.ext
    exact core_le_ballKernel d mark h c₀ c₁ split false hz.2 l.val
      ((mem_ball_one _ _ _).mpr (Or.inl hl))
  · have hm : ∃ v : Vertex (TriangleGeometry.family d), z • v ≠ v := by
      by_contra! hall
      exact hne (faithfulSMul_iff.mp (faithful d mark h) _ hall)
    obtain ⟨⟨i,v⟩,hv⟩ := hm
    cases i
    · exact Or.inl ⟨⟨⟨false,v⟩,rfl⟩,fun he => hv (congrArg Subtype.val he)⟩
    · exact Or.inr ⟨⟨⟨true,v⟩,rfl⟩,fun he => hv (congrArg Subtype.val he)⟩

/-- The original right actor fixes the independent quotient's actual infinity line. -/
theorem actor_fixes_axis (a : c₁.actor) :
    actorMap c₁ _ (endpointMarking d mark true) a • QuotientPlane.axis d = QuotientPlane.axis d := by
  apply Subtype.ext
  change actorMap c₁ _ (endpointMarking d mark true) a • CosetGeometry.base (TriangleGeometry.family d) true = _
  apply MulAction.mem_stabilizer_iff.mp
  rw [CosetGeometry.stabilizer_base]
  exact (endpointMarking d mark true ⟨a,c₁.actor_le a.property⟩).property

/-- The actual quotient core fixes its original marked axis. -/
theorem core_fixes_axis (a : (TriangleGeometry.family d true).pCoreIn 2) :
    (a : X ⧸ d.D) • QuotientPlane.axis d = QuotientPlane.axis d := by
  apply Subtype.ext
  change (a : X ⧸ d.D) • CosetGeometry.base (TriangleGeometry.family d) true = _
  apply MulAction.mem_stabilizer_iff.mp
  rw [CosetGeometry.stabilizer_base]
  exact pCoreIn_le 2 _ a.property

variable (hcenter : centerIn c₁.actor = ⊥)
include mark h c₀ c₁ E₁ hcenter split in
/-- The original natural conjugacy makes every nonidentity target-core element an elation. -/
theorem core_isElation (x : (TriangleGeometry.family d true).pCoreIn 2) (hx : x ≠ 1) :
    ∃ C : Point (TriangleGeometry.family d), IsElation (x : X ⧸ d.D) C (QuotientPlane.axis d) := by
  let hs := h.generatedLocallyRankOneTriple
  have hcores := paired_cores_eq_centers_of_actions hs c₀ c₁
  let I := Q (fullFamily L S) (base (fullFamily L S) true) ⊓
    Q (fullFamily L S) (base (fullFamily L S) false)
  have hI : I ≠ ⊥ := by
    intro he
    have hh := core_intersection_card c₁ hs hcores.2 hcenter E₁
    change Nat.card I = Nat.card k₁ at hh
    rw [he,Subgroup.card_bot] at hh
    exact (Finite.one_lt_card (α := k₁)).ne hh
  obtain ⟨z,hz,hz1⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hI)
  change z ≠ 1 at hz1
  let zQ : Q (fullFamily L S) (base (fullFamily L S) true) := ⟨z,hz.1⟩
  obtain ⟨x₀,rfl⟩ := (originalCoreEquiv d mark true).surjective x
  have hx₀ : x₀ ≠ 1 := by intro he; exact hx (he ▸ (originalCoreEquiv d mark true).map_one)
  have hzQ : zQ ≠ 1 := fun he => hz1 (congrArg Subtype.val he)
  obtain ⟨a,ha⟩ := core_nonidentity_conjugate c₁ hs hcores.2 hcenter E₁ zQ x₀ hzQ hx₀
  have hzI : originalCoreMap d mark true zQ ∈ (TriangleGeometry.family d true).pCoreIn 2 ⊓
      (TriangleGeometry.family d false).pCoreIn 2 := by
    refine ⟨(originalCoreEquiv d mark true zQ).property,?_⟩
    rw [←originalCoreMap_intersection d mark h ⟨z,hz.2,hz.1⟩]
    exact (originalCoreEquiv d mark false ⟨z,hz.2⟩).property
  have hzY : originalCoreMap d mark true zQ ≠ 1 := by
    intro he
    apply hzQ
    apply (originalCoreEquiv d mark true).injective
    apply Subtype.ext
    exact he.trans (congrArg Subtype.val (map_one (originalCoreEquiv d mark true))).symm
  have hel := (intersection_isElation d mark h c₀ c₁ split _ hzI hzY).conjugate
    (actorMap c₁ _ (endpointMarking d mark true) a)
  have hact : actorMap c₁ _ (endpointMarking d mark true) a * originalCoreMap d mark true zQ *
      (actorMap c₁ _ (endpointMarking d mark true) a)⁻¹ =
        (originalCoreEquiv d mark true x₀ : X ⧸ d.D) := by
    change _ = originalCoreMap d mark true x₀
    change _ = (originalCoreEquiv d mark true x₀ : X ⧸ d.D)
    rw [originalCoreEquiv_apply]
    have he : (⟨x₀,Q_le_stabilizer _ _ x₀.property⟩ : stabilizer (fullFamily L S) (base (fullFamily L S) true)) =
        ⟨a,c₁.actor_le a.property⟩ * ⟨zQ,Q_le_stabilizer _ _ zQ.property⟩ *
          (⟨a,c₁.actor_le a.property⟩ : stabilizer (fullFamily L S) (base (fullFamily L S) true))⁻¹ :=
      Subtype.ext ha.symm
    rw [he,map_mul,map_mul,map_inv]
    change _ * (originalCoreEquiv d mark true zQ : X ⧸ d.D) * _ = _
    rw [originalCoreEquiv_apply]
    rfl
  rw [hact,actor_fixes_axis] at hel
  exact ⟨_,hel⟩

/-- The original one-field coordinates now chart all affine points of the independent quotient. -/
def affineChart (o : {p : Point (TriangleGeometry.family d) // p ∉ QuotientPlane.axis d}) :
    (Fin 2 → k₁) ≃ {p : Point (TriangleGeometry.family d) // p ∉ QuotientPlane.axis d} :=
  letI := plane d mark h c₀ c₁ hn₀ hn₁ E₀ hm
  translationChart ((TriangleGeometry.family d true).pCoreIn 2) (QuotientPlane.axis d)
    (core_fixes_axis d) o (core_isElation d mark h c₀ c₁ E₁ split hcenter)
    (by
      rw [plane_order d mark h c₀ c₁ hn₀ hn₁ E₀ hm]
      change Nat.card ((d.tits.standardParabolic {d.simple 1}).pCoreIn 2) = _
      rw [Nat.card_congr (originalCoordinates d mark h c₀ c₁ hcenter E₁).toEquiv,
        Nat.card_congr Multiplicative.toAdd,Nat.card_fun,Nat.card_fin])
    (originalCoordinates d mark h c₀ c₁ hcenter E₁)

/-- Affine coordinates retain the literal full-endpoint marking and original field parameter. -/
theorem affineChart_apply (o : {p : Point (TriangleGeometry.family d) // p ∉ QuotientPlane.axis d})
    (t : Fin 2 → k₁) :
    (affineChart d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o t).val =
      (originalCoreEquiv d mark true
        ((A2Source.coreCoordinates c₁ h.generatedLocallyRankOneTriple
          (paired_cores_eq_centers_of_actions h.generatedLocallyRankOneTriple c₀ c₁).2 hcenter E₁).symm
            (.ofAdd t)) : X ⧸ d.D) • o.val := rfl

/-- The independently transported actual core acts by addition in this one field. -/
theorem affineChart_add
    (o : {p : Point (TriangleGeometry.family d) // p ∉ QuotientPlane.axis d})
    (a : (TriangleGeometry.family d true).pCoreIn 2) (t : Fin 2 → k₁) :
    (affineChart d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o
      ((originalCoordinates d mark h c₀ c₁ hcenter E₁ a).toAdd + t)).val =
      (a : X ⧸ d.D) • (affineChart d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o t).val := by
  let := plane d mark h c₀ c₁ hn₀ hn₁ E₀ hm
  exact translationChart_add _ _ _ _ _ _ _ a t

include mark h c₀ c₁ hn₀ hn₁ E₀ hm in
/-- Choosing an affine origin introduces no new premise on the independent quotient. -/
theorem exists_affine_origin :
    Nonempty {p : Point (TriangleGeometry.family d) // p ∉ QuotientPlane.axis d} := by
  let := plane d mark h c₀ c₁ hn₀ hn₁ E₀ hm
  obtain ⟨p,hp⟩ := Nondegenerate.exists_point (P := Point (TriangleGeometry.family d)) (QuotientPlane.axis d)
  exact ⟨⟨p,hp⟩⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source.MarkedPlane
