module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.G2.MSVertexAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.G2.MSReciprocal
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.ReciprocalCoordinates

/-!
# Inner critical images in the original G₂(4) escape

Restrict the constructed vertex quotient to the opposite critical seed.
Its kernel is that seed's literal centralizer of the other seed, and the
natural projection gives reciprocal fixed-space bounds. The G₂ offender
classification makes both images inner of order 64. Their lifts lie in the
actual residual times the two-core at the opposite vertex.

The final theorem constructs this configuration from the original Sylow
normalizer escape, with no extra recognition, index or inner-action premise.
This establishes the reciprocal-image step of MS93 (3.2), pp.865--866. The
comparison of field structures and exclusion of q=4 remain with this owner;
the final 11.2.3 assembly is qt-d-1222-natural-normalizer-source.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Representation.OneCohomology
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.G2MS
variable {M J W N D : Type*} [Group M] [Finite M] [Group J]
  [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup N] [Module (ZMod 2) N] [Module.Finite (ZMod 2) N]
  {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}
  {ρ : Representation (ZMod 2) J W} {B : Subgroup J}
  {τ : Representation (ZMod 2) D N}

/-- Restriction of the literal vertex quotient to the opposite critical seed. -/
def criticalActor (path : CriticalPath R geometry a z)
    (κ : stabilizer R z →* J) : Z R a →* J :=
  κ.comp (inclusion (Z_le_stabilizer_of_dist_le a
    (geometry.exists_critical a path.start_color) path.critical.1.le))

/-- The original critical image is elementary and nontrivial, has the exact
centralizer index, and satisfies the reciprocal fixed-space bound. -/
theorem critical_actor_bounds (path : CriticalPath R geometry a z)
    (hb : 0 < geometry.b R) (hcomm : ⁅Z R a,Z R z⁆ ≠ ⊥)
    (E : VertexAction R z B) :
    IsElementaryTwo (criticalActor path E.quotient).range ∧
      Nat.card (criticalActor path E.quotient).range =
        (centralizer (Z R z : Set (FreeAmalgam R))).relIndex (Z R a) ∧
      2 ^ fixedCodim E.action (criticalActor path E.quotient).range ≤
        (centralizer (Z R a : Set (FreeAmalgam R))).relIndex (Z R z) := by
  let := finite_Z R a
  let := finite_Z R z
  let : Finite (U R z) := Finite.of_injective (inclusion (U_le_Z z)) (inclusion_injective _)
  let : IsElementaryAbelian 2 (Z R a) := geometry.Z_elementary hb a path.start_color
  let δ := criticalActor path E.quotient
  have hδ : δ.ker = (centralizer (Z R z : Set (FreeAmalgam R))).subgroupOf (Z R a) :=
    ChapterC.RankTwo.Sp4Four.SourceComparison.restricted_kernel_of_mapped_centralizer
      _ _ _ _ E.quotient E.kernel_centralizer
  have hc : Nat.card δ.range =
      (centralizer (Z R z : Set (FreeAmalgam R))).relIndex (Z R a) := by
    change Nat.card δ.range = ((centralizer (Z R z : Set (FreeAmalgam R))).subgroupOf (Z R a)).index
    rw [←hδ,index_ker]
  have he : IsElementaryTwo δ.range := by
    refine ⟨?_,IsElementaryAbelian.of_surjective δ.rangeRestrict δ.rangeRestrict_surjective⟩
    intro hz
    have hi : (centralizer (Z R z : Set (FreeAmalgam R))).relIndex (Z R a) = 1 := by
      rw [←hc,hz,card_bot]
    exact hcomm (commutator_eq_bot_iff_le_centralizer.mpr (relIndex_eq_one.mp hi))
  have hn : Z R a ≤ normalizer (U R z : Set (FreeAmalgam R)) :=
    (Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color)
      path.critical.1.le).trans (U_normalized z)
  refine ⟨he,hc,?_⟩
  exact (natural_fixed_index_le E.action _ _ hn E.projection E.projection_surjective
    δ (fun x u => E.conjugate
      (inclusion (Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color)
        path.critical.1.le) x) u)).trans
      (relIndex_le_of_le_right (U_le_Z z) index_ne_zero_of_finite)

omit [Finite M] in
/-- An inner critical image lifts into the actual residual times its two-core. -/
theorem critical_inner_lift (path : CriticalPath R geometry a z)
    (κ : stabilizer R z →* J) (B : Subgroup J)
    (hk : κ.ker.map (stabilizer R z).subtype = Q R z)
    (hL : ((Ltilde R z).subgroupOf (stabilizer R z)).map κ = B)
    (hinner : (criticalActor path κ).range ≤ B) :
    Z R a ≤ Ltilde R z ⊔ Q R z := by
  intro x hx
  have hxst := Z_le_stabilizer_of_dist_le a
    (geometry.exists_critical a path.start_color) path.critical.1.le hx
  have hmem : κ ⟨x,hxst⟩ ∈ ((Ltilde R z).subgroupOf (stabilizer R z)).map κ := by
    rw [hL]
    exact hinner ⟨⟨x,hx⟩,rfl⟩
  obtain ⟨y,hy,he⟩ := hmem
  have hyx : y⁻¹ * ⟨x,hxst⟩ ∈ κ.ker := by
    change κ (y⁻¹ * ⟨x,hxst⟩) = 1
    rw [map_mul,map_inv,he,inv_mul_cancel]
  have hQ : ((y : FreeAmalgam R)⁻¹ * x) ∈ Q R z := by
    rw [←hk]
    exact ⟨_,hyx,rfl⟩
  have hh := (Ltilde R z ⊔ Q R z).mul_mem (mem_sup_left hy) (mem_sup_right hQ)
  simpa only [Subgroup.coe_subtype,mul_inv_cancel_left] using hh

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.G2MS

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Representation.OneCohomology
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.G2MS
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (m : ActionEquiv D.centralQuotientAction
    (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
local notation "H" => (L ⊔ (T : Subgroup G) : Subgroup G)
local notation "K" => Subgroup.subgroupOf L (L ⊔ (T : Subgroup G))
local notation "R" => Subgroup.subgroupOf (T : Subgroup G) (L ⊔ (T : Subgroup G))

include D S m in
/-- Both original critical images are inner and have order 64. These are
literal vertex quotients and the original centralizer indices. -/
theorem source_critical_inner_indices
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R) :
    Z R a ≤ Ltilde R z ⊔ Q R z ∧ Z R z ≤ Ltilde R a ⊔ Q R a ∧
      (Q R z).relIndex (Z R a) = 64 ∧ (Q R a).relIndex (Z R z) = 64 := by
  have hC := (source_critical_geometry D S m hescape).2
  have hba : 0 < criticalDistance R a (geometry.exists_critical a path.start_color) := by
    rw [geometry.distance_constant a path.start_color]; exact hb
  have hrev := critical_reverse R geometry hC a path.start_color hba z path.end_color path.critical
  let rev : CriticalPath R geometry z a := CriticalPath.ofPair path.end_color hrev
  have hcomm := critical_noncommutation R geometry hC a path.start_color hba path.critical
  obtain ⟨Ee⟩ := source_vertex_action D S m hescape path.end_color
  obtain ⟨Ea⟩ := source_vertex_action D S m hescape path.start_color
  let := Ee.component_normal
  have hcomm' : ⁅Z R z,Z R a⁆ ≠ ⊥ := by rwa [commutator_comm]
  obtain ⟨hAe,hcarde,hbe⟩ := critical_actor_bounds path hb hcomm Ee
  obtain ⟨hAa,hcarda,hba'⟩ := critical_actor_bounds rev hb hcomm' Ea
  have hbe' : 2 ^ fixedCodim Ee.action (criticalActor path Ee.quotient).range ≤
      Nat.card (criticalActor rev Ea.quotient).range := by rwa [hcarda]
  have hba'' : 2 ^ fixedCodim Ea.action (criticalActor rev Ea.quotient).range ≤
      Nat.card (criticalActor path Ee.quotient).range := by rwa [hcarde]
  obtain ⟨hie,hia,horde,horda,_,_⟩ := reciprocal_natural_indices Ee.field Ea.field Ee.degree Ea.degree
    Ee.action Ea.action _ _ Ee.componentEquiv Ea.componentEquiv
    Ee.component_apply Ea.component_apply Ee.faithful Ea.faithful _ _ hAe hAa hbe' hba''
  refine ⟨critical_inner_lift path Ee.quotient _ Ee.kernel_core Ee.component_image hie,
    critical_inner_lift rev Ea.quotient _ Ea.kernel_core Ea.component_image hia,?_,?_⟩
  · rw [←ChapterC.RankTwo.Sp4Four.SourceComparison.quotient_image_card
      (Z R a) (stabilizer R z) (Q R z) _ Ee.quotient Ee.kernel_core]
    exact horde
  · rw [←ChapterC.RankTwo.Sp4Four.SourceComparison.quotient_image_card
      (Z R z) (stabilizer R a) (Q R a) _ Ea.quotient Ea.kernel_core]
    exact horda

include D S m in
/-- The actual escaping source supplies a reversible critical pair with both
inner images of order 64 and nontrivial original commutator. -/
theorem source_critical_inner_pair
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ∃ g : Geometry R, 0 < g.b R ∧ Even (g.b R) ∧
      ∃ a : Vertex R, ∃ ha : color R a = false,
        CriticalPair R (alpha R) a (g.exists_critical (alpha R) rfl) ∧
        CriticalPair R a (alpha R) (g.exists_critical a ha) ∧
        ⁅Z R (alpha R),Z R a⁆ ≠ ⊥ ∧
        Z R (alpha R) ≤ Ltilde R a ⊔ Q R a ∧
        Z R a ≤ Ltilde R (alpha R) ⊔ Q R (alpha R) ∧
        (Q R a).relIndex (Z R (alpha R)) = 64 ∧
        (Q R (alpha R)).relIndex (Z R a) = 64 := by
  obtain ⟨g,hpos,hev,a,ha,hc,hr,hn⟩ := source_critical_pair D S m hescape
  exact ⟨g,hpos,hev,a,ha,hc,hr,hn,
    source_critical_inner_indices D S m hescape (CriticalPath.ofPair rfl hc) hpos⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.G2MS
