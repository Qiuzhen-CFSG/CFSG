module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourSeedFixedTransfer
public import Theory.Representation.BinaryConjugationSection.CommutatorImage
public import Theory.Representation.BinaryConjugationSection.ConjugateSpan

/-!
# The full moved radius in the actual midpoint span

An actual large critical support path gives Vcirc_a inside the midpoint
normal span W of any distance-four path at a. Residual commutator
idempotence and W <= V_a then identify [W,L_a] with the literal Vcirc_a.
This connects the full radius movement to the moved part of the span
quotient without identifying reciprocal spans or quotient carriers.

Source: MS93 (5.12)(2), printed pp.925--926. No fixed-radius hypothesis
or module recognition premise is needed for this group equality.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Representation Representation.BinaryOffender Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

omit [Finite F] [CharP F 2] in
private theorem moving_full_commutation
    (geometry : Geometry d.radical) (hb : 2 < geometry.b d.radical)
    {a : Vertex d.radical} (ha : color d.radical a=false) :
    ⁅Vcirc d.radical a,Ltilde d.radical a⁆ = Vcirc d.radical a := by
  let S := stabilizer d.radical a
  let A := (V d.radical a).subgroupOf S
  let := finite_stabilizer d.radical a
  let : A.Normal := normal_subgroupOf_of_le_normalizer (DistanceEight.V_normalized d.radical a)
  have hVQ := geometry.V_le_Q hb a ha
  have hVS : V d.radical a ≤ S := hVQ.trans (fun _ hx => hx.1)
  have hp : IsPGroup 2 A :=
    ((Q_isPGroup d.radical (h.replacement_two_group d)
      (h.replacement_core_le d) a ha).to_le hVQ).comap_subtype
  have hi := commutator_isPPerfect_idempotent (pResidual 2 S) A
    (isPPerfect_pResidual 2) hp le_normalizer_of_normal
  have hh := congrArg (Subgroup.map S.subtype) hi
  have hm : A.map S.subtype=V d.radical a := map_subgroupOf_eq_of_le hVS
  simpa only [map_commutator,hm,Ltilde,Vcirc] using hh

/-- An actual large support path identifies the movement of the literal
midpoint normal span with the full moved radius at the original vertex. -/
theorem Input.replacement_distance_four_span_commutator_eq_moving_radius
    {geometry : Geometry d.radical} {a z c y : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (largePath : CriticalPath d.radical geometry c y)
    (hlarge : Nat.card F^2 ≤ (Q d.radical y).relIndex (Z d.radical c)) :
    ⁅localZSpan d.radical (path.walk.getVert 2) a,Ltilde d.radical a⁆ = Vcirc d.radical a := by
  have hl := path.length_eq_b
  have hWV : localZSpan d.radical (path.walk.getVert 2) a ≤ V d.radical a :=
    localZSpan_le_V d.radical (by
      rw [SimpleGraph.dist_comm,path.dist_start (by omega)])
  apply le_antisymm (commutator_mono hWV le_rfl)
  change Vcirc d.radical a ≤ _
  rw [←moving_full_commutation h d geometry (by omega) path.start_color]
  exact commutator_mono
    (h.replacement_distance_four_moving_le_midpoint_span_of_large_path d path hb largePath hlarge)
    le_rfl

/-- Under the same actual section coordinates, the full original moved radius
has exactly the moved image of the marked span action. No reciprocal quotient
or natural coordinates are substituted for this carrier or this map. -/
theorem Input.replacement_distance_four_span_moved_image
    {geometry : Geometry d.radical} {a z c₀ y : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (largePath : CriticalPath d.radical geometry c₀ y)
    (hlarge : Nat.card F^2 ≤ (Q d.radical y).relIndex (Z d.radical c₀))
    (E : BinaryField) (hE : E.degree=n)
    (f : stabilizer d.radical a →* Sp E.Carrier) (hf : Function.Surjective f)
    {V₀ : Type*} [AddCommGroup V₀] [Module (ZMod 2) V₀]
    (σ : Representation (ZMod 2) (Sp E.Carrier) V₀)
    (c : BinaryConjugationSection (stabilizer d.radical a)
      (localZSpan d.radical (path.walk.getVert 2) a)
      (localZSpan d.radical (path.walk.getVert 2) a ⊓ B d.radical a (geometry.Z_normal a))
      (σ.comp f)) :
    c.imageSpace (Vcirc d.radical a) = subspaceCommutator σ ⊤ ⊤ := by
  let := finite_stabilizer d.radical a
  have hcard : 2 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 2 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  let : Group.IsPerfect (Sp E.Carrier) := perfect_of_card_gt_two hcard
  have hmap : ((Ltilde d.radical a).subgroupOf (stabilizer d.radical a)).map f = ⊤ := by
    have he : (Ltilde d.radical a).subgroupOf (stabilizer d.radical a) =
        pResidual 2 (stabilizer d.radical a) :=
      comap_map_eq_self_of_injective (stabilizer d.radical a).subtype_injective _
    rw [he,map_pResidual_of_surjective 2 f hf,pResidual_eq_top_of_isPerfect 2]
  rw [←h.replacement_distance_four_span_commutator_eq_moving_radius d path hb largePath hlarge,
    commutator_comm,c.imageSpace_commutator _ _ (Ltilde_le_stabilizer a) le_rfl,
    c.imageSpace_self,subspaceCommutator_comp_map,hmap]

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
