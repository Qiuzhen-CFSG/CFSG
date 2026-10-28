module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Source.MarkedProjectiveCoordinates
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Source.NormalGeneration
public import Theory.Combinatorics.TranslationPlane.FullFlagElations

/-!
# Six compatible generating roots in the independent A₂ quotient

The original shared core fills its entire geometric flag-elation group:
faithfulness, its order q and the geometric evaluation bound prove equality.
Flag transitivity then realizes all six native elementary roots in the
faithful action image. Their unique preimages satisfy every elementary
relation, including all mixed orientations.

The generated image is the native SL₃ image, normal under all collineations.
Every axis-core element is an elation, so belongs to that image. Original
natural conjugacy puts the other core in the same normal subgroup. Their
join is exactly U; the proved nonperfect normal-generation argument gives
the whole SAME quotient. The accepted presentation now gives PSL₃, including
q=2,4. No global ambient descent or unknown-group simplicity is used.
Source: DGS, Groups and Graphs, 10.5 and Theorem D, pp.156,224;
Steinberg, Lectures on Chevalley Groups, Section 6.
-/

@[expose] public noncomputable section
open Subgroup Configuration Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source
open DGS85 DGS85.NoncommutingProfile Subgroup.CosetGeometry.RankTwo
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
namespace MarkedProjectiveCoordinates
variable {G X : Type*} [Group G] [Group X] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  {P : Fin 2 → Subgroup X} (d : MarkedQuotient P)
  (mark : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    d.standardAmalgam)
  (h : HypothesisF11 L S)

variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
local instance markedRootsFieldAlgebra {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2
variable
  (c₀ : BOneActionData (fullFamily L S) (base (fullFamily L S) false)
    (base (fullFamily L S) true) k₀ W₀)
  (c₁ : BOneActionData (fullFamily L S) (base (fullFamily L S) true)
    (base (fullFamily L S) false) k₁ W₁)
  (hn₀ : (commonBorel L S).subgroupOf (generated L S) ≤ normalizer (c₀.actor : Set (generated L S)))
  (hn₁ : (commonBorel L S).subgroupOf (generated L S) ≤ normalizer (c₁.actor : Set (generated L S)))
  (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
  (hm : RootCoordinates.rotationOrder d = 3) (split : SplitData d.tits) (hcenter : centerIn c₁.actor = ⊥)

variable (o : {p : Point (TriangleGeometry.family d) // p ∉ QuotientPlane.axis d})
open MarkedCoreTransport
open Theory.SpecificGroups.LinearHigher
open scoped commutatorElement

/-- Transport an actual source elation to its full native flag subgroup. -/
theorem action_elation_mem {g : X ⧸ d.D}
    {C : Point (TriangleGeometry.family d)} {l : Line (TriangleGeometry.family d)}
    (he : IsElation g C l) :
    action d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o g ∈
      TranslationPlane.flagElations
        (pointCoordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o C)
        (lineCoordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o l) := by
  constructor
  · intro p hp
    obtain ⟨p,rfl⟩ := (pointCoordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o).surjective p
    rw [coordinates_incident] at hp
    rw [action_point]
    exact congrArg (pointCoordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o) (he.fixes_axis_points p hp)
  · intro m hm'
    obtain ⟨m,rfl⟩ := (lineCoordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o).surjective m
    rw [coordinates_incident] at hm'
    rw [action_line]
    exact congrArg (lineCoordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o) (he.fixes_center_lines m hm')

/-- The original shared core acts through the literal independent endpoint marking. -/
def flagRootMap :
    (Q (fullFamily L S) (base (fullFamily L S) true) ⊓
      Q (fullFamily L S) (base (fullFamily L S) false) : Subgroup (generated L S)) →*
        Collineation (TranslationPlane.FieldChart.PG k₁) (TranslationPlane.FieldChart.PG k₁) :=
  (action d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o).comp
    ((originalCoreMap d mark true).comp (inclusion inf_le_left))

/-- The original shared core embeds faithfully in the independent projective action. -/
theorem flagRootMap_injective :
    Function.Injective (flagRootMap d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o) := by
  intro a b hab
  have he := action_injective d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o hab
  have hh := (originalCoreEquiv d mark true).injective (Subtype.ext he)
  exact Subtype.ext (congrArg
    (fun x : Q (fullFamily L S) (base (fullFamily L S) true) => (x : generated L S)) hh)

/-- The two actual neighborhood fixation conditions give the native flag-root conditions. -/
theorem flagRootMap_range_le :
    (flagRootMap d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o).range ≤
      TranslationPlane.flagElations
        (pointCoordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o (QuotientPlane.centerPoint d))
        (TranslationPlane.FieldChart.axis k₁) := by
  rintro _ ⟨a,rfl⟩
  let z := originalCoreMap d mark true ⟨a,a.property.1⟩
  change action d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o z ∈ _
  by_cases hz : z = 1
  · rw [hz,map_one]; exact one_mem _
  have hI : z ∈ (TriangleGeometry.family d true).pCoreIn 2 ⊓ (TriangleGeometry.family d false).pCoreIn 2 := by
    refine ⟨(originalCoreEquiv d mark true ⟨a,a.property.1⟩).property,?_⟩
    change originalCoreMap d mark true ⟨a,a.property.1⟩ ∈ _
    rw [←originalCoreMap_intersection d mark h ⟨a,a.property.2,a.property.1⟩]
    exact (originalCoreEquiv d mark false ⟨a,a.property.2⟩).property
  rw [←lineCoordinates_axis d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o]
  exact action_elation_mem d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o
    (MarkedPlane.intersection_isElation d mark h c₀ c₁ split z hI hz)

/-- The original core intersection fills the entire geometric flag-root subgroup.
In particular this supplies equality of root ranges, not just their orders. -/
theorem flagRootMap_range_eq :
    (flagRootMap d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o).range =
      TranslationPlane.flagElations
        (pointCoordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o (QuotientPlane.centerPoint d))
        (TranslationPlane.FieldChart.axis k₁) := by
  classical
  have hCl : pointCoordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o
      (QuotientPlane.centerPoint d) ∈ TranslationPlane.FieldChart.axis k₁ := by
    rw [←lineCoordinates_axis d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o,coordinates_incident]
    exact ⟨Bool.false_ne_true,CosetGeometry.incident_base _ _ _⟩
  apply TranslationPlane.eq_flagElations_of_card _ _ hCl
    (TranslationPlane.FieldChart.point k₁ 0) (TranslationPlane.FieldChart.point_not_mem_axis k₁ 0)
    _ (flagRootMap_range_le d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o)
  have hc := Nat.card_congr (Equiv.ofInjective
    (flagRootMap d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o)
    (flagRootMap_injective d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o))
  have hi := core_intersection_card c₁ h.generatedLocallyRankOneTriple
    (paired_cores_eq_centers_of_actions h.generatedLocallyRankOneTriple c₀ c₁).2 hcenter E₁
  have ho := Nat.card_congr (TranslationPlane.FieldChart.chart k₁)
  rw [Nat.card_fun,Nat.card_fin,card_affinePoints] at ho
  have ho' : ProjectivePlane.order (TranslationPlane.FieldChart.PG k₁)
      (TranslationPlane.FieldChart.PG k₁) = Nat.card k₁ := by nlinarith
  exact hc.symm.trans (hi.trans ho'.symm)
/-- Every native incident flag is reached by the same source quotient action. -/
theorem action_flag_transitive (C l : TranslationPlane.FieldChart.PG k₁) (hCl : C ∈ l) :
    ∃ g : X ⧸ d.D,
      Collineation.pointHom _ _ (action d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o g)
        (pointCoordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o (QuotientPlane.centerPoint d)) = C ∧
      Collineation.lineHom _ _ (action d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o g)
        (TranslationPlane.FieldChart.axis k₁) = l := by
  obtain ⟨p,rfl⟩ := (pointCoordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o).surjective C
  obtain ⟨m,rfl⟩ := (lineCoordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o).surjective l
  rw [coordinates_incident] at hCl
  obtain ⟨g,hp,hl⟩ := incident_common_translate (TriangleGeometry.family d) hCl.2
  rw [p.property] at hp
  rw [m.property] at hl
  refine ⟨g,?_,?_⟩
  · rw [action_point]
    exact congrArg (pointCoordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o) (Subtype.ext hp)
  · rw [←lineCoordinates_axis d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o,action_line]
    exact congrArg (lineCoordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o) (Subtype.ext hl)

/-- All geometric flag roots belong to the actual source action image.
This follows by conjugating the original core intersection, with one shared
source element carrying both incident vertices. -/
theorem flagElations_le_action_range (C l : TranslationPlane.FieldChart.PG k₁) (hCl : C ∈ l) :
    TranslationPlane.flagElations C l ≤
      (action d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o).range := by
  obtain ⟨g,hC,hl⟩ := action_flag_transitive d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o C l hCl
  intro y hy
  rw [←hC,←hl,←TranslationPlane.flagElations_map_conj] at hy
  obtain ⟨z,hz,rfl⟩ := hy
  rw [←flagRootMap_range_eq d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o] at hz
  obtain ⟨a,rfl⟩ := hz
  refine ⟨g * originalCoreMap d mark true ⟨a,a.property.1⟩ * g⁻¹,?_⟩
  simp only [map_mul,map_inv]
  rfl

/-- Every native root is realized in the same source quotient. -/
theorem exists_root_preimage (r : Root 3) (a : k₁) :
    ∃ g : X ⧸ d.D,
      action d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o g =
        specialLinearCollineation (matrixRoot r a) :=
  flagElations_le_action_range d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o _ _
    (TranslationPlane.FieldChart.coordinate_incident k₁ r.property)
    (TranslationPlane.FieldChart.matrixRoot_mem_flagElations k₁ r a)

/-- All six roots use the one field chart and its actual faithful projective action. -/
def compatibleRoot (r : Root 3) (a : k₁) : X ⧸ d.D :=
  (exists_root_preimage d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o r a).choose

/-- The native action equation fixes the scaling of each root parameter. -/
theorem action_compatibleRoot (r : Root 3) (a : k₁) :
    action d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o
      (compatibleRoot d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o r a) =
        specialLinearCollineation (matrixRoot r a) :=
  (exists_root_preimage d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o r a).choose_spec

/-- All elementary relations hold for the constructed original-quotient roots.
The chain field includes all ordered triples, hence both signs and orientations. -/
theorem compatibleRoot_relations :
    Relations (compatibleRoot d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o) := by
  have native : Relations (fun (r : Root 3) (a : k₁) =>
      specialLinearCollineation (matrixRoot r a)) :=
    matrixRoot_relations.map specialLinearCollineation
  constructor
  · intro r a b
    apply action_injective d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o
    rw [map_mul,action_compatibleRoot,action_compatibleRoot,action_compatibleRoot]
    exact native.add r a b
  · intro r s a b hrs hsr
    apply action_injective d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o
    rw [map_commutatorElement,action_compatibleRoot,action_compatibleRoot,map_one]
    exact native.distant r s a b hrs hsr
  · intro i j k hij hjk hik a b
    apply action_injective d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o
    rw [map_commutatorElement,action_compatibleRoot,action_compatibleRoot,action_compatibleRoot]
    exact native.chain i j k hij hjk hik a b

/-- The subgroup generated by all six simultaneously parametrized source roots. -/
def rootClosure : Subgroup (X ⧸ d.D) :=
  closure {g | ∃ r a, g = compatibleRoot d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o r a}

/-- The root-generated subgroup has exactly the native matrix action image. -/
theorem rootClosure_map_action :
    (rootClosure d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o).map
      (action d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o) =
        (specialLinearCollineation (K := k₁)).range := by
  apply le_antisymm
  · apply map_le_iff_le_comap.mpr
    apply (closure_le _).mpr
    rintro _ ⟨r,a,rfl⟩
    exact ⟨matrixRoot r a, (action_compatibleRoot d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o r a).symm⟩
  · rintro _ ⟨A,rfl⟩
    apply Atlas.sl_elementary_induction
      (fun A : SL(3,k₁) => specialLinearCollineation A ∈
        (rootClosure d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o).map
          (action d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o)) _
      (fun A B hA hB => by rw [map_mul]; exact mul_mem hA hB) A
    intro i j hij a
    refine ⟨compatibleRoot d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o (root i j hij) a,
      subset_closure ⟨root i j hij,a,rfl⟩,?_⟩
    exact action_compatibleRoot d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o _ _

/-- Source membership is determined faithfully by the native matrix image. -/
theorem rootClosure_eq_comap : rootClosure d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o =
    (specialLinearCollineation (K := k₁)).range.comap
      (action d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o) := by
  rw [←rootClosure_map_action d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o]
  exact (comap_map_eq_self_of_injective
    (action_injective d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o) _).symm

/-- The constructed six-root subgroup is normal in the whole same source quotient. -/
theorem rootClosure_normal : (rootClosure d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o).Normal := by
  rw [rootClosure_eq_comap]
  let := TranslationPlane.FieldChart.specialLinear_range_normal (F := k₁)
  infer_instance

/-- Every axis-core element belongs to the generated roots, since every native flag group is linear. -/
theorem axisCore_le_rootClosure :
    (TriangleGeometry.family d true).pCoreIn 2 ≤ rootClosure d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o := by
  intro x hx
  by_cases hx1 : x = 1
  · exact hx1 ▸ one_mem _
  obtain ⟨C,hC⟩ := MarkedPlane.core_isElation d mark h c₀ c₁ E₁ split hcenter ⟨x,hx⟩
    (fun he => hx1 (congrArg Subtype.val he))
  rw [rootClosure_eq_comap]
  exact TranslationPlane.FieldChart.flagElations_le_specialLinear_range _ _
    ((coordinates_incident d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o _ _).mpr hC.incident)
    (action_elation_mem d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o hC)

/-- Natural conjugacy at the other endpoint places its entire actual core in the same normal closure. -/
theorem pointCore_le_rootClosure :
    (TriangleGeometry.family d false).pCoreIn 2 ≤ rootClosure d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o := by
  let R := rootClosure d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o
  let : R.Normal := rootClosure_normal d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o
  have hc₀ : centerIn c₀.actor = ⊥ := by
    apply card_eq_one.mp
    have he := paired_actor_center_orders_eq h.generatedLocallyRankOneTriple c₀ c₁ E₀ E₁
    rwa [hcenter,card_bot] at he
  let I := Q (fullFamily L S) (base (fullFamily L S) true) ⊓
    Q (fullFamily L S) (base (fullFamily L S) false)
  have hI : I ≠ ⊥ := by
    intro he
    have hh := core_intersection_card c₁ h.generatedLocallyRankOneTriple
      (paired_cores_eq_centers_of_actions h.generatedLocallyRankOneTriple c₀ c₁).2 hcenter E₁
    change Nat.card I = Nat.card k₁ at hh
    rw [he,card_bot] at hh
    exact (Finite.one_lt_card (α := k₁)).ne hh
  obtain ⟨z,hz,hz1⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hI)
  change z ≠ 1 at hz1
  intro x hx
  obtain ⟨x₀,hx₀⟩ := (originalCoreEquiv d mark false).surjective ⟨x,hx⟩
  have hxval : originalCoreMap d mark false x₀ = x := congrArg Subtype.val hx₀
  by_cases hx1 : x₀ = 1
  · rw [←hxval,hx1,map_one]; exact R.one_mem
  let z₀ : Q (fullFamily L S) (base (fullFamily L S) false) := ⟨z,hz.2⟩
  obtain ⟨a,ha⟩ := core_nonidentity_conjugate c₀ h.generatedLocallyRankOneTriple
    (paired_cores_eq_centers_of_actions h.generatedLocallyRankOneTriple c₀ c₁).1 hc₀ E₀ z₀ x₀
    (fun he => hz1 (congrArg Subtype.val he)) hx1
  have hzR : originalCoreMap d mark false z₀ ∈ R := by
    rw [originalCoreMap_intersection d mark h ⟨z,hz.2,hz.1⟩]
    exact axisCore_le_rootClosure d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o
      (originalCoreEquiv d mark true ⟨z,hz.1⟩).property
  have hconj := Subgroup.Normal.conj_mem (inferInstance : R.Normal) _ hzR
    (actorMap c₀ _ (endpointMarking d mark false) a)
  have he : actorMap c₀ _ (endpointMarking d mark false) a * originalCoreMap d mark false z₀ *
      (actorMap c₀ _ (endpointMarking d mark false) a)⁻¹ = originalCoreMap d mark false x₀ := by
    change _ * (originalCoreEquiv d mark false z₀ : X ⧸ d.D) * _ =
      (originalCoreEquiv d mark false x₀ : X ⧸ d.D)
    rw [originalCoreEquiv_apply,originalCoreEquiv_apply]
    have ha' : (⟨x₀,Q_le_stabilizer _ _ x₀.property⟩ : stabilizer (fullFamily L S) (base (fullFamily L S) false)) =
        ⟨a,c₀.actor_le a.property⟩ * ⟨z₀,Q_le_stabilizer _ _ z₀.property⟩ *
          (⟨a,c₀.actor_le a.property⟩ : stabilizer (fullFamily L S) (base (fullFamily L S) false))⁻¹ :=
      Subtype.ext ha.symm
    rw [ha',map_mul,map_mul,map_inv]
    rfl
  rwa [he,hxval] at hconj

/-- The six roots generate the SAME independent quotient, including nonperfect q=2. -/
theorem compatibleRoot_generate :
    closure {g | ∃ r a, g = compatibleRoot d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o r a} = ⊤ := by
  let R := rootClosure d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o
  let : R.Normal := rootClosure_normal d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o
  apply normal_eq_top_of_unipotent_le d mark h split R
  rw [←original_core_sup_eq_unipotent d mark h c₀ c₁ split]
  exact sup_le (pointCore_le_rootClosure d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o)
    (axisCore_le_rootClosure d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o)

/-- The proved six-root presentation recognizes this whole independent quotient. -/
def unmarkedEquiv : (X ⧸ d.D) ≃* PSL(3,k₁) := by
  let := Matrix.PSL3.RootPresentationRecognition.quotient_nontrivial d
  exact Matrix.PSL3.RootPresentationRecognition.equiv
    (compatibleRoot_relations d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o)
    (compatibleRoot_generate d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o)
    (LinearThreePresentation.center_eq_bot d mark h split)

end MarkedProjectiveCoordinates
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source
