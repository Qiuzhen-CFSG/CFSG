module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Source.LocalMatrices
public import Theory.Combinatorics.TranslationPlane.FlagElations

/-!
# The original core intersection is the full geometric flag root

Under the constructed projective coordinates the original adjacent-core
intersection consists of all elations with the original incident center and
axis. Its order q, its faithful action and the geometric evaluation bound
prove equality with the full flag subgroup. Thus no independently scaled
additive parametrization or missing flag-root equality is assumed.

Source: DGS, Groups and Graphs, centerfree branch of 10.5 and Theorem D,
printed pp.156,224. The independent amalgam transport and the other five
root groups remain subsequent steps of the same recognition family.
-/

@[expose] public noncomputable section
open Subgroup Configuration
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source
open DGS85 DGS85.NoncommutingProfile Subgroup.CosetGeometry.RankTwo
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
namespace ProjectiveCoordinates
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (h : HypothesisF11 L S) (d : SourceQuotient L S)
variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
local instance {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2
variable
  (c₀ : BOneActionData (fullFamily L S) (base (fullFamily L S) false)
    (base (fullFamily L S) true) k₀ W₀)
  (c₁ : BOneActionData (fullFamily L S) (base (fullFamily L S) true)
    (base (fullFamily L S) false) k₁ W₁)
  (hn₀ : (commonBorel L S).subgroupOf (generated L S) ≤ normalizer (c₀.actor : Set (generated L S)))
  (hn₁ : (commonBorel L S).subgroupOf (generated L S) ≤ normalizer (c₁.actor : Set (generated L S)))
  (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
  (hm : RootCoordinates.rotationOrder d = 3) (hcenter : centerIn c₁.actor = ⊥)

variable (o : {p : Point (TriangleGeometry.family d) // p ∉ QuotientPlane.axis d})

/-- The literal original adjacent-core intersection, acting through d.q. -/
def flagRootMap :
    (Q (fullFamily L S) (base (fullFamily L S) true) ⊓
      Q (fullFamily L S) (base (fullFamily L S) false) : Subgroup (generated L S)) →*
        Collineation (TranslationPlane.FieldChart.PG k₁) (TranslationPlane.FieldChart.PG k₁) :=
  (action h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o).comp
    (d.q.comp (Q (fullFamily L S) (base (fullFamily L S) true) ⊓
      Q (fullFamily L S) (base (fullFamily L S) false)).subtype)

/-- The original core intersection acts faithfully under this same quotient map. -/
theorem flagRootMap_injective :
    Function.Injective (flagRootMap h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o) := by
  intro a b hab
  have he := action_injective h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o hab
  have hp (x : (Q (fullFamily L S) (base (fullFamily L S) true) ⊓
      Q (fullFamily L S) (base (fullFamily L S) false) : Subgroup (generated L S))) :
      (x : generated L S) ∈ fullFamily L S true := by
    have hh := Q_le_stabilizer (fullFamily L S) (base (fullFamily L S) true) x.property.1
    simpa only [stabilizer,base,CosetGeometry.stabilizer_base] using hh
  have hh := (QuotientPlane.cover d).injective true
    (a₁ := ⟨a,hp a⟩) (a₂ := ⟨b,hp b⟩) he
  apply Subtype.ext
  exact congrArg (fun x : fullFamily L S true => (x : generated L S)) hh

/-- Both original neighborhood fixation conditions are the complete native flag conditions. -/
theorem flagRootMap_range_le :
    (flagRootMap h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o).range ≤
      TranslationPlane.flagElations
        (pointCoordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o (QuotientPlane.centerPoint d))
        (TranslationPlane.FieldChart.axis k₁) := by
  rintro _ ⟨a,rfl⟩
  by_cases ha : (a : generated L S) = 1
  · have ha' : a = 1 := Subtype.ext ha
    rw [ha',map_one]
    exact Subgroup.one_mem _
  let : MulAction (generated L S) (Point (TriangleGeometry.family d)) :=
    MulAction.compHom _ d.q
  let : MulAction (generated L S) (Line (TriangleGeometry.family d)) :=
    MulAction.compHom _ d.q
  have he := QuotientPlane.intersection_isElation d h.generatedLocallyRankOneTriple
    (a : generated L S) a.property ha
  constructor
  · intro p hp
    obtain ⟨p,rfl⟩ := (pointCoordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o).surjective p
    rw [←lineCoordinates_axis h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o,
      coordinates_incident] at hp
    change Collineation.pointHom _ _ (action h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o
      (d.q (a : generated L S))) _ = _
    rw [action_point]
    exact congrArg (pointCoordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o)
      (he.fixes_axis_points p hp)
  · intro m hm'
    obtain ⟨m,rfl⟩ := (lineCoordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o).surjective m
    rw [coordinates_incident] at hm'
    change Collineation.lineHom _ _ (action h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o
      (d.q (a : generated L S))) _ = _
    rw [action_line]
    exact congrArg (lineCoordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o)
      (he.fixes_center_lines m hm')

/-- The original core intersection fills the entire geometric flag-root subgroup.
In particular this supplies equality of root ranges, not just their orders. -/
theorem flagRootMap_range_eq :
    (flagRootMap h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o).range =
      TranslationPlane.flagElations
        (pointCoordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o (QuotientPlane.centerPoint d))
        (TranslationPlane.FieldChart.axis k₁) := by
  classical
  have hCl : pointCoordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o
      (QuotientPlane.centerPoint d) ∈ TranslationPlane.FieldChart.axis k₁ := by
    rw [←lineCoordinates_axis h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o,coordinates_incident]
    exact ⟨Bool.false_ne_true,CosetGeometry.incident_base _ _ _⟩
  apply TranslationPlane.eq_flagElations_of_card _ _ hCl
    (TranslationPlane.FieldChart.point k₁ 0) (TranslationPlane.FieldChart.point_not_mem_axis k₁ 0)
    _ (flagRootMap_range_le h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o)
  have hc := Nat.card_congr (Equiv.ofInjective
    (flagRootMap h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o)
    (flagRootMap_injective h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o))
  have hi := core_intersection_card c₁ h.generatedLocallyRankOneTriple
    (paired_cores_eq_centers_of_actions h.generatedLocallyRankOneTriple c₀ c₁).2 hcenter E₁
  have ho := Nat.card_congr (TranslationPlane.FieldChart.chart k₁)
  rw [Nat.card_fun,Nat.card_fin,card_affinePoints] at ho
  have ho' : ProjectivePlane.order (TranslationPlane.FieldChart.PG k₁)
      (TranslationPlane.FieldChart.PG k₁) = Nat.card k₁ := by nlinarith
  exact hc.symm.trans (hi.trans ho'.symm)
/-- Every native incident flag is reached by the same source quotient action. -/
theorem action_flag_transitive (C l : TranslationPlane.FieldChart.PG k₁) (hCl : C ∈ l) :
    ∃ g : (generated L S) ⧸ d.D,
      Collineation.pointHom _ _ (action h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o g)
        (pointCoordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o (QuotientPlane.centerPoint d)) = C ∧
      Collineation.lineHom _ _ (action h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o g)
        (TranslationPlane.FieldChart.axis k₁) = l := by
  obtain ⟨p,rfl⟩ := (pointCoordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o).surjective C
  obtain ⟨m,rfl⟩ := (lineCoordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o).surjective l
  rw [coordinates_incident] at hCl
  obtain ⟨g,hp,hl⟩ := incident_common_translate (TriangleGeometry.family d) hCl.2
  rw [p.property] at hp
  rw [m.property] at hl
  refine ⟨g,?_,?_⟩
  · rw [action_point]
    exact congrArg (pointCoordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o) (Subtype.ext hp)
  · rw [←lineCoordinates_axis h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o,action_line]
    exact congrArg (lineCoordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o) (Subtype.ext hl)

/-- All geometric flag roots belong to the actual source action image.
This follows by conjugating the original core intersection, with one shared
source element carrying both incident vertices. -/
theorem flagElations_le_action_range (C l : TranslationPlane.FieldChart.PG k₁) (hCl : C ∈ l) :
    TranslationPlane.flagElations C l ≤
      (action h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o).range := by
  obtain ⟨g,hC,hl⟩ := action_flag_transitive h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o C l hCl
  intro y hy
  rw [←hC,←hl,←TranslationPlane.flagElations_map_conj] at hy
  obtain ⟨z,hz,rfl⟩ := hy
  rw [←flagRootMap_range_eq h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o] at hz
  obtain ⟨a,rfl⟩ := hz
  refine ⟨g * d.q (a : generated L S) * g⁻¹,?_⟩
  simp only [map_mul,map_inv]
  rfl

end ProjectiveCoordinates
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source
