module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TriangleStructure.Incidence
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Source.MarkingAlignment
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Source.NormalGeneration
public import Theory.Combinatorics.TranslationPlane.FullFlagElations
public import Theory.Combinatorics.CollineationAction

/-!
# Full marked A₂ recognition from an original linear factor

The proved projective incidence coordinates give a faithful action on
PG(2,F). The actual middle root fills a native flag-elation group by its
order. Flag transitivity therefore realizes every elementary root in the
same quotient. Their preimages satisfy the six-root presentation.

The generated subgroup is normal, since its image is the native SL₃ image.
The whole axis radical acts by elations and belongs to it. A reflection
carries the middle root back to the remaining simple root; the original
normal-generation theorem now gives the whole quotient, including q=2.
Sylow alignment recovers U, the full Borel and both marked parabolics.

The final theorems discharge all natural-action, field-incidence, root-data
and generation premises from F.1.1, one original linear factor, rotation
three and the same marked split quotient. Both orientations and the literal
original quotient map are retained. The Chapter 12 consumer uses the full
amalgam comparison. Earlier quotient construction and exhaustive Weyl-order
selection remain separate obligations of the seven-row assembly.
Source: Fong--Seitz I (3E), printed p.14; DGS (10.5) and Theorem D, printed
pp.156,224; Steinberg, Lectures on Chevalley Groups, Section 6.
-/

@[expose] public noncomputable section
open Subgroup Configuration Theory.GroupTheory
open scoped MatrixGroups Pointwise commutatorElement
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Subgroup.CosetGeometry.RankTwo
open Theory.SpecificGroups.LinearHigher
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TriangleStructure
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 3) (i : Fin 2) {n : ℕ}
  (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^n))

namespace IncidenceRecognition
variable {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 2^n)
  (ep : Point (TriangleGeometry.family Q) ≃ TranslationPlane.FieldChart.PG F)
  (el : Line (TriangleGeometry.family Q) ≃ TranslationPlane.FieldChart.PG F)
  (hinc : ∀ p m, ep p ∈ el m ↔ p ∈ m)

def action : X ⧸ Q.D →*
    Collineation (TranslationPlane.FieldChart.PG F) (TranslationPlane.FieldChart.PG F) :=
  (Collineation.transport ep el hinc).comp
    (Collineation.ofAction (X ⧸ Q.D) (Point (TriangleGeometry.family Q)) (Line (TriangleGeometry.family Q)))

omit [Finite F] in
theorem action_point (g : X ⧸ Q.D) (p : Point (TriangleGeometry.family Q)) :
    Collineation.pointHom _ _ (action Q ep el hinc g) (ep p) = ep (g • p) := by
  simp only [action,MonoidHom.comp_apply,Collineation.transport_point,
    Equiv.symm_apply_apply,Collineation.ofAction_point]

omit [Finite F] in
theorem action_line (g : X ⧸ Q.D) (m : Line (TriangleGeometry.family Q)) :
    Collineation.lineHom _ _ (action Q ep el hinc g) (el m) = el (g • m) := by
  simp only [action,MonoidHom.comp_apply,Collineation.transport_line,
    Equiv.symm_apply_apply,Collineation.ofAction_line]

omit [Finite F] in
include e h in
theorem action_injective : Function.Injective (action Q ep el hinc) := by
  let := A2Source.MarkedPlane.faithful Q e h
  intro g k he
  apply eq_of_smul_eq_smul (α := Vertex (TriangleGeometry.family Q))
  rintro ⟨j,q⟩
  cases j
  · have hh := congrArg (fun a => Collineation.pointHom _ _ a (ep ⟨⟨false,q⟩,rfl⟩)) he
    rw [action_point,action_point] at hh
    exact congrArg Subtype.val (ep.injective hh)
  · have hh := congrArg (fun a => Collineation.lineHom _ _ a (el ⟨⟨true,q⟩,rfl⟩)) he
    rw [action_line,action_line] at hh
    exact congrArg Subtype.val (el.injective hh)

omit [Finite F] in
theorem action_elation_mem {g : X ⧸ Q.D}
    {C : Point (TriangleGeometry.family Q)} {l : Line (TriangleGeometry.family Q)}
    (he : IsElation g C l) : action Q ep el hinc g ∈ TranslationPlane.flagElations (ep C) (el l) := by
  constructor
  · intro p hp
    obtain ⟨p,rfl⟩ := ep.surjective p
    rw [hinc] at hp
    rw [action_point]
    exact congrArg ep (he.fixes_axis_points p hp)
  · intro m hm'
    obtain ⟨m,rfl⟩ := el.surjective m
    rw [hinc] at hm'
    rw [action_line]
    exact congrArg el (he.fixes_center_lines m hm')

def flagRootMap :
    (simpleRemainder Q split 1 ⊓ simpleRemainder Q split 0 : Subgroup (X ⧸ Q.D)) →*
      Collineation (TranslationPlane.FieldChart.PG F) (TranslationPlane.FieldChart.PG F) :=
  (action Q ep el hinc).comp (simpleRemainder Q split 1 ⊓ simpleRemainder Q split 0).subtype

omit [Finite F] in
include e h in
theorem flagRootMap_injective : Function.Injective (flagRootMap Q split ep el hinc) :=
  (action_injective Q e h ep el hinc).comp Subtype.val_injective

omit [Finite F] in
include e h hm i hi in
theorem flagRootMap_range_le : (flagRootMap Q split ep el hinc).range ≤
    TranslationPlane.flagElations (ep (A2Source.QuotientPlane.centerPoint Q))
      (el (A2Source.QuotientPlane.axis Q)) := by
  rintro _ ⟨a,rfl⟩
  change action Q ep el hinc (a : X ⧸ Q.D) ∈ _
  by_cases ha : (a : X ⧸ Q.D) = 1
  · rw [ha,map_one]; exact one_mem _
  exact action_elation_mem Q ep el hinc
    (original_intersection_isElation Q e h split hm i hi a a.property ha)

include e h hm i hi hF in
/-- The middle root fills the entire native flag-elation subgroup. -/
theorem flagRootMap_range_eq : (flagRootMap Q split ep el hinc).range =
    TranslationPlane.flagElations (ep (A2Source.QuotientPlane.centerPoint Q))
      (el (A2Source.QuotientPlane.axis Q)) := by
  classical
  have hCl : ep (A2Source.QuotientPlane.centerPoint Q) ∈ el (A2Source.QuotientPlane.axis Q) :=
    (hinc _ _).mpr ⟨Bool.false_ne_true,CosetGeometry.incident_base _ _ _⟩
  obtain ⟨o,ho⟩ := Nondegenerate.exists_point (P := TranslationPlane.FieldChart.PG F)
    (el (A2Source.QuotientPlane.axis Q))
  apply TranslationPlane.eq_flagElations_of_card _ _ hCl o ho _
    (flagRootMap_range_le Q e h split hm i hi ep el hinc)
  rw [←Nat.card_congr (MonoidHom.ofInjective (flagRootMap_injective Q e h split ep el hinc)).toEquiv,
    TranslationPlane.FieldChart.plane_order,hF,
    Theory.AlgebraicGroup.TitsSystem.SourceBinary.TriangleStructure.radical_intersection Q split hm 1 0 (by decide)]
  simp only [rootAt,card_rightConjugate]
  obtain ⟨K,hK,hfin,hcard,⟨ν⟩⟩ := original_linear_factors Q e h split hm i hi 1
  let := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let := h.finite_local 1
  obtain ⟨T,hT⟩ := h.sylow 1
  exact (simpleRoot_card_linear Q e h split 1 T hT ν).trans hcard

omit [Finite F] in
theorem action_flag_transitive (C l : TranslationPlane.FieldChart.PG F) (hCl : C ∈ l) :
    ∃ g : X ⧸ Q.D,
      Collineation.pointHom _ _ (action Q ep el hinc g) (ep (A2Source.QuotientPlane.centerPoint Q)) = C ∧
      Collineation.lineHom _ _ (action Q ep el hinc g) (el (A2Source.QuotientPlane.axis Q)) = l := by
  obtain ⟨p,rfl⟩ := ep.surjective C
  obtain ⟨m,rfl⟩ := el.surjective l
  rw [hinc] at hCl
  obtain ⟨g,hp,hl⟩ := incident_common_translate (TriangleGeometry.family Q) hCl.2
  rw [p.property] at hp
  rw [m.property] at hl
  exact ⟨g,by rw [action_point]; exact congrArg ep (Subtype.ext hp),
    by rw [action_line]; exact congrArg el (Subtype.ext hl)⟩

include e h split hm i hi hF in
/-- Flag transitivity transports the actual middle root to every native flag. -/
theorem flagElations_le_action_range (C l : TranslationPlane.FieldChart.PG F) (hCl : C ∈ l) :
    TranslationPlane.flagElations C l ≤ (action Q ep el hinc).range := by
  obtain ⟨g,hC,hl⟩ := action_flag_transitive Q ep el hinc C l hCl
  intro y hy
  rw [←hC,←hl,←TranslationPlane.flagElations_map_conj] at hy
  obtain ⟨z,hz,rfl⟩ := hy
  rw [←flagRootMap_range_eq Q e h split hm i hi hF ep el hinc] at hz
  obtain ⟨a,rfl⟩ := hz
  refine ⟨g * (a : X ⧸ Q.D) * g⁻¹,?_⟩
  simp only [map_mul,map_inv]
  rfl

include e h split hm i hi hF in
/-- Every native root is realized in the same source quotient. -/
theorem exists_root_preimage (r : Root 3) (a : F) :
    ∃ g : X ⧸ Q.D,
      action Q ep el hinc g =
        specialLinearCollineation (matrixRoot r a) :=
  flagElations_le_action_range Q e h split hm i hi hF ep el hinc _ _
    (TranslationPlane.FieldChart.coordinate_incident F r.property)
    (TranslationPlane.FieldChart.matrixRoot_mem_flagElations F r a)

/-- All six roots use the one field chart and its actual faithful projective action. -/
def compatibleRoot (r : Root 3) (a : F) : X ⧸ Q.D :=
  (exists_root_preimage Q e h split hm i hi hF ep el hinc r a).choose

/-- The native action equation fixes the scaling of each root parameter. -/
theorem action_compatibleRoot (r : Root 3) (a : F) :
    action Q ep el hinc
      (compatibleRoot Q e h split hm i hi hF ep el hinc r a) =
        specialLinearCollineation (matrixRoot r a) :=
  (exists_root_preimage Q e h split hm i hi hF ep el hinc r a).choose_spec

/-- All elementary relations hold for the constructed original-quotient roots.
The chain field includes all ordered triples, hence both signs and orientations. -/
theorem compatibleRoot_relations :
    Relations (compatibleRoot Q e h split hm i hi hF ep el hinc) := by
  have native : Relations (fun (r : Root 3) (a : F) =>
      specialLinearCollineation (matrixRoot r a)) :=
    matrixRoot_relations.map specialLinearCollineation
  constructor
  · intro r a b
    apply action_injective Q e h ep el hinc
    rw [map_mul,action_compatibleRoot,action_compatibleRoot,action_compatibleRoot]
    exact native.add r a b
  · intro r s a b hrs hsr
    apply action_injective Q e h ep el hinc
    rw [map_commutatorElement,action_compatibleRoot,action_compatibleRoot,map_one]
    exact native.distant r s a b hrs hsr
  · intro i j k hij hjk hik a b
    apply action_injective Q e h ep el hinc
    rw [map_commutatorElement,action_compatibleRoot,action_compatibleRoot,action_compatibleRoot]
    exact native.chain i j k hij hjk hik a b

/-- The subgroup generated by all six simultaneously parametrized source roots. -/
def rootClosure : Subgroup (X ⧸ Q.D) :=
  closure {g | ∃ r a, g = compatibleRoot Q e h split hm i hi hF ep el hinc r a}

/-- The root-generated subgroup has exactly the native matrix action image. -/
theorem rootClosure_map_action :
    (rootClosure Q e h split hm i hi hF ep el hinc).map
      (action Q ep el hinc) =
        (specialLinearCollineation (K := F)).range := by
  apply le_antisymm
  · apply map_le_iff_le_comap.mpr
    apply (closure_le _).mpr
    rintro _ ⟨r,a,rfl⟩
    exact ⟨matrixRoot r a, (action_compatibleRoot Q e h split hm i hi hF ep el hinc r a).symm⟩
  · rintro _ ⟨A,rfl⟩
    apply Atlas.sl_elementary_induction
      (fun A : SL(3,F) => specialLinearCollineation A ∈
        (rootClosure Q e h split hm i hi hF ep el hinc).map
          (action Q ep el hinc)) _
      (fun A B hA hB => by rw [map_mul]; exact mul_mem hA hB) A
    intro ii jj hij a
    refine ⟨compatibleRoot Q e h split hm i hi hF ep el hinc (root ii jj hij) a,
      subset_closure ⟨root ii jj hij,a,rfl⟩,?_⟩
    exact action_compatibleRoot Q e h split hm i hi hF ep el hinc _ _

/-- Source membership is determined faithfully by the native matrix image. -/
theorem rootClosure_eq_comap : rootClosure Q e h split hm i hi hF ep el hinc =
    (specialLinearCollineation (K := F)).range.comap
      (action Q ep el hinc) := by
  rw [←rootClosure_map_action Q e h split hm i hi hF ep el hinc]
  exact (comap_map_eq_self_of_injective
    (action_injective Q e h ep el hinc) _).symm

/-- The constructed six-root subgroup is normal in the whole same source quotient. -/
theorem rootClosure_normal : (rootClosure Q e h split hm i hi hF ep el hinc).Normal := by
  rw [rootClosure_eq_comap]
  let := TranslationPlane.FieldChart.specialLinear_range_normal (F := F)
  infer_instance


/-- Every actual axis-radical element has a native linear action. -/
theorem axisRadical_le_rootClosure : simpleRemainder Q split 1 ≤
    rootClosure Q e h split hm i hi hF ep el hinc := by
  intro x hx
  by_cases hx1 : x = 1
  · exact hx1 ▸ one_mem _
  obtain ⟨C,hC⟩ := original_radical_isElation Q e h split hm i hi ⟨x,hx⟩
    (fun he => hx1 (congrArg Subtype.val he))
  rw [rootClosure_eq_comap]
  exact TranslationPlane.FieldChart.flagElations_le_specialLinear_range _ _
    ((hinc _ _).mpr hC.incident) (action_elation_mem Q ep el hinc hC)

/-- Reflection carries the middle root back to the missing simple root.
Normal generation then gives the entire original quotient, including q=2. -/
theorem compatibleRoot_generate :
    closure {g | ∃ r a, g = compatibleRoot Q e h split hm i hi hF ep el hinc r a} = ⊤ := by
  let R := rootClosure Q e h split hm i hi hF ep el hinc
  let : R.Normal := rootClosure_normal Q e h split hm i hi hF ep el hinc
  have hV : simpleRemainder Q split 1 ≤ R :=
    axisRadical_le_rootClosure Q e h split hm i hi hF ep el hinc
  have hA : simpleRoot Q split 1 ≤ R := by
    intro x hx
    let s := representative (Q.simple 0)
    let z := (s : X ⧸ Q.D)⁻¹*x*(s : X ⧸ Q.D)
    have hz : z ∈ rootAt Q split 1 (Q.simple 0) := by
      change (s : X ⧸ Q.D)*z*(s : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split 1
      simpa only [z,mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using hx
    rw [←Theory.AlgebraicGroup.TitsSystem.SourceBinary.TriangleStructure.radical_intersection
      Q split hm 1 0 (by decide)] at hz
    have hh := Subgroup.Normal.conj_mem (inferInstance : R.Normal) z (hV hz.1) (s : X ⧸ Q.D)
    simpa only [z,mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using hh
  apply A2Source.normal_eq_top_of_unipotent_le Q e h split R
  intro x hx
  have hp : x ∈ (simpleRoot Q split 1 : Set (X ⧸ Q.D)) *
      (simpleRemainder Q split 1 : Set (X ⧸ Q.D)) := by
    rw [simpleRoot_mul_remainder]; exact hx
  obtain ⟨a,ha,b,hb,rfl⟩ := hp
  exact R.mul_mem (hA ha) (hV hb)

/-- The six constructed roots recognize the same quotient over the original field. -/
def unmarkedEquiv : (X ⧸ Q.D) ≃* PSL(3,F) := by
  let := Matrix.PSL3.RootPresentationRecognition.quotient_nontrivial Q
  exact Matrix.PSL3.RootPresentationRecognition.equiv
    (compatibleRoot_relations Q e h split hm i hi hF ep el hinc)
    (compatibleRoot_generate Q e h split hm i hi hF ep el hinc)
    (LinearThreePresentation.center_eq_bot Q e h split)

end IncidenceRecognition

include e h split hm i hi in
/-- One original linear factor and rotation three produce the full marked A₂
root data, with all field equations, generation and placements discharged. -/
theorem original_rootData :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2^n ∧
      ∃ j : Fin 2, Nonempty (Matrix.PSL3.RootPresentationRecognition.RootData Q split F j) := by
  obtain ⟨F,hF,hfin,hchar,hcard,c,hc⟩ := original_field_coordinates Q e h split hm i hi
  obtain ⟨o⟩ := original_affine_origin Q e h split hm i hi
  obtain ⟨ep,el,_,hinc,_⟩ := hc o
  exact ⟨F,hF,hfin,hchar,hcard,A2Source.MarkingAlignment.exists_rootData Q split
    (IncidenceRecognition.unmarkedEquiv Q e h split hm i hi hcard ep el hinc)⟩


include e h split hm i hi in
/-- Full marked recognition of the original triangle, over its original binary
degree. One quotient equivalence identifies U, the whole Borel and both
endpoints; the full inclusion amalgam evaluates through that same equivalence. -/
theorem original_marked_recognition :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2^n ∧
      ∃ (j : Fin 2) (E : (X ⧸ Q.D) ≃* PSL(3,F))
        (cmp : RankTwoAmalgam.Iso
          (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
            (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
          (Matrix.PSL3.RootPresentationRecognition.flagAmalgam F j)),
        (split.U.map E.toMonoidHom = Matrix.PSL3.LinearThree.unipotent F) ∧
        (Q.tits.B.map E.toMonoidHom = Matrix.PSL3.LinearThree.borel F) ∧
        ((Q.tits.standardParabolic {Q.simple j}).map E.toMonoidHom =
          Matrix.PSL3.LinearThree.pointParabolic F) ∧
        ((Q.tits.standardParabolic {Q.simple (1-j)}).map E.toMonoidHom =
          Matrix.PSL3.LinearThree.lineParabolic F) ∧
        (∀ a : parabolic L S 0, (cmp.left a : PSL(3,F)) = E (e.left a : X ⧸ Q.D)) ∧
        (∀ a : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G),
          (cmp.middle a : PSL(3,F)) = E (e.middle a : X ⧸ Q.D)) ∧
        (∀ a : parabolic L S 1, (cmp.right a : PSL(3,F)) = E (e.right a : X ⧸ Q.D)) := by
  obtain ⟨F,hF,hfin,hchar,hcard,j,⟨rd⟩⟩ := original_rootData Q e h split hm i hi
  have hs := LinearThreePresentation.subgroup_images Q e h split rd
  exact ⟨F,hF,hfin,hchar,hcard,j,LinearThreePresentation.quotientEquiv Q e h split rd,
    LinearThreePresentation.comparison Q e h split rd,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,
    LinearThreePresentation.comparison_left_apply Q e h split rd,
    LinearThreePresentation.comparison_middle_apply Q e h split rd,
    LinearThreePresentation.comparison_right_apply Q e h split rd⟩


omit Q e split hm in
include h i hi in
/-- At the literal generated-source quotient every original representative,
including the whole overlap, follows the original map Q₀.q. -/
theorem source_marked_comparison (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    (hm₀ : rotationOrder Q₀ = 3) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2^n ∧
      ∃ (j : Fin 2) (E : ((generated L S) ⧸ Q₀.D) ≃* PSL(3,F))
        (cmp : RankTwoAmalgam.Iso
          (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
            (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
          (Matrix.PSL3.RootPresentationRecognition.flagAmalgam F j)),
        (∀ a : parabolic L S 0, (cmp.left a : PSL(3,F)) =
          E (Q₀.q ⟨a,parabolic_le_generated 0 a.property⟩)) ∧
        (∀ a : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G),
          (cmp.middle a : PSL(3,F)) = E (Q₀.q ⟨a,parabolic_le_generated 0 a.property.1⟩)) ∧
        (∀ a : parabolic L S 1, (cmp.right a : PSL(3,F)) =
          E (Q₀.q ⟨a,parabolic_le_generated 1 a.property⟩)) := by
  obtain ⟨F,hF,hfin,hchar,hcard,j,⟨rd⟩⟩ :=
    original_rootData Q₀ (originalMarkedIso Q₀) h split₀ hm₀ i hi
  exact ⟨F,hF,hfin,hchar,hcard,j,
    LinearThreePresentation.quotientEquiv Q₀ (originalMarkedIso Q₀) h split₀ rd,
    LinearThreePresentation.originalComparison h Q₀ split₀ rd,
    LinearThreePresentation.originalComparison_left_apply h Q₀ split₀ rd,
    LinearThreePresentation.originalComparison_middle_apply h Q₀ split₀ rd,
    LinearThreePresentation.originalComparison_right_apply h Q₀ split₀ rd⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TriangleStructure
