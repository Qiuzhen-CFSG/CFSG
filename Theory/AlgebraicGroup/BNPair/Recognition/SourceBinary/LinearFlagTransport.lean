module
public import Theory.SpecificGroups.PSL3.RootPresentationRecognition.Quotient
public import Theory.SpecificGroups.PSL3.LinearThreeFieldTransport

/-!
# Field transport of the oriented projective flag amalgam

Coefficient transport preserves both full matrix parabolics and their
whole Borel. The scalar projection intertwines this same transport, so
restriction gives a projective amalgam isomorphism with both inclusion
squares. Its three equations retain the literal ambient field map in
either orientation. No injectivity of SL₃ → PSL₃ is required.

The source A₂ catalogue consumer uses this to transport a finite field
from any universe to its small copy. Source: DGS Theorem D, p.224;
Aschbacher--Smith F.1.4--5 and F.1.12(I)(1), pp.260,262--264.
Ambient coefficient transport is the attributed ATLAS construction
re-exported by LinearThreeFieldTransport.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.PSL3.RootPresentationRecognition
open LinearThree
variable {F K : Type*} [Field F] [Finite F] [Field K] [Finite K]
private theorem point_field_mem (e : F ≃+* K) (g : PSL(3,F)) :
    Atlas.fieldEquivPSL 3 e g ∈ pointParabolic K ↔ g ∈ pointParabolic F := by
  obtain ⟨g,rfl⟩ := projection_surjective F g
  rw [show projection F g = QuotientGroup.mk' _ g from rfl,Atlas.fieldEquivPSL_mk]
  change (Atlas.fieldEquivSL 3 e g) ∈ (pointParabolic K).comap (projection K) ↔
    g ∈ (pointParabolic F).comap (projection F)
  rw [pointParabolic_comap,pointParabolic_comap,mem_pointParabolicSL_iff,mem_pointParabolicSL_iff]
  change (e (g.val 1 0) = 0 ∧ e (g.val 2 0) = 0) ↔ _
  simp
private theorem line_field_mem (e : F ≃+* K) (g : PSL(3,F)) :
    Atlas.fieldEquivPSL 3 e g ∈ lineParabolic K ↔ g ∈ lineParabolic F := by
  obtain ⟨g,rfl⟩ := projection_surjective F g
  rw [show projection F g = QuotientGroup.mk' _ g from rfl,Atlas.fieldEquivPSL_mk]
  change (Atlas.fieldEquivSL 3 e g) ∈ (lineParabolic K).comap (projection K) ↔
    g ∈ (lineParabolic F).comap (projection F)
  rw [lineParabolic_comap,lineParabolic_comap,mem_lineParabolicSL_iff,mem_lineParabolicSL_iff]
  change (e (g.val 2 0) = 0 ∧ e (g.val 2 1) = 0) ↔ _
  simp
private theorem borel_field_mem (e : F ≃+* K) (g : PSL(3,F)) :
    Atlas.fieldEquivPSL 3 e g ∈ borel K ↔ g ∈ borel F := by
  obtain ⟨g,rfl⟩ := projection_surjective F g
  rw [show projection F g = QuotientGroup.mk' _ g from rfl,Atlas.fieldEquivPSL_mk]
  change (Atlas.fieldEquivSL 3 e g) ∈ (borel K).comap (projection K) ↔
    g ∈ (borel F).comap (projection F)
  rw [LinearThree.borel_comap,LinearThree.borel_comap,mem_borelSL_iff,mem_borelSL_iff]
  change (e (g.val 1 0) = 0 ∧ e (g.val 2 0) = 0 ∧ e (g.val 2 1) = 0) ↔ _
  simp

private theorem map_eq_of_mem_iff {A C : Type*} [Group A] [Group C]
    (e : A ≃* C) (U : Subgroup A) (V : Subgroup C)
    (h : ∀ a, e a ∈ V ↔ a ∈ U) : U.map e.toMonoidHom = V := by
  ext x
  obtain ⟨a,rfl⟩ := e.surjective x
  rw [mem_map_equiv,e.symm_apply_apply]
  exact (h a).symm

theorem map_flagVertex_field (e : F ≃+* K) (i j : Fin 2) :
    (flagVertex F i j).map (Atlas.fieldEquivPSL 3 e).toMonoidHom = flagVertex K i j := by
  apply map_eq_of_mem_iff
  intro a
  unfold flagVertex
  split
  · exact point_field_mem e a
  · exact line_field_mem e a

theorem map_borel_field (e : F ≃+* K) :
    (borel F).map (Atlas.fieldEquivPSL 3 e).toMonoidHom = borel K :=
  map_eq_of_mem_iff _ _ _ (borel_field_mem e)

@[expose] def flagFieldIso (e : F ≃+* K) (i : Fin 2) :
    RankTwoAmalgam.Iso (flagAmalgam F i) (flagAmalgam K i) where
  left := restrictEquiv (Atlas.fieldEquivPSL 3 e) _ _ (map_flagVertex_field e i 0)
  middle := restrictEquiv (Atlas.fieldEquivPSL 3 e) _ _ (map_borel_field e)
  right := restrictEquiv (Atlas.fieldEquivPSL 3 e) _ _ (map_flagVertex_field e i 1)
  left_commutes _ := Subtype.ext rfl
  right_commutes _ := Subtype.ext rfl

theorem flagFieldIso_left_apply (e : F ≃+* K) (i : Fin 2) (a : flagVertex F i 0) :
    ((flagFieldIso e i).left a : PSL(3,K)) = Atlas.fieldEquivPSL 3 e a := rfl

theorem flagFieldIso_middle_apply (e : F ≃+* K) (i : Fin 2) (b : borel F) :
    ((flagFieldIso e i).middle b : PSL(3,K)) = Atlas.fieldEquivPSL 3 e b := rfl

theorem flagFieldIso_right_apply (e : F ≃+* K) (i : Fin 2) (a : flagVertex F i 1) :
    ((flagFieldIso e i).right a : PSL(3,K)) = Atlas.fieldEquivPSL 3 e a := rfl
end Matrix.PSL3.RootPresentationRecognition

