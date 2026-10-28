module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionPlaneCommutator

/-!
# The original plane-core involution classes

The ordinary binary plane radical has one identity and two conjugacy classes,
represented by the literal long and short Hermitian parameters. Transport
through the original plane map gives the same three-way cover of Q₂.

If the source long and short roots are not fused, the five-element local
long-root class maps bijectively to the ambient root class in Q₂. In the
exceptional case graph/short fusion supplies precisely this nonfusion by
F.4.36. This proves the Q₂ class-count field of `FusionFacts` from the earlier
fusion input, with no extra ambient classification assumption.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, F.4.27,
F.4.37 and F.5.3(8), printed pp.287, 293 and 300.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory Matrix
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourPlaneLocal UnitaryFourPlaneRadical UnitaryFourShortRoot
open UnitaryTwo.ModelClasses UnitaryTwo.ShortRootFusion UnitaryTwo.ShortRootQuotient
local notation "hn" => Nat.le_refl 1
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 hn
local notation "L" => L2Matrix 1 hn
local notation "W" => hermitianMatrices F σ
variable {G G0 : Type*} [Group G] [Group G0]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G)

def sourceModelPlaneMap : L →* G := (ordinaryMap c i true).comp matrixPlaneEquiv.toMonoidHom

theorem sourceModelPlaneMap_long (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z) :
    sourceModelPlaneMap c i modelLong = rootElement c i z :=
  (source_root_eq_planeParameter c i z h).symm

theorem sourceModelPlaneMap_short :
    sourceModelPlaneMap c i modelShort = sourceMarkedShort c i := rfl

theorem sourceModelPlaneMap_injective (hi : Function.Injective i) :
    Function.Injective (sourceModelPlaneMap c i) :=
  (ordinaryMap_injective c i hi true).comp matrixPlaneEquiv.injective

theorem sourceModelPlaneMap_radical :
    (radical F σ hσ).map (sourceModelPlaneMap c i) = Q c i true := by
  ext y
  rw [← sourcePlaneParameter_range c i]
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨X,hX⟩ := (radicalEquiv F σ hσ).surjective ⟨x,hx⟩
    exact ⟨X,congrArg (fun r : radical F σ hσ => sourceModelPlaneMap c i r.val) hX⟩
  · rintro ⟨X,rfl⟩
    exact ⟨(radicalEquiv F σ hσ X).val,(radicalEquiv F σ hσ X).property,rfl⟩

theorem source_Q_plane_classes (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
    (x : G) (hx : x ∈ Q c i true) :
    x = 1 ∨ IsConj (rootElement c i z) x ∨ IsConj (sourceMarkedShort c i) x := by
  rw [← sourceModelPlaneMap_radical c i] at hx
  obtain ⟨y,hy,rfl⟩ := hx
  rcases local_radical_classes y hy with he | hz | ht
  · exact Or.inl (by rw [he,map_one])
  · exact Or.inr (Or.inl (sourceModelPlaneMap_long c i z h ▸
      (sourceModelPlaneMap c i).map_isConj hz))
  · exact Or.inr (Or.inr ((sourceModelPlaneMap c i).map_isConj ht))

theorem source_root_class_Q_plane_of_nonfusion (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z)
    (hnonfusion : ¬ IsConj (rootElement c i z) (sourceMarkedShort c i)) :
    Nat.card (classIntersection (rootElement c i z) (Q c i true)) = 5 := by
  let f : {x : L // IsConj modelLong x} →
      classIntersection (rootElement c i z) (Q c i true) := fun x =>
    ⟨⟨sourceModelPlaneMap c i x.val,by
      rw [← sourceModelPlaneMap_radical c i]
      apply mem_map_of_mem
      obtain ⟨a,ha⟩ := isConj_iff.mp x.property
      rw [← ha]
      exact (inferInstance : (radical F σ hσ).Normal).conj_mem modelLong
        (radicalEquiv F σ hσ (Multiplicative.ofAdd (longParameter F σ))).property a⟩,
      sourceModelPlaneMap_long c i z h ▸ (sourceModelPlaneMap c i).map_isConj x.property⟩
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    exact sourceModelPlaneMap_injective c i h.embedding_injective
      (congrArg (fun a : classIntersection (rootElement c i z) (Q c i true) => a.val.val) he)
  have hs : Function.Surjective f := by
    intro x
    have hx : x.val.val ∈ (radical F σ hσ).map (sourceModelPlaneMap c i) :=
      (sourceModelPlaneMap_radical c i).ge x.val.property
    obtain ⟨y,hy,he⟩ := hx
    rcases local_radical_classes y hy with hy1 | hylong | hyshort
    · have hx1 : x.val.val = 1 := by rw [← he,hy1,map_one]
      have hz1 := isConj_one_left.mp (hx1 ▸ x.property)
      have hz2 := source_root_order c i z h
      rw [hz1,orderOf_one] at hz2
      omega
    · exact ⟨⟨y,hylong⟩,Subtype.ext (Subtype.ext he)⟩
    · have hshort : IsConj (sourceMarkedShort c i) x.val.val := by
        rw [← he]
        exact (sourceModelPlaneMap c i).map_isConj hyshort
      exact False.elim (hnonfusion (x.property.trans hshort.symm))
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hf,hs⟩).symm).trans local_long_class_card

theorem source_root_class_Q_plane_of_graph_fusion (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z)
    (hf : IsConj (Source.graphElement c i) (sourceMarkedShort c i)) :
    Nat.card (classIntersection (rootElement c i z) (Q c i true)) = 5 :=
  source_root_class_Q_plane_of_nonfusion c i z h
    (fun hz => Source.graph_not_conjugate_root c i z h (hf.trans hz.symm))

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
