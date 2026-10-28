module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.DiagramHall.LinearCovered
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.StarCoordinates
public import Theory.GroupTheory.Hall.PermutableActors
public import Theory.GroupTheory.SylowNormalizerOvergroup
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.Diagram
/-!
# Selecting the original Hall-normalizing graph actor

For the single PSL₃ component, the covered Borel is two-closed. Hall
conjugacy factors a diagram-moving Sylow element as an overlap element
times a Hall-normalizing Sylow element. The first factor acts inner on
the source component, so the second still moves the diagram. The relation
AS = SA and the disjoint Hall/Sylow orders make that second factor
normalize A as well. Its literal source quotient action preserves the
marked Borel and its normal Sylow two-subgroup.

Source: Aschbacher–Smith, 4.4.13(1), printed pp.623–624, with E.2.2(2b),
printed pp.215–216. The scalar-cover normalizer escape consumes this actor.
-/

public section
open Subgroup
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape.LinearThree
open MarkedModels MarkedModels.DiagramHall ChapterB
open Matrix.PSL3.LinearThree Matrix.PSL3.LinearThree.OuterExtensions
variable {X : Type*} [Group X] [Finite X]
variable {F : Type*} [Field F] [Finite F]
noncomputable section
/-- The actual quotient conjugation action in the prescribed projective marking. -/
@[expose] def sourceModelAction (M K : Subgroup X) [(sourceImage M K).Normal]
    (e : sourceImage M K ≃* PSL(3,F)) : X →* MulAut PSL(3,F) :=
  (MulAut.congr e).toMonoidHom.comp
    ((MulAut.conjNormal (H := sourceImage M K)).comp (QuotientGroup.mk' (sourceKernel M)))

omit [Finite X] [Finite F] in
/-- The source action is compatible with the given marking on each source element. -/
theorem sourceModelAction_apply (M K : Subgroup X) [(sourceImage M K).Normal]
    (e : sourceImage M K ≃* PSL(3,F)) (t : X) (z : sourceImage M K) :
    sourceModelAction M K e t (e z) =
      e (MulAut.conjNormal (QuotientGroup.mk' (sourceKernel M) t) z) := by
  simp only [sourceModelAction, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

omit [Finite X] [Finite F] in
/-- Elements of the original component induce inner projective automorphisms. -/
theorem sourceModelAction_inner (M K : Subgroup X) [(sourceImage M K).Normal]
    (e : sourceImage M K ≃* PSL(3,F)) {x : X} (hx : x ∈ K) :
    sourceModelAction M K e x =
      MulAut.conj (e ⟨QuotientGroup.mk' (sourceKernel M) x, x, hx, rfl⟩) := by
  change MulAut.congr e (MulAut.conjNormal ((QuotientGroup.mk' (sourceKernel M)) x)) = _
  rw [← MulAut.congr_conj]
  apply congrArg (MulAut.congr e)
  ext y
  rfl

omit [Finite X] in
private theorem sourceAutomizer_eq_map (M K T : Subgroup X) [(sourceImage M K).Normal] :
    sourceAutomizer M K T = (sourceImage M T).map
      (MulAut.conjNormal (H := sourceImage M K)) := by
  ext a
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x.val,hx,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    refine ⟨⟨x,?_⟩,hx,rfl⟩
    rw [normalizer_eq_top]
    trivial

omit [Finite F] in
/-- Membership in the original maximal subgroup preserves the marked Borel. -/
theorem sourceModelAction_preserves_borel (M K : Subgroup X) [(sourceImage M K).Normal]
    (e : sourceImage M K ≃* PSL(3,F))
    (he : (componentOverlap M K).map e.toMonoidHom = borel F)
    {x : X} (hx : x ∈ M) :
    (borel F).map (sourceModelAction M K e x).toMonoidHom = borel F := by
  let q := QuotientGroup.mk' (sourceKernel M)
  let a : MulAut (sourceImage M K) := MulAut.conjNormal (q x)
  have ha : (componentOverlap M K).map a.toMonoidHom = componentOverlap M K := by
    rw [source_overlap_coordinate]
    apply eq_of_le_of_card_ge
    · rintro z ⟨y,hy,rfl⟩
      change q x * y.val * (q x)⁻¹ ∈ sourceImage M M
      have hx' : q x ∈ sourceImage M M := mem_map_of_mem q hx
      exact (sourceImage M M).mul_mem ((sourceImage M M).mul_mem hx' hy)
        ((sourceImage M M).inv_mem hx')
    · rw [card_map_of_injective (f := a.toMonoidHom) a.injective]
  rw [← he, map_map]
  have hcomp : (sourceModelAction M K e x).toMonoidHom.comp e.toMonoidHom =
      e.toMonoidHom.comp a.toMonoidHom := by
    ext y
    simp only [sourceModelAction, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rfl
  rw [hcomp, ← map_map, ha]

/-- The same original actor preserves the normal Sylow subgroup of the Borel. -/
theorem sourceModelAction_preserves_unipotent {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2^n) (M K : Subgroup X) [(sourceImage M K).Normal]
    (e : sourceImage M K ≃* PSL(3,F))
    (he : (componentOverlap M K).map e.toMonoidHom = borel F)
    {x : X} (hx : x ∈ M) :
    (unipotent F).map (sourceModelAction M K e x).toMonoidHom = unipotent F := by
  let a := sourceModelAction M K e x
  have hB := sourceModelAction_preserves_borel M K e he hx
  have hnU := map_mono (f := a.toMonoidHom) (borel_le_normalizer_unipotent F)
  rw [hB, map_equiv_normalizer_eq] at hnU
  have hle : (unipotent F).map a.toMonoidHom ≤ unipotent F :=
    ((unipotentSylow F hn hF).isPGroup'.map a.toMonoidHom).le_sylow_of_normalized
      (unipotentSylow F hn hF) ((unipotent_le_borel F).trans hnU)
  exact eq_of_le_of_card_ge hle (by rw [card_map_of_injective (f := a.toMonoidHom) a.injective])

/-- Hall conjugacy retains a diagram-moving actor normalizing the prescribed subgroup. -/
theorem exists_hall_diagram_actor_of_normal {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2^n) (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (K : Subgroup X) (hK : K.IsCComponent)
    (hc : SingleClauses (minimalParabolicMax S hP) K S)
    [(sourceImage (minimalParabolicMax S hP) K).Normal]
    (e : sourceImage (minimalParabolicMax S hP) K ≃* PSL(3,F))
    (he : (componentOverlap (minimalParabolicMax S hP) K).map e.toMonoidHom = borel F)
    (hm : MovesDiagram (minimalParabolicMax S hP) K S e
      (pointParabolic F) (lineParabolic F))
    (Y A : Subgroup X) (hYM : Y ≤ minimalParabolicMax S hP)
    (hHall : IsHallSubgroup oddPrimes (Y.subgroupOf (minimalParabolicMax S hP)))
    (hAY : A ≤ Y)
    (hperm : (A : Set X) * (S : Set X) = (S : Set X) * (A : Set X)) :
    ∃ t : X, t ∈ S ∧ t ∈ normalizer (Y : Set X) ∧ t ∈ normalizer (A : Set X) ∧
      sourceModelAction (minimalParabolicMax S hP) K e t ∉ diagramTrivial F := by
  let M := minimalParabolicMax S hP
  have hSM : (S : Subgroup X) ≤ M := (minimalParabolicMax_spec S hP).2
  let : K.Normal := single_component_normal S hK hc
  have hq := single_overlap_quotient_two S hSM hc
  have hb := linear_coveredBorel hn hF S hP K hc e he
  have hYB : Y.subgroupOf M ≤ K.subgroupOf M :=
    OddHall.odd_subgroup_le _ _ hq (OddHall.odd_hall_odd hHall)
  obtain ⟨a, ha, hmoved⟩ := hm
  rw [sourceAutomizer_eq_map] at ha
  obtain ⟨s', ⟨s, hs, rfl⟩, rfl⟩ := ha
  have hsout : sourceModelAction M K e s ∉ diagramTrivial F := by
    intro hh
    exact hmoved ((mem_diagramTrivial_iff F _).mp hh)
  obtain ⟨q, hqB, t, htS, htY, hqt⟩ := OddHall.factor_through_overlap
    (K.subgroupOf M) hb (S.subtype hSM) (Y.subgroupOf M) hYB
    (hHall.subgroupOf hYB) ⟨s,hSM hs⟩ hs
  have htY' : (t : X) ∈ normalizer (Y : Set X) := by
    rw [← subgroupOf_normalizer_eq hYM] at htY
    exact htY
  have hqt' : (q : X) * (t : X) = s := congrArg Subtype.val hqt
  have hqtriv : sourceModelAction M K e q ∈ diagramTrivial F := by
    rw [sourceModelAction_inner M K e (x := (q : X)) hqB]
    apply (mem_diagramTrivial_iff F _).mpr
    exact ⟨⟨_,rfl⟩,⟨_,rfl⟩⟩
  have htout : sourceModelAction M K e t ∉ diagramTrivial F := by
    intro hh
    apply hsout
    rw [← hqt', map_mul]
    exact (diagramTrivial F).mul_mem hqtriv hh
  have hYodd : Odd (Nat.card Y) := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hYM).toEquiv]
    exact OddHall.odd_hall_odd hHall
  have hdis : Disjoint (S : Subgroup X) Y := by
    obtain ⟨k,hk⟩ := S.isPGroup'.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hk]
    exact (Nat.coprime_two_left.mpr hYodd).pow_left k
  exact ⟨t,htS,htY', normalizer_permutable_subgroup A S Y hAY hdis hperm ⟨htS,htY'⟩,
    htout⟩

/-- Normality of the literal source image follows from the original component product. -/
theorem single_sourceImage_normal (S : Sylow 2 X) {M K : Subgroup X}
    (hK : K.IsCComponent) (hc : SingleClauses M K S) :
    (sourceImage M K).Normal :=
  (single_component_normal S hK hc).map (QuotientGroup.mk' (sourceKernel M))
    (QuotientGroup.mk'_surjective (sourceKernel M))

/-- The original Hall and permutability hypotheses supply a diagram-moving actor
which preserves the prescribed subgroup and both standard Borel coordinates. -/
theorem exists_hall_diagram_actor {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2^n) (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (K : Subgroup X) (hK : K.IsCComponent)
    (hc : SingleClauses (minimalParabolicMax S hP) K S)
    (e : sourceImage (minimalParabolicMax S hP) K ≃* PSL(3,F))
    (he : (componentOverlap (minimalParabolicMax S hP) K).map e.toMonoidHom = borel F)
    (hm : MovesDiagram (minimalParabolicMax S hP) K S e
      (pointParabolic F) (lineParabolic F))
    (Y A : Subgroup X) (hYM : Y ≤ minimalParabolicMax S hP)
    (hHall : IsHallSubgroup oddPrimes (Y.subgroupOf (minimalParabolicMax S hP)))
    (hAY : A ≤ Y)
    (hperm : (A : Set X) * (S : Set X) = (S : Set X) * (A : Set X)) :
    let := single_sourceImage_normal S hK hc
    ∃ t : X, t ∈ S ∧ t ∈ normalizer (Y : Set X) ∧ t ∈ normalizer (A : Set X) ∧
      sourceModelAction (minimalParabolicMax S hP) K e t ∉ diagramTrivial F ∧
      (borel F).map (sourceModelAction (minimalParabolicMax S hP) K e t).toMonoidHom =
        borel F ∧
      (unipotent F).map (sourceModelAction (minimalParabolicMax S hP) K e t).toMonoidHom =
        unipotent F ∧
      sourceModelAction (minimalParabolicMax S hP) K e t ∉ Matrix.PSL3.ExtensionBorel.linearField F := by
  let := single_sourceImage_normal S hK hc
  obtain ⟨t,htS,htY,htA,htD⟩ := exists_hall_diagram_actor_of_normal hn hF S hP K hK hc
    e he hm Y A hYM hHall hAY hperm
  have htM := (minimalParabolicMax_spec S hP).2 htS
  refine ⟨t,htS,htY,htA,htD,sourceModelAction_preserves_borel _ _ e he htM,
    sourceModelAction_preserves_unipotent (by omega) hF _ _ e he htM,?_⟩
  rwa [← diagramTrivial_eq_linearField F (by omega : 0 < n) hF]
end
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape.LinearThree
