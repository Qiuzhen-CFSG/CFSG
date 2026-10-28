module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceComparison.Normalizer
public import Theory.SpecificGroups.AlternatingSix.TripleCoverMarking

/-!
# Aligning the source and ATLAS pointwise edge fixers

The two edge fixers are perfect A₅ subgroups of the respective triple
covers of A₆. Their central saturations give six-coset coordinates.
The cover comparison intertwines the actual outer involutions in natural
S₆ coordinates. An inner adjustment aligns the base stabilizers, and
passing to derived subgroups aligns the actual A₅ edge fixers.
The same adjustment on the full normalizers retains the cubic subgroup
and the literal centralizer inclusion. The final application uses the
vertex and edge groups of the published uniqueness systems.

Source: Aschbacher, *Sporadic Groups* (1994), 47.10, pp.266–267.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceComparison
open SourceLocal SourceLocal.PrimeNormalizers.ThreeLocal
open Theory.GroupTheory.GraphUniquenessSystem
open Sporadic.LeechRelated.J2
namespace Target
open RecognitionGeometry RecognitionGeometry.VertexExtension

private theorem edge_le_centralizer : E ≤ C := by
  let e : E.subgroupOf M ≃* alternatingGroup (Fin 5) :=
    (subgroupOfEquivOfLe (show E ≤ M from inf_le_left)).trans LocalA5.edgeEquiv
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect (E.subgroupOf M) := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  have h := le_of_isPerfect_of_index_eq_two (E.subgroupOf M) CM centralizer_index
  intro x hx
  exact h (show (⟨x, (show E ≤ M from inf_le_left) hx⟩ : M) ∈ E.subgroupOf M from hx)
end Target

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
variable (D : Seed G) (F : EdgeFrame D)

/-- The normalizer comparison preserves the literal pointwise edge fixer,
as well as the marked cubic subgroup and the centralizer inclusion. -/
theorem edge_comparison :
    ∃ (eC : C D ≃* RecognitionGeometry.VertexExtension.C)
      (eM : M D ≃* RecognitionGeometry.M),
      (∀ c : C D, eM ⟨c, C_le_M D c.property⟩ =
        RecognitionGeometry.VertexExtension.centralInclusion (eC c)) ∧
      (∀ m : M D, m ∈ XM D ↔ eM m ∈ RecognitionGeometry.VertexExtension.XM) ∧
      (∀ m : M D, (m : G) ∈ edgeFixer G D.base F.y ↔
        (eM m : Carrier) ∈ RecognitionGeometry.E) := by
  obtain ⟨S, _, _⟩ := InvolutionGeometry.Applications.source_prime_local D
  obtain ⟨H⟩ := PrimeNormalizers.centralizerCalculation_of_selectedGeometry
    (InvolutionGeometry.card_eq D) S
  let := H.quasisimple
  let := RecognitionGeometry.VertexExtension.C_isQuasisimple ConcreteSystem.card_M
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let E := edgeFixer G D.base F.y
  have hE : E ≤ C D := by
    dsimp only [E]
    rw [edgeFixer_eq_centralizer_join_of_alternatingFive D D.base F.y
      (InvolutionGeometry.Applications.edgeFixer_equiv D F.adjacent)]
    exact centralizer_le (show D.X ≤ D.base.val ⊔ F.y.val from le_sup_left)
  let EC := E.subgroupOf (C D)
  let TC := RecognitionGeometry.E.subgroupOf RecognitionGeometry.VertexExtension.C
  let eEC : EC ≃* alternatingGroup (Fin 5) := (subgroupOfEquivOfLe hE).trans
    (InvolutionGeometry.Applications.edgeFixer_equiv D F.adjacent).some
  let eTC : TC ≃* alternatingGroup (Fin 5) :=
    (subgroupOfEquivOfLe Target.edge_le_centralizer).trans RecognitionGeometry.LocalA5.edgeEquiv
  let : Group.IsPerfect EC := Group.IsPerfect.ofSurjective
    (f := eEC.symm.toMonoidHom) eEC.symm.surjective
  let : Group.IsPerfect TC := Group.IsPerfect.ofSurjective
    (f := eTC.symm.toMonoidHom) eTC.symm.surjective
  have hsourceZ : Nat.card (center (C D)) = 3 := by
    rw [H.center_eq]; exact CentralizerCalculation.card_XC
  have htargetZ : Nat.card (center RecognitionGeometry.VertexExtension.C) = 3 := by
    rw [RecognitionGeometry.VertexExtension.center_C_eq_XC ConcreteSystem.card_M]
    exact RecognitionGeometry.VertexExtension.card_XC
  have hsourceQ : Nat.card (C D ⧸ center (C D)) = 360 := by
    rw [Nat.card_congr H.centerQuotientEquiv.toEquiv, nat_card_alternatingGroup]
    norm_num
  let targetCenterEquiv :=
    (QuotientGroup.quotientMulEquivOfEq
      (RecognitionGeometry.VertexExtension.center_C_eq_XC ConcreteSystem.card_M)).trans
      (RecognitionGeometry.VertexExtension.centralQuotientEquivAlt6 ConcreteSystem.card_M)
  have htargetQ : Nat.card (RecognitionGeometry.VertexExtension.C ⧸
      center RecognitionGeometry.VertexExtension.C) = 360 := by
    rw [Nat.card_congr targetCenterEquiv.toEquiv, nat_card_alternatingGroup]
    norm_num
  obtain ⟨s, i, hs⟩ := AlternatingSix.TripleCoverMarking.five_coordinates hsourceZ hsourceQ EC eEC
  obtain ⟨t, j, ht⟩ := AlternatingSix.TripleCoverMarking.five_coordinates htargetZ htargetQ TC eTC
  let s0 := (QuotientGroup.quotientMulEquivOfEq H.center_eq.symm).trans s
  let t0 := (QuotientGroup.quotientMulEquivOfEq
    (RecognitionGeometry.VertexExtension.center_C_eq_XC ConcreteSystem.card_M).symm).trans t
  let f : C D →* alternatingGroup (Fin 6) :=
    s0.toMonoidHom.comp (QuotientGroup.mk' (XC D))
  have hsmap (c : C D) : f c = s (QuotientGroup.mk' (center (C D)) c) := by
    change s (QuotientGroup.quotientMulEquivOfEq H.center_eq.symm (QuotientGroup.mk c)) = _
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  let g : RecognitionGeometry.VertexExtension.C →* alternatingGroup (Fin 6) :=
    t0.toMonoidHom.comp RecognitionGeometry.VertexExtension.centralQuotientMap
  have htmap (c : RecognitionGeometry.VertexExtension.C) :
      g c = t (QuotientGroup.mk' (center RecognitionGeometry.VertexExtension.C) c) := by
    change t (QuotientGroup.quotientMulEquivOfEq _ (QuotientGroup.mk c)) = _
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  obtain ⟨k, eC, eM, hk, hq, he, hX⟩ := normalizers_over_coordinates H s0 t0
  obtain ⟨c, hc⟩ := AlternatingSix.TripleCoverMarking.align EC TC f g
    (t0.surjective.comp (QuotientGroup.mk'_surjective _)) i j
    (fun x => by rw [hsmap]; exact hs x) (fun x => by rw [htmap]; exact ht x)
    eC k hk hq
  let m := RecognitionGeometry.VertexExtension.centralInclusion c
  let dC := eC.trans (MulAut.conj c)
  let dM := eM.trans (MulAut.conj m)
  have hres (x : C D) : dM ⟨x, C_le_M D x.property⟩ =
      RecognitionGeometry.VertexExtension.centralInclusion (dC x) := by
    change m * eM ⟨x, C_le_M D x.property⟩ * m⁻¹ = _
    rw [he]
    rfl
  have hcentral (x : C D) : (x : G) ∈ E ↔ (dC x : Carrier) ∈ RecognitionGeometry.E := by
    change x ∈ EC ↔ dC x ∈ TC
    rw [← hc]
    simp only [mem_map_equiv, dC, MulEquiv.symm_apply_apply]
  refine ⟨dC, dM, hres, ?_, ?_⟩
  · intro x
    rw [hX]
    change eM x ∈ RecognitionGeometry.VertexExtension.XM ↔
      m * eM x * m⁻¹ ∈ RecognitionGeometry.VertexExtension.XM
    exact (mem_normalizer_iff.mp (show m ∈ normalizer
      (RecognitionGeometry.VertexExtension.XM : Set RecognitionGeometry.M) from
      by rw [normalizer_eq_top]; trivial)) (eM x)
  · intro x
    constructor
    · intro hx
      let a : C D := ⟨x, hE hx⟩
      have ha := (hcentral a).mp hx
      rw [show dM x = RecognitionGeometry.VertexExtension.centralInclusion (dC a) from hres a]
      exact ha
    · intro hx
      let b : RecognitionGeometry.VertexExtension.C := ⟨dM x, Target.edge_le_centralizer hx⟩
      obtain ⟨a, ha⟩ := dC.surjective b
      have hax : (⟨a, C_le_M D a.property⟩ : M D) = x := by
        apply dM.injective
        rw [hres, ha]
        rfl
      rw [← hax]
      apply (hcentral a).mpr
      rw [ha]
      exact hx

/-- The edge-preserving comparison on the two literal uniqueness systems. -/
theorem vertex_edge_comparison (D : Seed G) :
    ∃ e : (sourceSystem D).vertexGroup ≃* ConcreteSystem.system.vertexGroup,
      (∀ a : (sourceSystem D).vertexGroup,
        (a : G) ∈ D.X ↔ (e a : Carrier) ∈ RecognitionGeometry.X) ∧
      (∀ a : (sourceSystem D).vertexGroup,
        (a : G) ∈ (sourceSystem D).edgeGroup ↔
          (e a : Carrier) ∈ ConcreteSystem.system.edgeGroup) := by
  obtain ⟨_, eM, _, hX, hE⟩ := edge_comparison D (sourceFrame D)
  have hsource : (sourceSystem D).vertexGroup = M D :=
    D.stabilizer_eq_normalizer D.base
  let e := (MulEquiv.subgroupCongr hsource).trans
    (eM.trans (MulEquiv.subgroupCongr ConcreteSystem.system_vertexGroup.symm))
  refine ⟨e, fun a => hX (MulEquiv.subgroupCongr hsource a), ?_⟩
  intro a
  rw [ConcreteSystem.system_edgeGroup]
  exact hE (MulEquiv.subgroupCongr hsource a)

end CFSG.Quasithin.Janko23.J2Recognition.SourceComparison
