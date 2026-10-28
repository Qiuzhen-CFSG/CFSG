module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ProjectionEscape.NormalizerStructure
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Centers.MinimalParabolics.NaturalGeometry.MarkedGeneration

/-!
# The marked normalizer projection for the original source flag

The existing full-natural-action flag theorem chooses a basis whose first
cuts are exactly the original Vi. Conjugating the source quotient equivalence
by its coordinate map identifies the actual L-stabilizers of V₁ and V₂ with
the standard point and plane parabolics in SL₃(2). The original T ∩ L is
Sylow in L because L is relatively normal in M=N_G(L); its quotient image
lies in the standard Borel and Sylow maximality proves equality.

These three identities discharge every flag premise of the genuine ambient
projection construction in NormalizerStructure. The resulting
`nonempty_of_source` uses only Source.Data and the complete universal
Structural1222 contract. Its applicability comes from the original natural
setup; qt-12-02-reduction is the producer of that earlier source implication.
It has no CriticalPath, Geometry, CoreFacts or Y-containment premise.

The final theorems apply the resulting projection to the original projection,
normalizer-escape and Thompson consumers. Their independent finite-model,
geometry and earlier Thompson inputs stay with those source assembly owners;
no such inputs enter the projection's construction.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
Hypothesis 12.8.1 and Notation 12.8.2, printed pp.849–850;
Notation 14.7.1 and Lemma 14.7.70, printed pp.1043 and 1074.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ProjectionEscape.NormalizerStructure
open Chapter12.Section08 Matrix.PSL3Two Stellmacher
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
universe u

private theorem cut_coordinates (b : Basis 2) (i : Fin 2) (v : Space 3) :
    v ∈ cutSpace b i ↔ ∀ j : Fin 3, i.val < j.val → b.equivFun v j = 0 := by
  rw [cutSpace, Module.Basis.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Set.mem_ofPred_eq]
  change (∀ j : Fin 3, b.equivFun v j ≠ 0 → j.val ≤ i.val) ↔ _
  constructor
  · intro h j hj
    by_contra hv
    exact Nat.not_le_of_gt hj (h j hv)
  · intro h j hj
    by_contra hle
    exact hj (h j (Nat.lt_of_not_ge hle))

private theorem point_cut (b : Basis 2) (v : Space 3) :
    v ∈ cutSpace b 0 ↔ b.equivFun v 1 = 0 ∧ b.equivFun v 2 = 0 := by
  rw [cut_coordinates]
  constructor
  · intro h; exact ⟨h 1 (by decide),h 2 (by decide)⟩
  · rintro ⟨h1,h2⟩ j hj
    fin_cases j <;> simp_all

private theorem line_cut (b : Basis 2) (v : Space 3) :
    v ∈ cutSpace b 1 ↔ b.equivFun v 2 = 0 := by
  rw [cut_coordinates]
  constructor
  · intro h; exact h 2 (by decide)
  · intro h j hj
    fin_cases j <;> simp_all

private noncomputable def basisModel (b : Basis 2) : LinearGroup 3 ≃* SL :=
  (MulAut.conj b.equivFun).trans (slEquivLinear 3).symm

private theorem basisModel_act (b : Basis 2) (a : LinearGroup 3) (v : Space 3) :
    (basisModel b a).val.mulVec (b.equivFun v) = b.equivFun (a v) := by
  rw [← slEquivLinear_apply]
  change (slEquivLinear 3) ((slEquivLinear 3).symm ((MulAut.conj b.equivFun) a))
    (b.equivFun v) = _
  rw [MulEquiv.apply_symm_apply]
  change b.equivFun (a (b.equivFun.symm (b.equivFun v))) = _
  rw [b.equivFun.symm_apply_apply]

private theorem basisModel_point (b : Basis 2) (a : LinearGroup 3) :
    basisModel b a ∈ pointParabolicSL ↔ a ∈ parabolic (cutSpace b 0) := by
  rw [pointParabolicSL, MulAction.mem_stabilizer_set]
  change (∀ v : Space 3, _ ↔ _) ↔ ∀ v : Space 3, _ ↔ _
  constructor
  · intro h v
    have hv := h (b.equivFun v)
    change ((basisModel b a).val.mulVec (b.equivFun v) 1 = 0 ∧
      (basisModel b a).val.mulVec (b.equivFun v) 2 = 0) ↔ _ at hv
    rw [basisModel_act] at hv
    exact (point_cut b (a v)).trans (hv.trans (point_cut b v).symm)
  · intro h v
    obtain ⟨v,rfl⟩ := b.equivFun.surjective v
    have hv := h v
    rw [point_cut, point_cut] at hv
    change ((basisModel b a).val.mulVec (b.equivFun v) 1 = 0 ∧
      (basisModel b a).val.mulVec (b.equivFun v) 2 = 0) ↔ _
    rwa [basisModel_act]

private theorem basisModel_line (b : Basis 2) (a : LinearGroup 3) :
    basisModel b a ∈ lineParabolicSL ↔ a ∈ parabolic (cutSpace b 1) := by
  rw [lineParabolicSL, MulAction.mem_stabilizer_set]
  change (∀ v : Space 3, _ ↔ _) ↔ ∀ v : Space 3, _ ↔ _
  constructor
  · intro h v
    have hv := h (b.equivFun v)
    change ((basisModel b a).val.mulVec (b.equivFun v) 2 = 0) ↔ _ at hv
    rw [basisModel_act] at hv
    exact (line_cut b (a v)).trans (hv.trans (line_cut b v).symm)
  · intro h v
    obtain ⟨v,rfl⟩ := b.equivFun.surjective v
    have hv := h v
    rw [line_cut, line_cut] at hv
    change ((basisModel b a).val.mulVec (b.equivFun v) 2 = 0) ↔ _
    rwa [basisModel_act]

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

private theorem original_natural_action : letI := d.natural.chosen.elementary
    ∀ l : L, InvariantFlag.naturalFlagActorEquiv d.natural.naturalMarking.coordinates
      (setupSeedAction L V d.natural.chosen.normalizes l) =
        d.natural.naturalMarking.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) := by
  let := d.natural.chosen.elementary
  intro l
  apply LinearEquiv.ext
  intro v
  obtain ⟨v,rfl⟩ := d.natural.naturalMarking.coordinates.surjective v
  obtain ⟨v,rfl⟩ := Additive.ofMul.surjective v
  rw [InvariantFlag.naturalFlagActorEquiv_intertwines]
  exact d.natural.naturalMarking.equivariant l (Additive.ofMul v)

private theorem original_stabilizer_iff : letI := d.natural.chosen.elementary
    ∀ (l : L) (i : ℕ), (l : G) ∈ F.Gi i ↔
      d.natural.naturalMarking.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) ∈
        parabolic (F.naturalFlagSpace d.natural.naturalMarking.coordinates i) := by
  let := d.natural.chosen.elementary
  intro l i
  rw [← F.naturalFlagStabilizer_map, ← original_natural_action d,
    mem_map_equiv, MulEquiv.symm_apply_apply]
  exact (F.naturalFlagAction_mem_stabilizer L d.natural.chosen.normalizes i
    ⟨l,(le_sup_left : L ≤ L ⊔ (T : Subgroup G)) l.property⟩).symm

include d

/-- A quotient marking adapted to the very same original point and plane. -/
theorem exists_original_flag_marking
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    ∃ e : (L ⧸ pCore 2 L) ≃* SL,
      (((T : Subgroup G) ⊓ L).subgroupOf L).map
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) = borelSL ∧
      (F.Gi 1).subgroupOf L =
        pointParabolicSL.comap (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) ∧
      (F.Gi 2).subgroupOf L =
        lineParabolicSL.comap (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) := by
  let := d.natural.chosen.elementary
  let A := d.natural.naturalMarking
  obtain ⟨b,hb,hcuts⟩ := F.exists_naturalFlag_marking L d.natural.chosen.normalizes
    d.natural.full_L_action A.coordinates
  let e := A.quotientEquiv.trans (basisModel b)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hp (l : L) : (l : G) ∈ F.Gi 1 ↔ q l ∈ pointParabolicSL := by
    change _ ↔ basisModel b (A.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)) ∈ _
    rw [basisModel_point, ← hcuts 0]
    exact original_stabilizer_iff d l 1
  have hq (l : L) : (l : G) ∈ F.Gi 2 ↔ q l ∈ lineParabolicSL := by
    change _ ↔ basisModel b (A.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)) ∈ _
    rw [basisModel_line, ← hcuts 1]
    exact original_stabilizer_iff d l 2
  refine ⟨e,?_,?_,?_⟩
  · let M := normalizer (L : Set G)
    let LN := L.subgroupOf M
    let : LN.Normal := normal_subgroupOf_of_le_normalizer le_rfl
    obtain ⟨S,hS⟩ := (T.subtype (d.natural.sylow_normalizes structural)).exists_subgroupOf_eq_of_normal LN
    let a : LN ≃* L := subgroupOfEquivOfLe L.le_normalizer
    let S' : Sylow 2 L := S.mapSurjective (f := a.toMonoidHom) a.surjective
    have hS' : (S' : Subgroup L) = ((T : Subgroup G) ⊓ L).subgroupOf L := by
      ext l
      constructor
      · rintro ⟨x,hx,rfl⟩
        rw [hS] at hx
        exact ⟨hx,(a x).property⟩
      · intro hl
        refine ⟨a.symm l,?_,a.apply_symm_apply l⟩
        rw [hS]
        exact hl.1
    let P : Sylow 2 SL := S'.mapSurjective (f := q)
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
    have hP : (P : Subgroup SL) ≤ borelSL := by
      rintro x ⟨l,hl,rfl⟩
      rw [hS'] at hl
      exact ⟨(hp l).mp (F.invariant 1 hl.1), (hq l).mp (F.invariant 2 hl.1)⟩
    have heq := P.is_maximal' (IsPGroup.of_card (n := 3) card_borelSL) hP
    exact (congrArg (fun H : Subgroup L => H.map q) hS').symm.trans heq.symm
  · ext l; exact hp l
  · ext l; exact hq l

/-- Construct the genuine marked normalizer projection from the source data
and the earlier universal structural theorem. There is no critical-path,
Y-containment, local projection, or ambient-kernel hypothesis. -/
theorem nonempty_of_source
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    Nonempty (NormalizerProjection T L V F) := by
  obtain ⟨e,hB,hP,hQ⟩ := exists_original_flag_marking d structural
  exact nonempty_of_flag_marking d structural e hB hP hQ

/-- The source constructor supplies every field to the literal projection and
residual-action consumer; only its independent finite-model theorem remains. -/
theorem projection_and_noncentral_action_of_source
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (model : ParabolicImageTheorem.{u}) {c : CriticalPath (L := L) F}
    (h : Geometry d c) (k : CoreFacts c)
    (hYM : Y c ≤ normalizer (L : Set G)) :
    ∃ p : NormalizerProjection T L V F,
      ((Y c).subgroupOf (normalizer (L : Set G))).map p.project =
        ((F.Li L 2).subgroupOf (normalizer (L : Set G))).map p.project ∧
        ¬ (T : Subgroup G) ⊓ L ≤ centralizer (E c : Set G) := by
  obtain ⟨p⟩ := nonempty_of_source d structural
  exact ⟨p, projection_and_noncentral_action p model h k hYM⟩

/-- The genuine projection construction discharges the normalizer-escape
assembly's projection premise, with the model theorem still independent. -/
theorem normalizer_escape_of_source
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (model : ParabolicImageTheorem.{u}) {c : CriticalPath (L := L) F}
    (h : Geometry d c) (k : CoreFacts c) :
    ¬ Y c ≤ normalizer (L : Set G) := by
  obtain ⟨p⟩ := nonempty_of_source d structural
  exact normalizer_escape_of_projection p model h k

/-- Application to the original Thompson consumer, retaining precisely its
genuine earlier universal setup and Thompson-normality premises. -/
theorem thompson_escape_of_source
    (model : ParabolicImageTheorem.{u}) {c : CriticalPath (L := L) F}
    (h : Geometry d c) (k : CoreFacts c)
    (earlier : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (thompson : EarlierThompsonNormality.{u}) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ (I c).pCoreIn 2 := by
  obtain ⟨p⟩ := nonempty_of_source d earlier.structural
  exact thompson_escape_of_projection p model h k earlier thompson

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ProjectionEscape.NormalizerStructure
