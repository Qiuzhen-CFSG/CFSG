module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition.ParabolicSeed
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.SourceGeneration
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition
public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts

/-!
# From the original residual chief flag to Steinberg in 14.7.72

The source chief flag is a flag for the actual L₁ action on S/V. The marked
residual image supplies a surjective change of actor, preserving exactly the
invariant subspaces and their central sections. The source marking and original
U/V action construct the cyclic parabolic seed. The five proved model counts
then recognize Steinberg, and its automorphism invariance returns coordinates
for the original qL. This supplies the center equality in the special group.

The three-factor flag remains the exact independent consequence of 14.7.71.
It is not a dimension tag or a Steinberg premise; no containment S≤L₁ is used.
Source: Aschbacher–Smith, 14.7.22(2), 14.7.71–72 and H.6.5, printed p.1076.
-/

@[expose] public section
noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.ParabolicSteinberg
open Chapter12.Section08 CriticalFusion.Source
open SteinbergRecognition SteinbergRecognition.ModuleRecognition
open SteinbergRecognition.ModuleRecognition.ParabolicSeed
open BinaryLinearThree.ParabolicCyclic BinaryLinearThree.ParabolicCyclic.ChiefCounts

private theorem count_of_reindex {A B M : Type*} [Group A] [Group B]
    [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Representation (ZMod 2) A M) (f : B →* A) (hf : Function.Surjective f)
    {n : ℕ} (h : HasCount (ρ.comp f) n) : HasCount ρ n := by
  obtain ⟨s, hs0, hs1, hsc⟩ := h
  let e := reindexOrderIso ρ f hf
  let t : Series ρ := ⟨s.length, fun i => e.symm (s i),
    fun i => (apply_covBy_apply_iff e.symm).mpr (s.step i)⟩
  refine ⟨t, ?_, ?_, ?_⟩
  · change e.symm s.head = ⊥
    rw [hs0, OrderIso.map_bot]
  · change e.symm s.last = ⊤
    rw [hs1, OrderIso.map_top]
  · have ht : t.count = s.count := by
      apply Nat.card_congr
      apply Equiv.subtypeEquivRight
      intro i
      exact not_congr ((central_reindex ρ f hf (t i.castSucc) (t i.succ)).symm)
    exact ht.trans hsc

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

/-- The unchanged source quotient, restricted to the actual residual L₁. -/
def sourceActor : F.Li L 1 →* BinaryLinearThree.Group :=
  d.qL.comp (inclusion ((F.Li_le L 1).trans inf_le_left))

/-- The marked residual image, with the exact inverse point/line twist. -/
def markedActor (b : Marking d) : F.Li L 1 →* actor where
  toFun l := ⟨b.twist.symm (sourceActor d l), by
    rw [actor, ← b.residual d]
    exact ⟨inclusion ((F.Li_le L 1).trans inf_le_left) l, l.property, rfl⟩⟩
  map_one' := Subtype.ext (by simp [sourceActor])
  map_mul' x y := Subtype.ext (by simp [sourceActor])

theorem markedActor_surjective (b : Marking d) : Function.Surjective (markedActor d b) := by
  intro g
  have hg := g.property
  change g.val ∈ (pResidual 2 Matrix.PSL3Two.lineParabolicSL).map Matrix.PSL3Two.lineParabolicSL.subtype at hg
  rw [← b.residual d] at hg
  obtain ⟨l, hl, he⟩ := hg
  exact ⟨⟨l, hl⟩, Subtype.ext he⟩

variable [(V.subgroupOf (S F L)).Normal]
  [IsElementaryAbelian 2 (S F L ⧸ V.subgroupOf (S F L))]

/-- Changing the actor retains the precise source action, not just its image. -/
theorem markedActor_action (a : QuotientAction d) (b : Marking d) :
    (((a.representation.comp b.twist.toMonoidHom).comp actor.subtype).comp
      (markedActor d b)) = a.representation.comp (sourceActor d) := by
  apply MonoidHom.ext
  intro l
  apply LinearMap.ext
  intro v
  change a.representation (b.twist (b.twist.symm (sourceActor d l))) v = _
  rw [b.twist.apply_symm_apply]
  rfl

/-- A complete actual chief flag for the original L₁ action has the same
noncentral count after the proved surjective point/line actor change. -/
theorem marked_count (a : QuotientAction d) (b : Marking d) {n : ℕ}
    (h : HasCount (a.representation.comp (sourceActor d)) n) :
    HasCount ((a.representation.comp b.twist.toMonoidHom).comp actor.subtype) n := by
  apply count_of_reindex _ (markedActor d b) (markedActor_surjective d b)
  rw [markedActor_action d a b]
  exact h

/-- The parabolic seed is constructed from the original module and the
source marking. Only the actual three-factor chief flag remains from 14.7.71. -/
theorem recognized_of_source_count (a : QuotientAction d)
    (hTL : (T : Subgroup G) ≤ normalizer L)
    (hs : d.ModuleSeparation) (hU₀ : d.U₀ = F.Vi 1)
    (hcount : HasCount (a.representation.comp (sourceActor d)) 3) :
    Nonempty (SteinbergCoordinates d) := by
  obtain ⟨b⟩ := nonempty_marking d hTL
  have hlocal := LocalAction.localTransitive d a hs hU₀ hTL
  obtain ⟨s, _, _, hfixed, hgen, hdim⟩ :=
    exists_seed_of_local_transitive d b a hs hU₀ hlocal
  obtain ⟨t, ht0, ht1, htc⟩ := marked_count d a b hcount
  obtain ⟨e⟩ := recognition_of_three_noncentral_sections
    (a.representation.comp b.twist.toMonoidHom) (quotientCoordinates s).toAdd
      hfixed hgen hdim t ht0 ht1 htc
  exact ⟨a.steinbergCoordinatesOfTwist d b.twist e⟩

omit [(V.subgroupOf (S F L)).Normal]
  [IsElementaryAbelian 2 (S F L ⧸ V.subgroupOf (S F L))] in
/-- Apply the generation proof and the constructed recognition to all three
special-group layers. The source count is on the canonical quotient action
and its literal L₁ homomorphism. Neither recognition nor center equality is
an input. The earlier generation and 14.7.71 producers retain their premises. -/
theorem special_equalities_of_source_count
    (c : CriticalPath (L := L) F) (e : SourceGeneration.Earlier d c)
    (hcount : let h := SourceGeneration.generation d c e
      let := quotient_normal h.frattini_eq
      let := quotient_elementary e.span_le_Q h.frattini_eq
      HasCount ((quotientAction d e.sylow_normalizes h.core_commutator.le).representation.comp
        (sourceActor d)) 3) :
    Nonempty (SteinbergCoordinates d) ∧
      (center (S F L)).map (S F L).subtype = V ∧
      (frattini (S F L)).map (S F L).subtype = V ∧ ⁅S F L, S F L⁆ = V := by
  let h := SourceGeneration.generation d c e
  let := quotient_normal h.frattini_eq
  let := quotient_elementary e.span_le_Q h.frattini_eq
  obtain ⟨s⟩ := recognized_of_source_count d
    (quotientAction d e.sylow_normalizes h.core_commutator.le)
    e.sylow_normalizes e.critical.separation h.fixed_kernel hcount
  exact ⟨⟨s⟩, center_eq_of_steinberg d s h.seed_central h.derived_eq,
    h.frattini_eq, h.derived_eq⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.ParabolicSteinberg
