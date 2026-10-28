module
public import Theory.SpecificGroups.G2.RootPresentationRecognition.PositivePresentation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.MarkedLocal

/-!
# Positive G₂ presentation on the literal marked source quotient

Six additive roots satisfying the A–F equations and generating the specified
split U give a surjection from the actual model unipotent subgroup onto U.
The supplied original/geometric marking pulls this map back to the original
common Sylow. Both original endpoint embeddings agree with the same quotient
formula, and the source Sylow has order at most q⁶.

This discharges the positive collection step for the G₂ row of DGS, Groups
and Graphs, Theorem D, p.224. The numerator can be the infinite universal
completion; no descent to the original generated ambient group is used.
The source recognition owner still constructs the compatible root equations
and their positive generation. The full presentation, Borel and parabolic
comparison remain separate obligations in this same theorem family.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Atlas.G2.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.G2Presentation
variable {G X F : Type*} [Group G] [Group X] [Field F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (roots : PositiveRoots F (X ⧸ Q.D)) (rels : roots.CharTwoRelations)
  (hU : roots.generated = split.U)

/-- The constructed map on the same quotient that carries B,N and the endpoints. -/
def quotientUnipotentHom : Atlas.G2.unipotent (K := F) →* split.U :=
  (roots.unipotentHom rels.collection).codRestrict split.U (fun u => by
    rw [← hU, ← roots.unipotentHom_range rels.collection]
    exact ⟨u,rfl⟩)

/-- Each literal positive word uses exactly its original six parameters. -/
@[simp] theorem quotientUnipotentHom_product (t : Fin 6 → F) :
    (quotientUnipotentHom Q split roots rels hU (Atlas.G2.unipotentEquiv t) : X ⧸ Q.D) =
      roots.product t := roots.unipotentHom_product rels.collection t

theorem quotientUnipotentHom_surjective :
    Function.Surjective (quotientUnipotentHom Q split roots rels hU) := by
  intro u
  have hu : (u : X ⧸ Q.D) ∈ roots.generated := hU.symm ▸ u.property
  obtain ⟨t,ht⟩ := (roots.mem_generated_iff rels.collection u).mp hu
  exact ⟨Atlas.G2.unipotentEquiv t, Subtype.ext
    ((quotientUnipotentHom_product Q split roots rels hU t).trans ht)⟩

/-- The proved positive presentation evaluates into this exact source quotient. -/
def positiveEvaluation : PositivePresentation.Presentation F →* X ⧸ Q.D :=
  PositivePresentation.lift roots rels.collection

@[simp] theorem positiveEvaluation_product (t : Fin 6 → F) :
    positiveEvaluation Q roots rels ((PositivePresentation.roots (F := F)).product t) =
      roots.product t := PositivePresentation.lift_product roots rels.collection t

include hU in
/-- The positive presented words generate the whole specified U, with no model
homomorphism supplied as an input. -/
theorem positiveEvaluation_range : (positiveEvaluation Q roots rels).range = split.U := by
  rw [← hU]
  apply le_antisymm
  · rintro g ⟨p,rfl⟩
    obtain ⟨t,rfl⟩ := PositivePresentation.normalForm p
    rw [positiveEvaluation_product]
    exact roots.product_mem_generated t
  · intro g hg
    obtain ⟨t,rfl⟩ := (roots.mem_generated_iff rels.collection g).mp hg
    exact ⟨PositivePresentation.roots.product t, positiveEvaluation_product Q roots rels t⟩

variable
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S)

private theorem sylowMap_injective : Function.Injective (MarkedLocal.sylowMap Q e h) := by
  let b : commonBorel L S ≃* Q.tits.B :=
    (MulEquiv.subgroupCongr (lemma_F_1_3_6 h).symm).trans e.middle
  exact Q.tits.B.subtype_injective.comp
    (b.injective.comp (inclusion_injective (show S ≤ commonBorel L S from le_sup_right)))

/-- The existing whole-overlap marking identifies the original Sylow with U. -/
def sourceSylowEquiv : S ≃* split.U :=
  (MonoidHom.ofInjective (by exact sylowMap_injective Q e h)).trans
    (MulEquiv.subgroupCongr (MarkedLocal.sylow_range Q e h split))

@[simp] theorem sourceSylowEquiv_apply (s : S) :
    (sourceSylowEquiv Q split e h s : X ⧸ Q.D) = MarkedLocal.sylowMap Q e h s := rfl

/-- Positive presentation evaluation pulled through the actual original marking. -/
def sourceSylowHom : Atlas.G2.unipotent (K := F) →* S :=
  (sourceSylowEquiv Q split e h).symm.toMonoidHom.comp
    (quotientUnipotentHom Q split roots rels hU)

theorem sourceSylowHom_surjective :
    Function.Surjective (sourceSylowHom Q split roots rels hU e h) :=
  (sourceSylowEquiv Q split e h).symm.surjective.comp
    (quotientUnipotentHom_surjective Q split roots rels hU)

/-- The same quotient map is used after pullback to the original common Sylow. -/
theorem sourceSylowHom_quotient (u : Atlas.G2.unipotent (K := F)) :
    MarkedLocal.sylowMap Q e h (sourceSylowHom Q split roots rels hU e h u) =
      roots.unipotentHom rels.collection u := by
  have he := (sourceSylowEquiv Q split e h).apply_symm_apply
    (quotientUnipotentHom Q split roots rels hU u)
  exact congrArg Subtype.val he

/-- Both original endpoint embeddings commute on every positive word. -/
theorem sourceSylowHom_endpoint (i : Fin 2) (t : Fin 6 → F) :
    let s := sourceSylowHom Q split roots rels hU e h (Atlas.G2.unipotentEquiv t)
    MarkedLocal.endpointMap Q e i
      ⟨s, (show S ≤ parabolic L S i from le_sup_right.trans le_sup_left) s.property⟩ =
        roots.product t := by
  dsimp only
  rw [MarkedLocal.endpoint_sylow Q e h i, sourceSylowHom_quotient,
    PositiveRoots.unipotentHom_product]

include rels hU e h in
/-- A numerical source consequence of the proved positive collection. -/
theorem sourceSylow_card_le [Finite F] : Nat.card S ≤ Nat.card F ^ 6 := by
  rw [← Atlas.G2.card_unipotent]
  exact Nat.card_le_card_of_surjective (sourceSylowHom Q split roots rels hU e h)
    (sourceSylowHom_surjective Q split roots rels hU e h)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.G2Presentation
