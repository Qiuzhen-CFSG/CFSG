module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.G2.Geometry.Automorphisms
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.G2.Flag

/-!
# Transport from the whole intrinsic module to the ambient group

The coordinate embedding is the literal composite through U(K) and K ≤ G.
The component action uses the given K/O₂(K) marking. A normalizer element
acts through K's normalizer conjugation map, so full model operators obtained
on U(K) transport to its actual ambient conjugation with no global normality
assumption on K.

Source: the G₂ flag calculation in Aschbacher--Smith, original 14.6.10(5),
printed p.1029.
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.G2SecondParabolic
open ChapterC Atlas.G2 Atlas.G2.Natural
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
variable (K : Subgroup G) [IsElementaryAbelian 2 (blockU K)]

/-- Coordinates on the whole U, embedded through the actual subgroup K of G. -/
def coordinateEmbedding (E : W ≃ₗ[ZMod 2] Additive (blockU K)) : Multiplicative W →* G :=
  (K.subtype.comp (blockU K).subtype).comp E.toAddEquiv.toMultiplicativeLeft.toMonoidHom

theorem coordinateEmbedding_injective (E : W ≃ₗ[ZMod 2] Additive (blockU K)) :
    Function.Injective (coordinateEmbedding K E) :=
  K.subtype_injective.comp ((blockU K).subtype_injective.comp E.injective)

theorem coordinateEmbedding_range (E : W ≃ₗ[ZMod 2] Additive (blockU K)) :
    (coordinateEmbedding K E).range = (blockU K).map K.subtype := by
  apply le_antisymm
  · rintro _ ⟨w,rfl⟩
    exact ⟨(E w.toAdd).toMul, (E w.toAdd).toMul.property, rfl⟩
  · rintro _ ⟨u,hu,rfl⟩
    refine ⟨Multiplicative.ofAdd (E.symm (Additive.ofMul ⟨u,hu⟩)), ?_⟩
    change ((E (E.symm (Additive.ofMul ⟨u,hu⟩))).toMul : G) = u
    rw [E.apply_symm_apply]
    rfl

/-- The model actor is the original quotient by the two-core. -/
def coordinateActor (m : BlockModuleModel K g2TwoNaturalAction) :
    K →* commutator (Model (ZMod 2)) :=
  m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))

omit [IsElementaryAbelian 2 (blockU K)] in
theorem coordinateActor_surjective (m : BlockModuleModel K g2TwoNaturalAction) :
    Function.Surjective (coordinateActor K m) :=
  m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)

theorem coordinateEmbedding_component
    (h : IsShort K) (m : BlockModuleModel K g2TwoNaturalAction)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W)
    (E : W ≃ₗ[ZMod 2] Additive (blockU K))
    (hE : ∀ x w, E (ρ x.val w) = intrinsicAction h m x (E w))
    (x : K) (w : W) :
    coordinateEmbedding K E (Multiplicative.ofAdd (ρ (coordinateActor K m x).val w)) =
      x.val * coordinateEmbedding K E (Multiplicative.ofAdd w) * x.val⁻¹ := by
  have he := hE (coordinateActor K m x) w
  change E _ = intrinsicAction h m (m.quotientIso (QuotientGroup.mk' (pCore 2 K) x)) (E w) at he
  rw [intrinsicAction_apply] at he
  exact congrArg (fun v : Additive (blockU K) => ((v.toMul : K) : G)) he

/-- An actual normalizer of K acts by a full model operator on these same coordinates. -/
theorem coordinateEmbedding_normalizer {V Z J : Subgroup G} (d : FlagData K V Z J)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W)
    (E : W ≃ₗ[ZMod 2] Additive (blockU K))
    (hE : ∀ a : MulAut K, ∃ g : Model (ZMod 2), ∀ w,
      E (ρ g w) = intrinsicAut a (E w)) :
    ∀ j ∈ J, ∃ g : Model (ZMod 2), ∀ w,
      coordinateEmbedding K E (Multiplicative.ofAdd (ρ g w)) =
        j * coordinateEmbedding K E (Multiplicative.ofAdd w) * j⁻¹ := by
  intro j hj
  obtain ⟨g,hg⟩ := hE (K.normalizerMonoidHom ⟨j,d.normalizes hj⟩)
  exact ⟨g,fun w => congrArg (fun v : Additive (blockU K) => ((v.toMul : K) : G)) (hg w)⟩

end CFSG.Quasithin.Chapter14.Section06.G2SecondParabolic
