module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.MovedNaturalNormalizer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.MovedJankoPlacements

/-!
# Conditional assembly from the uniform native J₄ normalizer cover

The cover used here concerns every nonzero elementary subgroup of the actual
J₄ carrier. Its rows are the fixed Mathieu, first-centralizer and
symmetric-linear locals, and an embedded subgroup C with its actual L₅(2)
quotient. Conjugation transports that quotient through the same embedding.
Applying the cover to the image of the original V, and using N(V image) =
N(residual image), contradicts the four previously proved local exclusions.

The independent ordinary input retains the full C.2.8 module W, the covering
residual B and its inclusion-compatible quotient. Its application below uses
the original pushing-up witness; it makes no identification of W with V.

This is a conditional assembly, not a proof of either input. The uniform
native cover and its embedded max3 quotient belong to
qt-model-j4-elementary-normalizer-cover, with intrinsic symmetry supplied by
qt-model-j4-large-center-radicals. The ordinary full-W exclusion belongs to
qt-d-1222-natural-point-fixed-summand. Final discharge remains with
qt-d-1222-natural-odd-kernel-normalizer.

Source: Aschbacher--Smith, 4.4.3 and Remark 4.4.2, printed pp.619--623;
Kleidman--Wilson (1988), Section 2, pp.488--493.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The uniform earlier native theorem, with fixed named locals and an actual
embedded third local. The quotient of C is supplied separately. -/
def NativeElementaryNormalizerCover (C : Subgroup Janko4.Model) : Prop :=
  ∀ E : Subgroup Janko4.Model, E ≠ ⊥ → IsElementaryAbelian 2 E →
    (∃ g : Janko4.Model, normalizer (E : Set Janko4.Model) ≤
      (Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self
        Janko4.matrixB_pow_four).map (MulAut.conj g).toMonoidHom) ∨
    (∃ g : Janko4.Model, normalizer (E : Set Janko4.Model) ≤
      Janko4.InvolutionCentralizers.First.centralizer.map (MulAut.conj g).toMonoidHom) ∨
    (∃ g : Janko4.Model, normalizer (E : Set Janko4.Model) ≤
      C.map (MulAut.conj g).toMonoidHom) ∨
    (∃ g : Janko4.Model, normalizer (E : Set Janko4.Model) ≤
      Janko4.LocalStructure.SymmetricLinear.max4Subgroup.map (MulAut.conj g).toMonoidHom)

/-- Transport the actual third-local quotient through the cover's conjugator.
The other three rows are exactly the existing fixed native embeddings. -/
theorem native_containment_of_elementary_cover
    (C : Subgroup Janko4.Model) (eC : (C ⧸ pCore 2 C) ≃* PSL(5,ZMod 2))
    (hcover : NativeElementaryNormalizerCover C)
    (E : Subgroup Janko4.Model) (hne : E ≠ ⊥) (he : IsElementaryAbelian 2 E) :
    NativeJankoLocalContainment (normalizer (E : Set Janko4.Model)) := by
  rcases hcover E hne he with h | h | ⟨g,h⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · let t := (MulAut.conj g).subgroupMap C
    let q := t.toMonoidHom.quotientPCoreEquivOfSurjective t.surjective
      (by rw [t.toMonoidHom.ker_eq_bot t.injective]; exact IsPGroup.of_subsingleton 2 _)
    exact Or.inr (Or.inr (Or.inr ⟨C.map (MulAut.conj g).toMonoidHom,h,
      ⟨q.symm.trans eC⟩⟩))
  · exact Or.inr (Or.inr (Or.inl h))

open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The uniform cover excludes the original moved-inner configuration. The
elementary subgroup is the image of V under the literal component quotient;
the full normalizer equality supplies precisely the excluded placement. -/
theorem moved_janko_false_of_elementary_cover
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (C : Subgroup Janko4.Model) (eC : (C ⧸ pCore 2 C) ≃* PSL(5,ZMod 2))
    (hcover : NativeElementaryNormalizerCover C)
    {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (K : Subgroup (normalizer (A : Set G)))
    (hFK : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (hf : S.field.degree = 2) (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (ek : (K ⧸ center K) ≃* Janko4.Model) : False := by
  let U := (movedComponentSubgroup A V K).map (QuotientGroup.mk' (center K))
  obtain ⟨hU,hne,_,_⟩ := moved_projected_module D S hA hodd K hFK
  have he : IsElementaryAbelian 2 (U.map ek.toMonoidHom) := by
    let : IsElementaryAbelian 2 U := hU
    exact IsElementaryAbelian.map ek.toMonoidHom
  have hneJ : U.map ek.toMonoidHom ≠ ⊥ := by
    intro hz
    exact hne ((U.map_eq_bot_iff_of_injective ek.injective).mp hz)
  have hc := native_containment_of_elementary_cover C eC hcover _ hneJ he
  have hn := moved_janko_module_normalizer D S hA hodd hu K hFK hf e ek
  rw [←hn] at hc
  exact moved_janko_normalizer_avoids_native_locals D S hA hodd hu K hFK hf e ek hc

/-- The shared ordinary theorem still owed by the fixed-summand owner.
It quantifies over full W and actual covering residuals, with relative
normality and the literal quotient map. No source-specific normalizer
conclusion, shortness, W=V or order bound on W occurs in this interface. -/
def OrdinaryFullModuleExclusion (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput) : Prop :=
  ∀ {H M B R W : Subgroup G},
    ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W →
    M < H → (B.subgroupOf M).Normal → ∀ hBL : B ≤ L,
    (L : Set G) = (B : Set G) * (L.pCoreIn 2 : Set G) → V ≤ B.pCoreIn 2 →
    ∀ e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L),
    (∀ b : B, e (QuotientGroup.mk' (pCore 2 B) b) =
      QuotientGroup.mk' (pCore 2 L) (inclusion hBL b)) →
    S.field.degree = 2 → ((L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) →
    ∀ K : Subgroup H, IsComponent H K → ((K ⧸ center K) ≃* Janko4.Model) → False

/-- Apply the shared full-W theorem to the original pushing-up covering
residual. The Ru alternative uses the already proved full-cover obstruction. -/
theorem pushingUpFieldFourCase_false_of_ordinary
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (hordinary : OrdinaryFullModuleExclusion D S) {A : Subgroup G}
    (hpush : PushingUpFieldFourCase D S A) : False := by
  obtain ⟨J,H,W,_,_,_,hstrict,_,h,hproduct,hn,hVB,⟨e,he⟩,_,_,_,hf,⟨a⟩,_,
    K,hK,_,_,_,_,hmodel⟩ := hpush
  have hBL := (map_subtype_le (solvableResidual (L ⊓ H : Subgroup G))).trans inf_le_left
  rcases hmodel with hj | hr
  · exact hordinary h hstrict hn hBL hproduct hVB e he hf a K hK hj.some
  · exact Normalizers.FixedSummand.Centralizer.no_ordinary_rudvalis_field_four
      D S h e hf a K hK hr.some

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
