module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.PushingUpReduction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.OrdinaryModels
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.ConstrainedField

/-!
# Surviving quotient models of the nonbinary pushing-up configuration

Apply the ordinary local exclusions and the constrained field calculation
to the original inclusion-compatible covering pair. Ordinary components
have only Ree, Tits or sporadic central quotients left. The constrained
component has star image SL₅(2), and the original source quotient is the
full SL₃(4), whose cubic center is retained. All selected subgroups and
the original module remain in their original ambient group.

These remaining cases still require exclusion. Source applies this reduction
to the literal Hall kernel; final normalizer control remains with this task.
Source: Aschbacher--Smith C.3.1, C.4.8 and 4.4.6, pp.149--154,620.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The literal configuration with its surviving actual quotient models. -/
def PushingUpClassifiedCase (L V A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G,
    PushLE L (oddActorResidual L A) J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
    H ⊓ normalizer (L : Set G) < H ∧ V ≤ J.pCoreIn 2 ∧
    let B := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let M := H ⊓ normalizer (L : Set G)
    let R := J.pCoreIn 2
    ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W ∧
    (L : Set G) = (B : Set G) * (L.pCoreIn 2 : Set G) ∧
    (B.subgroupOf M).Normal ∧
    (∃ e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L),
      ∀ b : B, e (QuotientGroup.mk' (pCore 2 B) b) =
        QuotientGroup.mk' (pCore 2 L)
          (inclusion ((map_subtype_le _).trans inf_le_left) b)) ∧
    ¬ ExceptionalQuotient (B ⧸ pCore 2 B) ∧ 64 ≤ Nat.card W ∧
    (∃ c : sectionCentralizerIn (normalizer (L : Set G)) L,
      V.map (MulAut.conj (c : G)).toMonoidHom ≤ W) ∧
    ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      ¬ K ≤ M.subgroupOf H ∧ B ≤ normalizer (K.map H.subtype : Set G) ∧ K.Normal ∧
      ((IsComponent H K ∧ B.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K ∧
          OrdinaryRemainder (K ⧸ center K)) ∨
        (generalizedFitting K = pCore 2 K ∧
          Input KnownSimple.IsKnownSimple H R M (K.map H.subtype) ∧
          Nonempty (starImage (K.map H.subtype) R (K.map H.subtype) ≃*
            Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∧
          (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
            Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) F)) ∧
          Nat.card (center (L ⧸ pCore 2 L)) = 3))

include D S
/-- Both model calculations apply to the actual component of the same H. -/
theorem pushingUp_classified_case {A : Subgroup G} (hc : PushingUpReducedCase L V A) :
    PushingUpClassifiedCase L V A := by
  obtain ⟨J,H,W,hpush,hH,hJH,hstrict,hVJ,hC,hcover,hN,he,hno,hsize,hVW,
    K,hK,hq,hout,hn,hnormal,hcases⟩ := hc
  obtain ⟨e,he⟩ := he
  refine ⟨J,H,W,hpush,hH,hJH,hstrict,hVJ,hC,hcover,hN,⟨e,he⟩,hno,hsize,hVW,
    K,hK,hq,hout,hn,hnormal,?_⟩
  rcases hcases with ⟨ho,hB,hW⟩ | ⟨hfK,hinput,es⟩
  · exact Or.inl ⟨ho,hB,hW,ordinary_natural_models D S hC e K ho⟩
  · obtain ⟨hf,em,hz⟩ := constrained_natural_field_four D S hC hN e K hK hq hout hfK
    refine Or.inr ⟨hfK,hinput,es,⟨S.field.Carrier,inferInstance,inferInstance,?_,em⟩,hz⟩
    rw [S.field.card_eq,hf]
    decide

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
