module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.PushingUpComponents
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.ConstrainedModels

/-!
# The remaining pushing-up components for the nonbinary source

Apply the constrained-model exclusions to the actual covering residual and
the selected component. The latter is normal in H. It is either an ordinary
component containing the residual and module, or a constrained component
whose actual star image is SL₅(2). The compatible covering map, original V
and its section-centralizer conjugate, and the module order bound are retained.

This reduces the remaining pushing-up analysis; it does not exclude the
ordinary or binary-five cases. The odd-normalizer owner retains those proofs.
The source endpoint applies the reduction to the actual Hall kernel.

Source: Aschbacher--Smith C.3.1 and C.4.1--8, printed pp.149--154,
and their application in 4.4.6, printed p.620.
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

/-- The unchanged source configuration with only the remaining component rows. -/
def PushingUpReducedCase (L V A : Subgroup G) : Prop :=
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
      ((IsComponent H K ∧ B.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K) ∨
        (generalizedFitting K = pCore 2 K ∧
          Input KnownSimple.IsKnownSimple H R M (K.map H.subtype) ∧
          Nonempty (starImage (K.map H.subtype) R (K.map H.subtype) ≃*
            Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))))

include D S
/-- Apply the model exclusions to the literal inclusion-compatible covering pair. -/
theorem pushingUp_reduced_case {A : Subgroup G} (hc : PushingUpComponentCase L V A) :
    PushingUpReducedCase L V A := by
  obtain ⟨J,H,W,hpush,hH,hJH,hstrict,hVJ,hC,hcover,hN,he,hno,hsize,hVW,
    K,hK,hq,hout,hn,hcases⟩ := hc
  obtain ⟨e,he⟩ := he
  refine ⟨J,H,W,hpush,hH,hJH,hstrict,hVJ,hC,hcover,hN,⟨e,he⟩,hno,hsize,hVW,
    K,hK,hq,hout,hn,?_⟩
  rcases hcases with ⟨ho,hnormal,hB,hW⟩ | ⟨hfK,hinput,hmodel⟩
  · exact ⟨hnormal,Or.inl ⟨ho,hB,hW⟩⟩
  · obtain ⟨es⟩ := constrained_natural_star_linear_five_two D S hC hN e K hK hq hout hfK
    exact ⟨constrained_linear_five_two_normal hC K hK hq hout hfK es,
      Or.inr ⟨hfK,hinput,⟨es⟩⟩⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
