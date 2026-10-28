module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.BlockRecognition.SourceModels
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.SourceImageNormal
public import Theory.GroupTheory.CommutatorPreimage
/-!
# The auxiliary block lies in the original C.5.12 module

The source identity U(L)=[P₁,L] and [P₁,K]≤U(K) place U(L) inside any
X-invariant subgroup containing U(K), in particular the original full orbit
span V. The commutator-preimage argument preserves the two different orbit
spans used in C.5.12 and C.5.13.
Source: Aschbacher–Smith C.5.12, printed p.163.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]
theorem noncubic_auxiliary_blockU_le_source_module
    (K T X V : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hXV : X ≤ normalizer (V : Set G)) (hUV : U K ≤ V) :
    U (conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G))) ≤ V := by
  let A := K ⊔ T
  let C := A.pCoreIn 2
  let N := X ⊓ normalizer (C : Set G)
  let L := conjugateSpanBy K N
  have hm := DualOffender.noncubic_source_moved_core K T X hK h3 hT hUT hTK P hP hA hAX S hS
  have hu : U L = ⁅C,L⁆ := hm.2.2.2.2.symm.trans hm.2.2.1
  have hKN : K ≤ N := le_inf (le_sup_left.trans hAX)
    (le_sup_left.trans (A.le_normalizer.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A))))
  have hNV : N ≤ normalizer (V : Set G) := inf_le_left.trans hXV
  have hPC : C ≤ centralizer (U K : Set G) :=
    (CounterexampleCharacteristic.ReducedMarking.normal_short_extension_centralizer K T hK.chi.short hT hTK).ge.trans inf_le_right
  have hPK : ⁅K,C⁆ ≤ V := (block_fixer_displacement hK.chi.short
    ((pCoreIn_le 2 A).trans (sup_le K.le_normalizer hTK)) hPC).trans hUV
  let W := commutatorPreimage N C V
  have hKW : K ≤ W := le_commutatorPreimage hKN hPK
  have hNW : N ≤ normalizer (W : Set G) :=
    commutatorPreimage_normalized N C V N hNV N.le_normalizer inf_le_right hNV
  have hLW : L ≤ W := conjugateSpanBy_le hKW hNW
  rw [hu,commutator_comm]
  exact (commutator_mono hLW le_rfl).trans (commutator_commutatorPreimage_le N C V hNV)
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
