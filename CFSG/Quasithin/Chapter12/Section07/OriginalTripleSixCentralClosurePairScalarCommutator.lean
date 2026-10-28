module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixScalarResidualContainment

/-!
# The scalar commutator of the original pair layer

The same original K-conjugator retains the entire denominator
N=(W∩Wᵍ)U and its normality in I=⟨W,Wᵍ⟩. The previous scalar
bound modulo N improves to [P,X]=U for P=[O₂(I),I]. The reverse
inclusion uses U=[U,I] and U=[U,X], both on the original chosen module.

Source: the first sentence of Aschbacher--Smith12.7.20, printed p.846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The full pair denominator is retained, while the actual scalar
commutator of its whole two-core layer is precisely the chosen module. -/
theorem original_tripleSix_central_closure_pair_scalar_commutator
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K) :
    let W := conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))
    ∃ g : K,
      let Wg := W.map (MulAut.conj (g : G)).toMonoidHom
      let I := W ⊔ Wg
      let N := ((W ⊓ Wg) ⊔ U).subgroupOf I
      let P := ⁅I.pCoreIn 2,I⁆
      K ≤ I ∧ I = K ⊔ W ∧ N.Normal ∧
        ⁅P,tripleSixScalarResidual K⁆ ≤ (W ⊓ Wg) ⊔ U ∧
        ⁅P,tripleSixScalarResidual K⁆ = U := by
  let W := conjugateSpanBy (tripleSixPoint D a z)
    (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))
  obtain ⟨g,hKI,hIe,hscalar⟩ :=
    original_tripleSix_central_closure_scalar h structural D a z hz hzT hnot houter
  let Wg := W.map (MulAut.conj (g : G)).toMonoidHom
  let I := W ⊔ Wg
  let M := K ⊔ (T : Subgroup G)
  let X := tripleSixScalarResidual K
  let P := ⁅I.pCoreIn 2,I⁆
  change K ≤ I at hKI
  change I = K ⊔ W at hIe
  have hWT : W ≤ (T : Subgroup G) :=
    (original_tripleSix_central_closure_automizer_cases h structural D a z hz hzT hnot).1
  have hc := original_tripleSix_central_closure_configuration h structural D a z hz hzT hnot
  have hTW : (T : Subgroup G) ≤ normalizer (W : Set G) := by
    have he := hc.2.1
    change W = _ at he
    rw [he]
    exact le_sup_right.trans (le_normalizer_conjugateSpanBy _ _)
  have hIM : I ≤ M := hIe.le.trans (sup_le le_sup_left (hWT.trans le_sup_right))
  have hMI : M ≤ normalizer (I : Set G) := by
    apply sup_le (hKI.trans I.le_normalizer)
    rw [hIe]
    exact (le_inf D.sylow_normalizes_component hTW).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hQM : I.pCoreIn 2 ≤ M.pCoreIn 2 := pCoreIn_mono_of_normalizes hIM hMI
  have hIQ : I ≤ normalizer (I.pCoreIn 2 : Set G) := I.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hPQ : P ≤ I.pCoreIn 2 := le_normalizer_iff_commutator_le_left.mp hIQ
  have hpair := original_tripleSix_central_closure_pair_layer_at
    h structural D a z hz hzT hnot g hKI hIe
  have hUQ : U ≤ I.pCoreIn 2 := D.le_componentCore.trans
    (pCoreIn_mono_of_normalizes hKI
      (hIM.trans (sup_le K.le_normalizer D.sylow_normalizes_component)))
  have hUP : U ≤ P := hpair.2.2.1.le.trans (commutator_mono hUQ le_rfl)
  refine ⟨g,hKI,hIe,hpair.2.2.2.choose,hscalar,le_antisymm ?_ ?_⟩
  · exact (commutator_mono (hPQ.trans hQM) le_rfl).trans
      (original_tripleSix_central_closure_scalar_core h structural D a z hz hzT hnot houter)
  · exact (original_tripleSix_scalar_residual_contains_module
      h structural D a z hz hzT hnot houter).2.le.trans (commutator_mono hUP le_rfl)

end CFSG.Quasithin.Chapter12.Section07
