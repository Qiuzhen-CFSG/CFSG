module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticExactCoreSupplement
public import Theory.GroupTheory.Commutator.NormalSpan

/-!
# An original quintic-core supplement central modulo the span

The H-orbit of the actual elementary middle span supplements the full
centralizer kernel C. Its commutator bound propagates through that H-orbit,
giving a supplement central modulo the original quintic span U. No bound
or identification of the remaining full kernel is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The literal core has an H-normal supplement central modulo U. -/
theorem source_quintic_full_core_central_supplement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let U := conjugateSpanBy (localModule T M) H
    let C := H ⊓ centralizer (U : Set G)
    ∃ J : Subgroup G, J ≤ H.pCoreIn 2 ∧ H ≤ normalizer (J : Set G) ∧
      J ⊔ C = H.pCoreIn 2 ∧ ⁅J,H.pCoreIn 2⁆ ≤ U := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let C := H ⊓ centralizer (U : Set G)
  obtain ⟨g,hg,hWel,hWQ,hXW,hWU,hWUstar,hR,hRstar,hWcard,
      hcomm,hfixed,hWC,hWQcomm,hWnotC,hJQ,hHJ,hJC⟩ :=
    source_quintic_exact_span_full_core_supplement
      hG T hempty hM hu hmany hcard e H hH hi
  let R := U ⊓ Q.map (MulAut.conj g).toMonoidHom
  let W := conjugateSpanBy R X
  let J := conjugateSpanBy W H
  have hHQ : H ≤ normalizer (Q : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hHU : H ≤ normalizer (U : Set G) := le_normalizer_conjugateSpanBy _ _
  have hWH : W ≤ H := (hWQ.trans inf_le_left).trans (pCoreIn_le 2 H)
  have hJcomm : ⁅J,Q⁆ ≤ U := by
    change ⁅conjugateSpanBy W H,Q⁆ ≤ U
    rw [commutator_conjugateSpanBy_of_normalized_right W H Q hWH hHQ]
    exact conjugateSpanBy_le hWQcomm hHU
  exact ⟨J,hJQ,hHJ,hJC,hJcomm⟩

end CFSG.Quasithin.Chapter14.Section06
