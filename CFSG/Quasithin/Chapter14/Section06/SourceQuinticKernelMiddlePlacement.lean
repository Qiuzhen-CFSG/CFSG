module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticDGSFullKernel
public import CFSG.Quasithin.Chapter14.Section02.ResidualSylow

/-!
# The full quintic kernel lies in the middle core

The full span centralizer lies in the original Sylow subgroup and centralizes
the original four-plane. The actual middle quotient identifies precisely this
action kernel with its two-core. Normality of that core then places the full
centralizer in every conjugate of the quintic endpoint by the middle group.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The literal full kernel lies in the middle two-core, and hence in each
quintic endpoint conjugated by an element of the actual middle group. -/
theorem source_quintic_full_kernel_middle_placement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let U := conjugateSpanBy (localModule T M) H
    let C := H ⊓ centralizer (U : Set G)
    C ≤ X.pCoreIn 2 ∧
      ∀ g ∈ X, C ≤ H.map (MulAut.conj g).toMonoidHom := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (localModule T M) H
  let C := H ⊓ centralizer (U : Set G)
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hQHT : H.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow H (T.subtype hTH)).trans_eq (map_subgroupOf_eq_of_le hTH)
  have hQXT : X.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow X (T.subtype hTX)).trans_eq (map_subgroupOf_eq_of_le hTX)
  have hCX : C ≤ X :=
    (source_quintic_span_centralizer_le_core hG T hM H hH hi).trans
      (hQHT.trans hTX)
  have hCQX : C ≤ X.pCoreIn 2 := by
    rw [(Section02.source_residualSylow_quotient
      hG T hempty hM hu hmany hcard e).1]
    exact le_inf hCX (inf_le_right.trans
      (centralizer_le (le_conjugateSpanBy (localModule T M) H)))
  have hXQX : X ≤ normalizer (X.pCoreIn 2 : Set G) :=
    X.le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  refine ⟨hCQX, fun g hg => ?_⟩
  calc
    C ≤ X.pCoreIn 2 := hCQX
    _ = (X.pCoreIn 2).map (MulAut.conj g).toMonoidHom :=
      (mem_normalizer_iff_map_conj_eq.mp (hXQX hg)).symm
    _ ≤ H.map (MulAut.conj g).toMonoidHom := map_mono (hQXT.trans hTH)

end CFSG.Quasithin.Chapter14.Section06
