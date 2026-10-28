module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticSpanExact
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticKernelInterval

/-!
# Exact elementary span inside the original quintic core

The normalized path bound makes the selected elementary span exact, while
retaining the full centralizer kernel.  Its H-orbit supplements the original
quintic core, so the exact span can be consumed without a smallness callback.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The exact selected span supplements the full quintic centralizer kernel. -/
theorem source_quintic_exact_span_full_core_supplement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let U := conjugateSpanBy (localModule T M) H
    let C := H ⊓ centralizer (U : Set G)
    ∃ g ∈ X,
      let Ustar := U.map (MulAut.conj g).toMonoidHom
      let Qstar := (H.pCoreIn 2).map (MulAut.conj g).toMonoidHom
      let R := U ⊓ Qstar
      let Rstar := Ustar ⊓ H.pCoreIn 2
      let W := conjugateSpanBy R X
      let J := conjugateSpanBy W H
      IsElementaryAbelian 2 W ∧ W ≤ H.pCoreIn 2 ⊓ X.pCoreIn 2 ∧
        X ≤ normalizer (W : Set G) ∧ W ⊓ U = R ∧ W ⊓ Ustar = Rstar ∧
        Nat.card R = 16 ∧ Nat.card Rstar = 16 ∧ Nat.card W = 32 ∧
        ⁅W,U⁆ = centralInvolutions T ∧ U ⊓ centralizer (W : Set G) = R ∧
        W ⊓ C = R ∧ ⁅W,H.pCoreIn 2⁆ ≤ U ∧
        ¬ W ≤ C ∧ J ≤ H.pCoreIn 2 ∧
        H ≤ normalizer (J : Set G) ∧ J ⊔ C = H.pCoreIn 2 := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let C := H ⊓ centralizer (U : Set G)
  obtain ⟨g,hg,hWel,hWQ,hXW,hWU,hWUstar,hR,hRstar,hWcard,
      hcomm,hfixed,hindex,hcardinal,hWC,hWQcomm⟩ :=
    source_quintic_second_kernel_span_exact hG T hempty hM hu hmany hcard e H hH hi
  let Ustar := U.map (MulAut.conj g).toMonoidHom
  let Qstar := Q.map (MulAut.conj g).toMonoidHom
  let R := U ⊓ Qstar
  let Rstar := Ustar ⊓ Q
  let W := conjugateSpanBy R X
  let J := conjugateSpanBy W H
  have hZcard : Nat.card (centralInvolutions T) = 2 :=
    plane_centralInvolutions_card T M hM.1.2 hcard e
  have hZne : (centralInvolutions T : Subgroup G) ≠ ⊥ := by
    intro hz
    rw [hz,card_bot] at hZcard
    omega
  have hWnotC : ¬ W ≤ C := by
    intro hWC'
    have hbot : ⁅W,U⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
      (hWC'.trans inf_le_right)
    exact hZne (hcomm.symm.trans hbot)
  have hHQ : H ≤ normalizer (Q : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hJQ : J ≤ Q := conjugateSpanBy_le (hWQ.trans inf_le_left) hHQ
  have hHJ : H ≤ normalizer (J : Set G) := le_normalizer_conjugateSpanBy _ _
  have hHC : H ≤ normalizer (C : Set G) :=
    (le_inf H.le_normalizer ((le_normalizer_conjugateSpanBy (localModule T M) H).trans
      (normalizer_le_normalizer_centralizer U))).trans inf_normalizer_le_normalizer_inf
  have hCQ : C ≤ Q := source_quintic_span_centralizer_le_core hG T hM H hH hi
  have hHD : H ≤ normalizer ((J ⊔ C : Subgroup G) : Set G) := by
    intro h hh
    rw [mem_normalizer_iff_map_conj_eq,Subgroup.map_sup,
      mem_normalizer_iff_map_conj_eq.mp (hHJ hh),
      mem_normalizer_iff_map_conj_eq.mp (hHC hh)]
  have hJC : J ⊔ C = Q := by
    rcases (source_quintic_full_kernel_interval hG T hempty hM hu hmany hcard e H hH hi).2
      (J ⊔ C) le_sup_right (sup_le hJQ hCQ) hHD with he | he
    · exact (hWnotC ((le_conjugateSpanBy W H).trans (le_sup_left.trans he.le))).elim
    · exact he
  exact ⟨g,hg,hWel,hWQ,hXW,hWU,hWUstar,hR,hRstar,hWcard,hcomm,hfixed,hWC,
    hWQcomm,hWnotC,hJQ,hHJ,hJC⟩

end CFSG.Quasithin.Chapter14.Section06
