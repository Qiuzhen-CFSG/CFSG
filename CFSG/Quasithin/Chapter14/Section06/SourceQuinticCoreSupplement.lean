module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticSecondKernelSpan
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticKernelInterval

/-!
# The actual quintic core is generated modulo its full second kernel

The elementary middle span contains a reciprocal intersection that moves
the original H-span, so it escapes its full centralizer C. Its H-conjugate
span therefore has nonzero image in the irreducible quotient QH/C. The
original invariant-interval theorem gives the full supplement, with C
retained as the literal centralizer rather than replaced by a smaller layer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The selected elementary span and its original H-orbit supplement the
whole centralizer kernel in the whole quintic core. -/
theorem source_quintic_full_core_span_supplement
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
    let Q := H.pCoreIn 2
    let C := H ⊓ centralizer (U : Set G)
    ∃ g ∈ X,
      let Ustar := U.map (MulAut.conj g).toMonoidHom
      let Qstar := Q.map (MulAut.conj g).toMonoidHom
      let R := U ⊓ Qstar
      let Rstar := Ustar ⊓ Q
      let W := conjugateSpanBy R X
      let J := conjugateSpanBy W H
      IsElementaryAbelian 2 W ∧ W ≤ Q ⊓ X.pCoreIn 2 ∧
        X ≤ normalizer (W : Set G) ∧
        W ⊓ U = R ∧ W ⊓ Ustar = Rstar ∧ Rstar ≤ W ∧
        ⁅Rstar,U⁆ ≠ ⊥ ∧ ¬ W ≤ C ∧ J ≤ Q ∧
        H ≤ normalizer (J : Set G) ∧ J ⊔ C = Q := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let C := H ⊓ centralizer (U : Set G)
  obtain ⟨g,hg,_,_,_,_,_,_,_,hWel,hWQ,hXW,hWU,hRW,hWUstar,hmove⟩ :=
    source_quintic_second_kernel_span hG T hempty hM hu hmany hcard e H hH hi
  let Ustar := U.map (MulAut.conj g).toMonoidHom
  let Qstar := Q.map (MulAut.conj g).toMonoidHom
  let R := U ⊓ Qstar
  let Rstar := Ustar ⊓ Q
  let W := conjugateSpanBy R X
  let J := conjugateSpanBy W H
  have hWnotC : ¬ W ≤ C := by
    intro hWC
    exact hmove (commutator_eq_bot_iff_le_centralizer.mpr
      ((hRW.trans hWC).trans inf_le_right))
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
  exact ⟨g,hg,hWel,hWQ,hXW,hWU,hWUstar,hRW,hmove,hWnotC,hJQ,hHJ,hJC⟩

end CFSG.Quasithin.Chapter14.Section06
