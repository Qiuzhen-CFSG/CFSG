module

public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticFiveResidualDerived
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticSpanStrongFull
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticKernelMiddlePlacement

/-!
# The original reciprocal span excludes a central residual derived layer

If the actual five-residual contains every involution of the full core, it
contains the original elementary span W of order thirty-two. A central
residual derived layer would normalize the reciprocal seed of order sixteen.
The full kernel lies in the middle core, so it normalizes the same seed.
The three actual cores generate the middle group, forcing that seed to be
middle-invariant and equal to W. Their distinct orders contradict this.
The critical conjugator and every original subgroup marking are preserved.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Original reciprocal geometry rules out a central derived residual once
its literal involution-containment property is supplied. -/
theorem source_quintic_large_five_residual_derived_not_central_of_involutions
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlarge : Nat.card (H.pCoreIn 2) = 1024)
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 5)
    (hinv : ∀ q ∈ H.pCoreIn 2, q ^ 2 = 1 → q ∈ ⁅H.pCoreIn 2,A⁆) :
    ¬ ⁅⁅H.pCoreIn 2,A⁆,⁅H.pCoreIn 2,A⁆⁆ ≤ centralInvolutions T := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let QX := X.pCoreIn 2
  let C := H ⊓ centralizer (U : Set G)
  let R := ⁅Q,A⁆
  let Z := centralInvolutions T
  intro hcentral
  obtain ⟨g,hg,hDQ,hescape,hVI,_,_,_,_,hWel,hWQ,hXW,hWU,hWUstar,
    hSstarW,_,_,hSstarcard,hWcard,_,_,_,_,_,_⟩ :=
    source_quintic_second_kernel_span_strong_full hG T hempty hM hu hmany hcard e H hH hi
  let c := (MulAut.conj g).toMonoidHom
  let D := U.map c
  let Qstar := Q.map c
  let S := U ⊓ Qstar
  let Sstar := D ⊓ Q
  let W := conjugateSpanBy S X
  change IsElementaryAbelian 2 W at hWel
  change W ≤ Q ⊓ QX at hWQ
  change X ≤ normalizer (W : Set G) at hXW
  change W ⊓ U = S at hWU
  change W ⊓ D = Sstar at hWUstar
  change Sstar ≤ W at hSstarW
  change Nat.card Sstar = 16 at hSstarcard
  change Nat.card W = 32 at hWcard
  let : IsElementaryAbelian 2 W := hWel
  have hWR : W ≤ R := by
    intro w hw
    exact hinv w (hWQ hw).1 (elemPow_eq_one_of_isElementaryAbelian (p := 2) w hw)
  obtain ⟨_,_,_,_,_,hUR,hRC,_⟩ := source_quintic_large_five_residual
    hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA
  change R ⊔ C = Q at hRC
  have hAQ : A ≤ normalizer (Q : Set G) := hAH.trans
    (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  have hRQ : R ≤ Q := le_normalizer_iff_commutator_le_left.mp hAQ
  have hZU : Z ≤ U := (le_conjugateSpanBy _ _).trans (le_conjugateSpanBy _ _)
  have hZV : Z ≤ localModule T M := le_conjugateSpanBy _ _
  have hZSstar : Z ≤ Sstar := le_inf
    (hZV.trans (hVI.trans inf_le_right))
    (hZU.trans (hUR.trans hRQ))
  have hRSstar : R ≤ normalizer (Sstar : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr
      (((commutator_mono (hSstarW.trans hWR) le_rfl).trans hcentral).trans hZSstar)
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hQT : Q ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow H (T.subtype hTH)).trans_eq (map_subgroupOf_eq_of_le hTH)
  have hQXT : QX ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow X (T.subtype hTX)).trans_eq (map_subgroupOf_eq_of_le hTX)
  have hQXnormal : X ≤ normalizer (QX : Set G) := X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hQXmap : QX.map c = QX := mem_normalizer_iff_map_conj_eq.mp (hQXnormal hg)
  have hXmap : X.map c = X := mem_normalizer_iff_map_conj_eq.mp (X.le_normalizer hg)
  have hHU : H ≤ normalizer (U : Set G) := le_normalizer_conjugateSpanBy _ _
  have hHgD : H.map c ≤ normalizer (D : Set G) :=
    (map_mono hHU).trans (U.le_normalizer_map c)
  have hQstarX : Qstar ≤ X := (map_mono (hQT.trans hTX)).trans hXmap.le
  have hQXHg : QX ≤ H.map c := by
    rw [← hQXmap]
    exact map_mono (hQXT.trans hTH)
  have hnormS (K : Subgroup G) (hKX : K ≤ X) (hKHg : K ≤ H.map c) :
      K ≤ normalizer (Sstar : Set G) := by
    rw [← hWUstar]
    exact (le_inf (hKX.trans hXW) (hKHg.trans hHgD)).trans
      inf_normalizer_le_normalizer_inf
  have hCSstar : C ≤ normalizer (Sstar : Set G) := by
    have hCQX := (source_quintic_full_kernel_middle_placement
      hG T hempty hM hu hmany hcard e H hH hi).1
    exact hnormS C (hCQX.trans (pCoreIn_le 2 X)) (hCQX.trans hQXHg)
  have hQSstar : Q ≤ normalizer (Sstar : Set G) := by
    rw [← hRC]
    exact sup_le hRSstar hCSstar
  have hQstarSstar : Qstar ≤ normalizer (Sstar : Set G) :=
    hnormS Qstar hQstarX (map_mono (pCoreIn_le 2 H))
  have hQXSstar : QX ≤ normalizer (Sstar : Set G) :=
    hnormS QX (pCoreIn_le 2 X) hQXHg
  have hgen : X = (Q ⊔ Qstar) ⊔ QX :=
    (source_quintic_reciprocal_core_geometry
      hG T hempty hM hu hmany hcard e H hH hi g hg hescape).1
  have hXSstar : X ≤ normalizer (Sstar : Set G) := by
    rw [hgen]
    exact sup_le (sup_le hQSstar hQstarSstar) hQXSstar
  have hWmap : W.map c = W := mem_normalizer_iff_map_conj_eq.mp (hXW hg)
  have hSmap : S.map c = Sstar := by
    rw [← hWU, Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hWmap]
    exact hWUstar
  have hSstarMap : Sstar.map c = Sstar :=
    mem_normalizer_iff_map_conj_eq.mp (hXSstar hg)
  have hSSstar : S = Sstar := Subgroup.map_injective (MulAut.conj g).injective
    (hSmap.trans hSstarMap.symm)
  have hWle : W ≤ Sstar := conjugateSpanBy_le hSSstar.le hXSstar
  have hc := card_le_of_le hWle
  rw [hWcard, hSstarcard] at hc
  omega

end CFSG.Quasithin.Chapter14.Section06
