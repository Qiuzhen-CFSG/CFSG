module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.MovedFittingProduct
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.CentralModule
public import CFSG.Quasithin.Chapter14.Section01.AlternatingThree.Complete
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.Residual
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import Theory.GroupTheory.Fitting.OutsideComponent

/-!
# The original exceptional factors in 14.1.13

If radical characteristic control misses the generalized-Fitting preimage,
empty Lf first puts the solvable residual in the control subgroup. Component
extraction then forces the Fitting preimage itself to escape. C.2.6 supplies
one or two outside A₃ blocks with their original Thompson movement retained.
Applying the proved 14.1.10 identifies M with Mc and gives |Ω₁Z(T)|>2.
Each chosen block also has the actual normal A₄ or A₄² Sylow orbit, whose
centralizer and the Sylow subgroup supplement it.

These are source inputs to the remaining exceptional uniqueness argument.
They do not assert control of the centralizer of the whole outside product.
Source: Aschbacher–Smith 14.1.13, printed p.979.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.SourcePreliminaries
open Chapter15.Section03 Chapter15.Section03.InitialSource ChapterC.Section02Source
universe u
variable {G : Type u} [Group G] [Finite G]

theorem source_exceptional_moved_factors
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (R H : Subgroup M) (hr : IsPRadical 2 R)
    (hRT : R ≤ (T.subtype hM.2 : Subgroup M))
    (hcontrol : R.characteristicNormalizerClosure ≤ H)
    (hout : ¬ (generalizedFitting (M ⧸ pCore 2 M)).comap
      (QuotientGroup.mk' (pCore 2 M)) ≤ H) :
    M = Mc ∧ 2 < Nat.card (centralInvolutions T) ∧
    ∃ n : ℕ, 0 < n ∧ n ≤ 2 ∧ ∃ L : Fin n → Subgroup M,
      (∀ i, L i ≤ twoFittingCore M ∧ ¬ L i ≤ H ∧ ChapterC.IsBlock (L i) ∧
        ChapterC.IsAlternatingBlock (L i) 3 ∧ L i = ⁅L i,elementaryAbelianMaxJ R⁆) ∧
      (∀ i, let N := conjugateSpanBy (L i) (T.subtype hM.2 : Subgroup M)
        N.Normal ∧ (Nonempty (N ≃* alternatingGroup (Fin 4)) ∨
          Nonempty (N ≃* AlternatingFourPair.Model)) ∧
        (N ⊔ centralizer (N : Set M)) ⊔ (T.subtype hM.2 : Subgroup M) = ⊤) ∧
      ∀ x : M, x ∈ twoFittingCore M ↔
        ∃ h ∈ H ⊓ twoFittingCore M, ∃ l : Fin n → M,
          (∀ i, l i ∈ L i) ∧ x = h * (List.ofFn l).prod := by
  have hMH : M ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1,hM.2⟩
  have hc : centralizer (pCore 2 M : Set M) ≤ pCore 2 M :=
    hG.evenCharacteristic T M hM.1 hM.2
  have hres : solvableResidual M ≤ H := by
    by_contra hres
    apply outside_moves_radicalCentralModule hr hc hcontrol hres
    exact residual_le_centralizer_omegaCore
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hG T hempty hMH
  have hF : ¬ twoFittingCore M ≤ H := by
    intro hfit
    obtain ⟨L,hL,_,hLH⟩ := exists_cComponent_outside_of_fitting_preimage_le H hfit hout
    let := hL.perfect
    exact hLH ((le_solvableResidual_of_isPerfect L).trans hres)
  obtain ⟨n,hn,L,hL,hprod⟩ := fitting_ordered_moved_product
    (hG.twoLocal_sqtk hM.1.1) R H hr hcontrol hc
  have hnpos : 0 < n := by
    by_contra hnpos
    have hnzero : n = 0 := by omega
    subst n
    apply hF
    intro x hx
    obtain ⟨h,hh,l,_,he⟩ := (hprod x).mp hx
    simp only [List.ofFn_zero,List.prod_nil,mul_one] at he
    exact he ▸ hh.1
  have hQR : pCore 2 M ≤ R := pCore_le_of_pCore_normalizer_le R hr.isPGroup hr.2.le
  obtain ⟨he,hZ⟩ := AlternatingThree.source_lemma_14_1_10_complete
    hG T hM hu hmany (L ⟨0,hnpos⟩) R (hL _).2.2.1 (hL _).2.2.2.1 hQR hRT
      (hL _).2.2.2.2
  refine ⟨he,hZ,n,hnpos,hn,L,hL,?_,hprod⟩
  intro i
  obtain ⟨hnormal,hmodels⟩ := AlternatingThree.source_cubic_orbit hG T hM
    (L i) (hL i).2.2.1 (hL i).2.2.2.1
  let N := conjugateSpanBy (L i) (T.subtype hM.2 : Subgroup M)
  let : N.Normal := hnormal
  refine ⟨hnormal,hmodels,?_⟩
  exact normal_centralizer_sup_sylow_eq_top N (T.subtype hM.2)
    (AlternatingThree.cubic_model_structure N hmodels).2.2

/-- The full nonexceptional control branch: either M differs from Mc or the seed has order two. -/
theorem generalizedFittingPreimage_le_of_radical_control_away
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (haway : M ≠ Mc ∨ Nat.card (centralInvolutions T) = 2)
    (R H : Subgroup M) (hr : IsPRadical 2 R)
    (hRT : R ≤ (T.subtype hM.2 : Subgroup M))
    (hcontrol : R.characteristicNormalizerClosure ≤ H) :
    (generalizedFitting (M ⧸ pCore 2 M)).comap (QuotientGroup.mk' (pCore 2 M)) ≤ H := by
  by_contra hout
  obtain ⟨he,hZ,_⟩ := source_exceptional_moved_factors
    hG T hempty hM hu hmany R H hr hRT hcontrol hout
  rcases haway with hne | htwo
  · exact hne he
  · omega

end CFSG.Quasithin.Chapter14.SourcePreliminaries
