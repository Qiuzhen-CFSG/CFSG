module
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSource
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSource
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.SectionKernel
public import Theory.SpecificGroups.Janko4.PerfectCoverActions
import all CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.OddActorComparison

/-!
# The original noncubic actor and a normal J₄ cover

Choose an involution in the original T-fixed module and lift it to the same
normal covering component of the odd normalizer. Its full centralizer
residual has a genuine M₂₂ radical quotient. The ambient involution
centralizer is a two-local SQTK group, so the noncubic odd-actor comparison
puts this residual in N_G(L).

This extracts the generic comparison already proved in the Mathieu
implementation, without imposing a Mathieu marking on the original module.
The proof-only import deliberately keeps that implementation's other
chapter exports private: its Hall source and the rank-one source export a
homonymous theorem. The public interface uses only their common original
chosen-module definitions and the actual J₄ quotient. No public boundary of
either implementation is changed. The field-four Hermitian consumer combines
this containment with its native nine-space obstruction.

Source: Aschbacher--Smith 4.4.3, final paragraph on printed p.623,
as used in 8.2.7, printed p.718, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- A normal J₄ cover containing the original module supplies a T-fixed
involution whose full centralizer residual lies in N_G(L). The odd actor
has prime greater than three and acts on the original section of L. -/
theorem sourceOrbit_hermitian_janko_fixed_residual_comparison
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit)
    {p : ℕ} (hp : p.Prime) (hgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ sectionCentralizer L) (hAV : A ≤ centralizer (V : Set G))
    (K : Subgroup (normalizer (A : Set G))) [K.Normal] [Group.IsPerfect K]
    (hVK : V ≤ K.map (normalizer (A : Set G)).subtype)
    (hcent : centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)))
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    ∃ z : K, ((z : normalizer (A : Set G)) : G) ∈ V ∧ orderOf z = 2 ∧
      (T : Subgroup G) ≤ centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ∧
      ((solvableResidual (centralizer ({z} : Set K))).map
        (centralizer ({z} : Set K)).subtype).map
          ((normalizer (A : Set G)).subtype.comp K.subtype) ≤ normalizer (L : Set G) := by
  let : Fact p.Prime := ⟨hp⟩
  let := hAe
  let := D.elementary
  let a := jankoNormalizerAction K e hcent
  have ho : Odd (Nat.card A) := by
    obtain ⟨n,hn⟩ := hAe.isPGroup.exists_card_eq
    rw [hn]
    exact (hp.odd_of_ne_two (by omega)).pow
  have hAk : (A.subgroupOf (normalizer (A : Set G))).map a.projection = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [a.kernel]
    apply le_sSup
    refine ⟨inferInstance,?_⟩
    rw [Nat.card_congr (subgroupOfEquivOfLe A.le_normalizer).toEquiv]
    exact ho.coprime_two_left
  have hTV : (T : Subgroup G) ≤ normalizer (V : Set G) :=
    hV.symm ▸ D.sourceOrbit_weakClosure_setup.normalizes
  have hf := inf_centralizer_ne_bot_of_pGroups (T : Subgroup G) V T.isPGroup'
    (IsElementaryAbelian.isPGroup 2 V) hTV D.ne_bot
  obtain ⟨v,hv,hvne⟩ := (V ⊓ centralizer ((T : Subgroup G) : Set G)).bot_or_exists_ne_one.resolve_left hf
  obtain ⟨k,hk,hkv⟩ := hVK hv.1
  let z : K := ⟨k,hk⟩
  have hzv : ((z : normalizer (A : Set G)) : G) = v := hkv
  have hz : orderOf z = 2 := by
    rw [← orderOf_coe z,← orderOf_coe (z : normalizer (A : Set G)),hzv]
    exact orderOf_eq_prime_iff.mpr ⟨elemPow_eq_one_of_isElementaryAbelian v hv.1,hvne⟩
  have hzV : ((z : normalizer (A : Set G)) : G) ∈ V := hzv.symm ▸ hv.1
  have hTz : (T : Subgroup G) ≤ centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) := by
    intro t ht
    rw [hzv]
    exact mem_centralizer_singleton_iff.mpr (hv.2 t ht)
  have hzG : orderOf (((z : normalizer (A : Set G)) : G)) = 2 := by
    rw [orderOf_coe,orderOf_coe]
    exact hz
  have hAz : A ≤ centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr ((hAV hx) _ hzV).symm
  obtain ⟨P,hP,hPn,⟨eP⟩,hPm⟩ := janko_actor_residual_placement a hcent hAk z hz
  obtain ⟨Q,hQ,_⟩ := mathieu_residual_ambient_placement h.simpleQTKE hzG inf_le_left P hP eP
  let := hQ.2.2.1
  let := hQ.2.2.2
  have hQM := D.sourceOrbit_mathieu_oddActor_comparison_component h hp hgt A hne hAe hA
    _ hzG hTz hAz P hP eP Q hQ.2.1
  refine ⟨z,hzV,hz,hTz,?_⟩
  rw [←hPm]
  have hh := map_mono (f := (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G)).subtype)
    hQ.2.1
  rw [map_map,subtype_comp_inclusion] at hh
  exact hh.trans hQM
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
