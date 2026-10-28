module
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd.SolvableInversion
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicConstructionSeed
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicConstructionResidual
public import Theory.Frattini.PGroup
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Inversion and the prime-order branch of invariant Sylow selection

Inversion on the literal star quotient H/J, together with Φ(P)=P∩N_G(L),
gives inversion on P/Φ(P) whenever the chosen inverter normalizes P.
The two-primary quotient identifies the odd prime of every prime-order
rotation in H. Thus, when the original odd Sylow has prime order, the
already constructed inverted prime rotation generates another Sylow of
that same order. Its inverter preserves the Sylow and its Frattini
subgroup is trivial, completing every invariant-selection clause.

LocalConfigurationCyclicConstructionSelectionAssembly applies this branch
to the actual cyclic-block conclusion and retains only nonprime selection
as an input to the remaining assembly. General nonprime selection and
extraspecial exclusion stay with qt-d-12213-cyclic-block.
Source: Aschbacher–Smith, 12.2.21–22, printed pp.802–803.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d p : ℕ} {g v : G}

/-- An invariant odd Sylow inherits inversion on its literal Frattini quotient. -/
theorem CyclicConstructionSeed.inverts_frattini_quotient_of_normalizes
    (S : CyclicConstructionSeed T L V d p H P U g)
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V)
    (hv : v ∈ V) (hvU : v ∉ U) (hvP : v ∈ normalizer (P : Set G)) :
    ∀ x ∈ P, v * x * v⁻¹ * x ∈ (frattini P).map P.subtype := by
  have hTH := S.hstar.1.1.2
  have hVH := D.le_sylow.trans hTH
  have hPH : P ≤ H := S.overgroup ▸ le_sup_left
  have hvQ : v ∉ H.pCoreIn 2 := by
    intro he
    have hh : v ∈ H.pCoreIn 2 ⊓ V := ⟨he, hv⟩
    rw [S.core_intersection D A] at hh
    exact hvU hh.1
  let T' := T.subtype hTH
  let hmin := chosen_hstar_intrinsic_minimalParabolic D A S.hstar
  let J := ChapterB.minimalParabolicCore T' hmin
  have hmax : (H ⊓ normalizer (L : Set G)).subgroupOf H =
      ChapterB.minimalParabolicMax T' hmin := by
    obtain ⟨hTB, hBH, _⟩ := Chapter3.HStar.unique_maximal T D.sylow_normalizes_component S.hstar
    have hp := Chapter3.HStar.minimalParabolic T D.sylow_normalizes_component S.hstar
      (Or.inr ((ChapterB.isMinimalParabolicOver_top_iff T').mp hmin).2)
    exact ChapterB.minimalParabolicMax_unique T' hmin
      (ChapterB.intrinsic_minimalParabolic T H (H ⊓ normalizer (L : Set G)) hp hTB hBH).2
      (comap_mono hTB)
  have hJM : J ≤ (normalizer (L : Set G)).comap H.subtype := by
    have hh : J ≤ ChapterB.minimalParabolicMax T' hmin := normalCore_le _
    rw [← hmax] at hh
    exact hh.trans (comap_mono inf_le_right)
  have hTV' : (T' : Subgroup H) ≤ normalizer (V.subgroupOf H : Set H) := by
    intro t ht
    exact V.le_normalizer_comap H.subtype (hTV ht)
  have hi := ChapterB.minimalParabolic_solvable_inverts_star_residual T' hmin
    (A.hstar_solvable H S.hstar) (V.subgroupOf H)
    (subgroupOf_mono H D.le_sylow) hTV'
    (chosen_hstar_quotient_module_card_two D A hTV hTI S.hstar)
    (⟨v, hVH hv⟩ : H) hv (fun he => hvQ (mem_map_of_mem H.subtype he))
  have hPK := odd_prime_subgroup_le_twoResidual S.odd_prime (P.subgroupOf H)
    S.pgroup.comap_subtype
  intro x hx
  rw [S.frattini_intersection]
  exact ⟨P.mul_mem ((mem_normalizer_iff.mp hvP x).mp hx) hx,
    hJM (hi ⟨x, hPH hx⟩ (hPK hx))⟩


/-- The successive two-primary quotient fixes the prime of every odd prime rotation in H. -/
theorem CyclicConstructionSeed.prime_eq_of_odd_prime_element
    (S : CyclicConstructionSeed T L V d p H P U g)
    {r : ℕ} (hr : r.Prime) (ho : Odd r) (a : H) (ha : orderOf a = r) : r = p := by
  let : Fact p.Prime := ⟨S.prime⟩
  let q := QuotientGroup.mk' (pCore 2 H)
  have hqa : q a ≠ 1 := by
    intro he
    have hm := (QuotientGroup.eq_one_iff a).mp he
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := H)) ⟨a, hm⟩
    have hd : r ∣ 2 ^ n := ha ▸ orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hn)
    have heq : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hd)
    exact ho.not_two_dvd_nat (by rw [heq])
  have hm : q a ∈ pCore p (H ⧸ pCore 2 H) := by
    apply (pResidual_le_iff_isPGroup_quotient 2 _).mpr S.quotient_two
    exact mem_pResidual_of_orderOf_coprime
      (Nat.coprime_two_left.mpr ((ha.symm ▸ ho).of_dvd_nat (orderOf_map_dvd q a)))
  have hd := (pCore_isPGroup (p := p) (G := H ⧸ pCore 2 H)).dvd_orderOf
    (g := ⟨q a, hm⟩) (fun he => hqa (congrArg Subtype.val he))
  rw [← Subgroup.orderOf_coe] at hd
  exact ((Nat.prime_dvd_prime_iff_eq S.prime hr).mp
    (hd.trans (ha ▸ orderOf_map_dvd q a))).symm


/-- Complete invariant selection in the prime-order branch, keeping the original H and p. -/
theorem CyclicConstructionSeed.invariantSelection_of_prime_order
    (S : CyclicConstructionSeed T L V d p H P U g)
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V)
    (hc : Nat.card P = p) :
    ∃ P' U' g' v, CyclicInvariantSelection T L V d p H P' U' g' v := by
  obtain ⟨r, P', U', g', v, R, hg', hv, _, hvU, hinv⟩ :=
    chosen_hstar_exists_cyclicConstructionSeed D A hTV hTI S.hstar
  have hP'H : P' ≤ H := R.overgroup ▸ le_sup_left
  have hrp : r = p := S.prime_eq_of_odd_prime_element R.prime R.odd_prime
    ⟨g', hP'H R.generator_mem⟩ ((Subgroup.orderOf_coe _).symm.trans hg')
  rw [hrp] at R hg'
  let : Fact p.Prime := ⟨S.prime⟩
  have hcard : Nat.card P' = p := by
    obtain ⟨Q, hQ⟩ := S.sylow
    obtain ⟨Q', hQ'⟩ := R.sylow
    rw [← hQ', card_map_of_injective H.subtype_injective,
      Nat.card_congr (Q'.equiv Q).toEquiv, ← card_map_of_injective H.subtype_injective,
      hQ, hc]
  have hgen : zpowers g' = P' := eq_of_le_of_card_ge
    (zpowers_le.mpr R.generator_mem) (by rw [Nat.card_zpowers, hg', hcard])
  have hvP : v ∈ normalizer (P' : Set G) := by
    rw [← hgen, mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change zpowers (v * g' * v⁻¹) = zpowers g'
    rw [hinv, zpowers_inv]
  have hphi : frattini P' = ⊥ := by
    have hpow : g' ^ p = 1 := hg' ▸ pow_orderOf_eq_one g'
    let he : IsElementaryAbelian p (zpowers g') := IsElementaryAbelian.zpowers_of_pow_eq_one hpow
    let : IsElementaryAbelian p P' := hgen ▸ he
    let : Fact (IsPGroup p P') := ⟨R.pgroup⟩
    exact frattini_eq_bot_of_isElementaryAbelian (p := p)
  refine ⟨P', U', g', v, ?_⟩
  exact {
    toCyclicConstructionSeed := R
    alternatives := Or.inl hcard
    generator_order := hg'
    inverter_mem := hv
    inverter_outside := hvU
    inverts_generator := hinv
    inverter_normalizes := hvP
    inverts_frattini_quotient := R.inverts_frattini_quotient_of_normalizes D A hTV hTI hv hvU hvP
    frattini_normalizes := by rw [hphi, Subgroup.map_bot]; exact bot_le
    residual := R.residual D A hTV }

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
