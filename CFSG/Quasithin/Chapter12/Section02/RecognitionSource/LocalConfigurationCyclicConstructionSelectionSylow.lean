module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicConstructionSelectionNormalizer
public import Theory.GroupTheory.InvariantSylowPrimeIndex
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import Theory.ElementaryAbelian.Injective
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
import all CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicConstructionSeed

/-!
# Invariant Sylow selection in the two nonprime branches of 12.2.22

The original star-quotient inversion proves that the inverter stays outside
the two-core of N_H(B)/B, where B is the source subgroup of index p in P.
The quotient Baer–Suzuki argument selects a Sylow containing B that is
invariant under the same inverter. Reselection preserves every supplement
field, the original generator g, and the literal pair core U. The small
odd alternatives transfer by the actual Sylow equivalence.

Consequently, once the small-group alternatives have been established,
every invariant-selection clause follows without a further callback.
The final application is in LocalConfigurationCyclicConstructionSelectionSylowAssembly.
Small-group recognition and the terminal extraspecial contradiction remain
with qt-d-12213-cyclic-block.
Source: Aschbacher–Smith, 12.2.21–22, printed pp.802–803.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d p : ℕ} {g : G}
namespace CyclicConstructionSeed
variable (S : CyclicConstructionSeed T L V d p H P U g)
include S

/-- The original solvable quotient chain has only the primes 2 and p. -/
theorem hstar_prime_divisors {r : ℕ} (hr : r.Prime) (hd : r ∣ Nat.card H) :
    r = 2 ∨ r = p := by
  let : Fact p.Prime := ⟨S.prime⟩
  let Q := pCore 2 H
  let R := pCore p (H ⧸ Q)
  obtain ⟨a, ha⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
  obtain ⟨b, hb⟩ := (pCore_isPGroup (p := p) (G := H ⧸ Q)).exists_card_eq
  obtain ⟨c, hc⟩ := S.quotient_two.exists_card_eq
  rw [card_eq_card_quotient_mul_card_subgroup Q,
    card_eq_card_quotient_mul_card_subgroup R, ha, hb, hc] at hd
  rcases hr.dvd_mul.mp hd with hd | hd
  · rcases hr.dvd_mul.mp hd with hd | hd
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hd))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr S.prime).mp (hr.dvd_of_dvd_pow hd))
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hd))

/-- The original inverter acts by inversion on P modulo the actual normal
core of the minimal parabolic, whose intersection with P is in Φ(P). -/
theorem exists_normal_inversion_kernel
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V)
    {v : G} (hv : v ∈ V) (hvU : v ∉ U) :
    ∃ J : Subgroup H, J.Normal ∧
      J ≤ (normalizer (L : Set G)).comap H.subtype ∧
      ∀ (x : G) (hx : x ∈ P), (⟨v, D.le_sylow.trans S.hstar.1.1.2 hv⟩ : H) *
        ⟨x, (S.overgroup ▸ le_sup_left) hx⟩ *
        (⟨v, D.le_sylow.trans S.hstar.1.1.2 hv⟩ : H)⁻¹ *
        ⟨x, (S.overgroup ▸ le_sup_left) hx⟩ ∈ J := by
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
  exact ⟨J, inferInstance, hJM, fun x hx => hi ⟨x, hPH hx⟩ (hPK hx)⟩

/-- The source index-p normalizer construction selects a Sylow of H
invariant under the original inverter, retaining the prescribed subgroup B. -/
theorem exists_invariant_sylow_containing_index_prime
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V)
    (B : Subgroup G) (hBP : B ≤ P) (hPhi : (frattini P).map P.subtype ≤ B)
    (hidx : B.relIndex P = p) (hPN : P ≤ normalizer (B : Set G))
    {v : G} (hv : v ∈ V) (hvU : v ∉ U) (hvB : v ∈ normalizer (B : Set G)) :
    ∃ R : Sylow p H, B ≤ (R : Subgroup H).map H.subtype ∧
      v ∈ normalizer (((R : Subgroup H).map H.subtype) : Set G) := by
  let : Fact p.Prime := ⟨S.prime⟩
  let := D.elementary
  have hPH : P ≤ H := S.overgroup ▸ le_sup_left
  have hBH := hBP.trans hPH
  obtain ⟨Q, hQ⟩ := S.sylow
  have hQsub : P.subgroupOf H = (Q : Subgroup H) := by
    rw [← hQ]
    change ((Q : Subgroup H).map H.subtype).comap H.subtype = _
    rw [comap_map_eq, H.subtype.ker_eq_bot H.subtype_injective, sup_bot_eq]
  let BH := B.subgroupOf H
  let N := normalizer (BH : Set H)
  have hQN : (Q : Subgroup H) ≤ N := by
    intro x hx
    have hxP : x ∈ P.subgroupOf H := hQsub.symm ▸ hx
    exact B.le_normalizer_comap H.subtype (hPN hxP)
  let PN := Q.subtype hQN
  let BN := BH.subgroupOf N
  have hBN : BN ≤ (PN : Subgroup N) := by
    intro x hx
    change x.val ∈ (Q : Subgroup H)
    rw [← hQsub]
    exact hBP hx
  have hBidx : BN.relIndex (PN : Subgroup N) = p := by
    change (BH.subgroupOf N).relIndex ((Q : Subgroup H).subgroupOf N) = p
    rw [relIndex_subgroupOf hQN, ← hQsub, relIndex_subgroupOf hPH]
    exact hidx
  have hBlt : BN < (PN : Subgroup N) := lt_of_le_of_ne hBN (by
    intro he
    rw [he, relIndex_self] at hBidx
    exact S.prime.ne_one hBidx.symm)
  let vH : H := ⟨v, D.le_sylow.trans S.hstar.1.1.2 hv⟩
  have hvN : vH ∈ N := B.le_normalizer_comap H.subtype hvB
  let vN : N := ⟨vH, hvN⟩
  obtain ⟨J, hJ, hJM, hi⟩ := S.exists_normal_inversion_kernel D A hTV hTI hv hvU
  let : J.Normal := hJ
  let JN := J.comap N.subtype
  have hJP : JN ⊓ (PN : Subgroup N) ≤ BN := by
    intro x hx
    have hxP : (x.val : G) ∈ P := by
      change x.val ∈ P.subgroupOf H
      rw [hQsub]
      exact hx.2
    have hxPhi : (x.val : G) ∈ (frattini P).map P.subtype := by
      rw [S.frattini_intersection]
      exact ⟨hxP, hJM hx.1⟩
    exact hPhi hxPhi
  have hinv : ∀ x ∈ (PN : Subgroup N), vN * x * vN⁻¹ * x ∈ JN := by
    intro x hx
    have hxP : (x.val : G) ∈ P := by
      change x.val ∈ P.subgroupOf H
      rw [hQsub]
      exact hx
    exact hi x.val hxP
  have hmove := not_mem_twoCore_quotient_of_inverts_modulo S.odd_prime
    (PN : Subgroup N) BN JN PN.isPGroup' hBlt hJP vN hinv
  have hprimes (r : ℕ) (hr : r.Prime) (hd : r ∣ Nat.card N) : r = 2 ∨ r = p :=
    S.hstar_prime_divisors hr (hd.trans (card_subgroup_dvd_card N))
  have hv2 : vN ^ 2 = 1 := Subtype.ext (Subtype.ext
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv))
  obtain ⟨R, hBR, hvR⟩ := exists_invariant_sylow_of_prime_relative_index PN BN hBN hBidx
    hprimes vN hv2 hmove
  let RH := (R : Subgroup N).map N.subtype
  have hc : Nat.card RH = p ^ (Nat.card H).factorization p := by
    rw [card_map_of_injective N.subtype_injective,
      Nat.card_congr (R.equiv PN).toEquiv]
    change Nat.card ((Q : Subgroup H).subgroupOf N) = _
    rw [Nat.card_congr (subgroupOfEquivOfLe hQN).toEquiv, Q.card_eq_multiplicity]
  let R' := Sylow.ofCard RH hc
  refine ⟨R', ?_, ?_⟩
  · intro x hx
    have hxH : (⟨x, hBH hx⟩ : H) ∈ BH := hx
    have hxN : (⟨x, hBH hx⟩ : H) ∈ N := BH.le_normalizer hxH
    exact ⟨⟨x, hBH hx⟩, ⟨⟨⟨x, hBH hx⟩, hxN⟩, hBR hx, rfl⟩, rfl⟩
  · exact (RH.le_normalizer_map H.subtype)
      (mem_map_of_mem H.subtype ((R : Subgroup N).le_normalizer_map N.subtype
        (mem_map_of_mem N.subtype hvR)))

/-- Reselecting the odd Sylow preserves every seed field on the same prime
rotation g and the same literal pair core U. -/
theorem reselect_sylow
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hg : orderOf g = p) (R : Sylow p H)
    (hgR : g ∈ (R : Subgroup H).map H.subtype) :
    CyclicConstructionSeed T L V d p H ((R : Subgroup H).map H.subtype) U g := by
  let : Fact p.Prime := ⟨S.prime⟩
  have hPH : P ≤ H := S.overgroup ▸ le_sup_left
  let a : H := ⟨g, hPH S.generator_mem⟩
  let q := QuotientGroup.mk' (pCore 2 H)
  have hao : orderOf a = p := (Subgroup.orderOf_coe a).symm.trans hg
  have hqa : q a ≠ 1 := by
    intro he
    have hm := (QuotientGroup.eq_one_iff a).mp he
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := H)) ⟨a, hm⟩
    have hd : p ∣ 2 ^ n := hao ▸ orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hn)
    have heq : p = 2 := (Nat.prime_dvd_prime_iff_eq S.prime Nat.prime_two).mp
      (S.prime.dvd_of_dvd_pow hd)
    exact S.odd_prime.not_two_dvd_nat (by rw [heq])
  have hmin := chosen_hstar_intrinsic_minimalParabolic D A S.hstar
  obtain ⟨r, hr, ho, hres, _, hPhi, _⟩ := ChapterB.minimalParabolic_solvable_structure
    (T.subtype S.hstar.1.1.2) hmin (A.hstar_solvable H S.hstar)
  let : Fact r.Prime := ⟨hr⟩
  have haR : q a ∈ pCore r (H ⧸ pCore 2 H) := by
    rw [← hres]
    exact mem_pResidual_of_orderOf_coprime
      (Nat.coprime_two_left.mpr ((hao.symm ▸ S.odd_prime).of_dvd_nat (orderOf_map_dvd q a)))
  have hrp : r = p := by
    have hd := (pCore_isPGroup (p := r) (G := H ⧸ pCore 2 H)).dvd_orderOf
      (g := ⟨q a, haR⟩) (fun he => hqa (congrArg Subtype.val he))
    rw [← Subgroup.orderOf_coe] at hd
    exact (Nat.prime_dvd_prime_iff_eq hr S.prime).mp
      (hd.trans (hao ▸ orderOf_map_dvd q a))
  rw [hrp] at hres hPhi
  have B := odd_supplement_of_sylow D A S.hstar S.odd_prime hres hPhi R
  exact {
    hstar := B.hstar
    prime := B.prime
    odd_prime := B.odd_prime
    pgroup := B.pgroup
    sylow := B.sylow
    escapes := B.escapes
    overgroup := B.overgroup
    factorization := B.factorization
    quotient_core := B.quotient_core
    quotient_two := B.quotient_two
    frattini_intersection := B.frattini_intersection
    generator_mem := hgR
    pair_core := S.pair_core
    pair_generated := S.pair_generated
    pair_disjoint := S.pair_disjoint
    core_generated := S.core_generated
    pair_fixed := S.pair_fixed
    core_moved := S.core_moved
    transvections := S.transvections
    action_kernel := S.action_kernel
    hyperplane_index := S.hyperplane_index
    hyperplane := S.hyperplane }

/-- The small odd-group alternatives are preserved under Sylow reselection. -/
theorem alternatives_of_sylow
    (halt : Nat.card P = p ∨
      (IsElementaryAbelian p P ∧ Nat.card P = p ^ 2) ∨
      (IsExtraspecial p P ∧ Nat.card P = p ^ 3 ∧ Monoid.exponent P = p))
    (R : Sylow p H) :
    let P' := (R : Subgroup H).map H.subtype
    Nat.card P' = p ∨
      (IsElementaryAbelian p P' ∧ Nat.card P' = p ^ 2) ∨
      (IsExtraspecial p P' ∧ Nat.card P' = p ^ 3 ∧ Monoid.exponent P' = p) := by
  let : Fact p.Prime := ⟨S.prime⟩
  obtain ⟨Q, hQ⟩ := S.sylow
  let e : P ≃* (R : Subgroup H).map H.subtype :=
    (MulEquiv.subgroupCongr hQ.symm).trans
      (((Q : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective).symm.trans
        ((Q.equiv R).trans ((R : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective)))
  have hc := Nat.card_congr e.toEquiv
  dsimp only
  rcases halt with h | ⟨he, h⟩ | ⟨he, h, hx⟩
  · exact Or.inl (hc.symm.trans h)
  · let := he
    exact Or.inr (Or.inl ⟨IsElementaryAbelian.of_injective e.symm.toMonoidHom e.symm.injective,
      hc.symm.trans h⟩)
  · exact Or.inr (Or.inr ⟨IsExtraspecial.of_mulEquiv e he, hc.symm.trans h,
      (Monoid.exponent_eq_of_mulEquiv e).symm.trans hx⟩)

/-- In both nonprime alternatives, the source normalizer quotient gives a
fully invariant odd analysis while retaining the original g, v and U. -/
theorem invariantSelection_of_small_alternatives
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V)
    (halt : Nat.card P = p ∨
      (IsElementaryAbelian p P ∧ Nat.card P = p ^ 2) ∨
      (IsExtraspecial p P ∧ Nat.card P = p ^ 3 ∧ Monoid.exponent P = p))
    (hg : orderOf g = p) {v : G} (hv : v ∈ V) (hvU : v ∉ U)
    (hi : v * g * v⁻¹ = g⁻¹) :
    ∃ P', CyclicInvariantSelection T L V d p H P' U g v := by
  by_cases hc : Nat.card P = p
  · have hgen : zpowers g = P := eq_of_le_of_card_ge
      (zpowers_le.mpr S.generator_mem) (by rw [Nat.card_zpowers, hg, hc])
    have hvP : v ∈ normalizer (P : Set G) := by
      rw [← hgen, mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
      change zpowers (v * g * v⁻¹) = zpowers g
      rw [hi, zpowers_inv]
    exact ⟨P, S.invariantSelection_of_small_invariant_inverter D A hTV hTI halt hg hv hvU hi hvP⟩
  · obtain ⟨B, hBP, hPhi, hgB, hidx, hPN, hvB⟩ :=
      S.exists_index_prime_normalizer_seed D A hTV hTI halt hc hg hv hi
    obtain ⟨R, hBR, hvR⟩ :=
      S.exists_invariant_sylow_containing_index_prime D A hTV hTI B hBP hPhi hidx hPN hv hvU hvB
    have S' := S.reselect_sylow D A hg R (hBR hgB)
    exact ⟨_, S'.invariantSelection_of_small_invariant_inverter D A hTV hTI
      (S.alternatives_of_sylow halt R) hg hv hvU hi hvR⟩

end CyclicConstructionSeed
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
