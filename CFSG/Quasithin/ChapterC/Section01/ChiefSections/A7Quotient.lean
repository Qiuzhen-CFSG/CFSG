module

public import CFSG.Quasithin.ChapterC.Section01.ChiefSections
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.PResidual.PerfectLift
public import Theory.GroupTheory.CentralPChiefFactorsOddQuotient
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# Central chief factors above the A7 moving layer

Let J embed in E, with actual core quotients A5 and A7 respectively, and
assume J is two-perfect. The image H of J in A7 has the same A5 core
quotient because the kernel is a two-group. Thus |O₂(H)| divides 42 and
is a power of two, so it is one or two. Its normality makes it central.
Two-perfectness then makes H a perfect central cover of A5.

The literal quotient J/(J ∩ U(E)) maps onto H with central two-group
kernel: U(E) = [O₂(E), E] kills the commutators of that kernel with J.
A second perfect central cover is therefore quasisimple and has only
central binary chief factors. This discharges the quotient premise of
`chiefPairEmbedding` for the original embedding J → E.

The quotient argument needs none of the additional short-group conditions;
in particular it applies to both ordinary and exceptional A7 blocks,
without a module order bound or normality of J in E.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), C.1.7--8,
C.1.22 and the A7 exclusion in 14.7.68(2), printed pp.123, 129, 1071--1072.
-/

public section

open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC

private theorem a5_quasisimple : IsQuasisimple (alternatingGroup (Fin 5)) where
  toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  simple := by
    let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    exact ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup

private theorem image_quasisimple {J : Type*} [Group J] [Finite J]
    (hp : IsPPerfect 2 J) (eJ : (J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5))
    (f : J →* alternatingGroup (Fin 7)) (hk : IsPGroup 2 f.ker) :
    IsQuasisimple f.range := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsQuasisimple (alternatingGroup (Fin 5)) := a5_quasisimple
  have hk' : IsPGroup 2 f.rangeRestrict.ker := by
    rwa [MonoidHom.ker_rangeRestrict]
  let e : (f.range ⧸ pCore 2 f.range) ≃* alternatingGroup (Fin 5) :=
    (f.rangeRestrict.pCoreQuotientEquiv f.rangeRestrict_surjective hk').symm.trans eJ
  have h60 : Nat.card (f.range ⧸ pCore 2 f.range) = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hd : Nat.card f.range ∣ 2520 := by
    have hc : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    exact hc ▸ f.range.card_subgroup_dvd_card
  have h42 : Nat.card (pCore 2 f.range) ∣ 42 := by
    have hc := card_eq_card_quotient_mul_card_subgroup (pCore 2 f.range)
    rw [h60] at hc
    rw [hc] at hd
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 60)).mp hd
  have hcop : Nat.Coprime (Nat.card (pCore 2 f.range)) 21 := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := f.range)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 21).pow_left n
  have hc : pCore 2 f.range ≤ center f.range := by
    have htwo : Nat.card (pCore 2 f.range) ∣ 2 := hcop.dvd_mul_right.mp h42
    rcases (Nat.dvd_prime Nat.prime_two).mp htwo with h1 | h2
    · rw [card_eq_one.mp h1]
      exact bot_le
    · exact central_of_normal_card_two _ h2
  let : IsQuasisimple (f.range ⧸ pCore 2 f.range) := IsQuasisimple.of_mulEquiv e.symm
  have hpr : IsPPerfect 2 f.range := hp.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let q := QuotientGroup.mk' (pCore 2 f.range)
  have hqk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  let : Group.IsPerfect f.range :=
    hpr.isPerfect_of_surjective_pGroup_kernel q (QuotientGroup.mk'_surjective _) hqk
  exact (show PerfectCentralCovering.Cover f.range (f.range ⧸ pCore 2 f.range) from
    { toMonoidHom := q
      surjective := QuotientGroup.mk'_surjective _
      ker_le_center := by simpa only [q, QuotientGroup.ker_mk'] using hc
      isPerfect := inferInstance }).isQuasisimple

variable {E J : Type*} [Group E] [Group J] [Finite J]

/-- The actual quotient above the moving-layer intersection is quasisimple.
The marking uses E/O₂(E), not the quotient by a module-action kernel. -/
theorem a7_blockIntersection_quotient_quasisimple (ι : J →* E)
    (hι : Function.Injective ι)
    (eE : (E ⧸ pCore 2 E) ≃* alternatingGroup (Fin 7))
    (eJ : (J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5))
    (hp : IsPPerfect 2 J) : IsQuasisimple (J ⧸ (blockU E).comap ι) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : J →* alternatingGroup (Fin 7) :=
    eE.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 E)).comp ι)
  have hker : f.ker = (pCore 2 E).comap ι := by
    ext j
    change eE ((QuotientGroup.mk' (pCore 2 E)) (ι j)) = 1 ↔ ι j ∈ pCore 2 E
    rw [eE.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff (ι j)
  have hk : IsPGroup 2 f.ker := by
    rw [hker]
    exact pCore_isPGroup.comap_of_injective ι hι
  let : IsQuasisimple f.range := image_quasisimple hp eJ f hk
  let N := (blockU E).comap ι
  have hN : N ≤ f.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict, hker]
    exact comap_mono blockU_le_core
  let q : (J ⧸ N) →* f.range := QuotientGroup.lift N f.rangeRestrict hN
  have hq : Function.Surjective q :=
    QuotientGroup.lift_surjective_of_surjective N f.rangeRestrict f.rangeRestrict_surjective hN
  have hqk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_lift, MonoidHom.ker_rangeRestrict]
    exact hk.map _
  have hqc : q.ker ≤ center (J ⧸ N) := by
    rw [QuotientGroup.ker_lift, MonoidHom.ker_rangeRestrict]
    apply (map_mk_le_center_iff N f.ker).mpr
    rw [commutator_le]
    intro j _ k hk
    change ι ⁅j, k⁆ ∈ blockU E
    rw [map_commutatorElement]
    change ⁅ι j, ι k⁆ ∈ ⁅pCore 2 E, (⊤ : Subgroup E)⁆
    rw [commutator_comm]
    have hkE : ι k ∈ pCore 2 E := by
      change k ∈ (pCore 2 E).comap ι
      rwa [← hker]
    exact commutator_mem_commutator (mem_top _) hkE
  have hpq : IsPPerfect 2 (J ⧸ N) :=
    hp.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  let : Group.IsPerfect (J ⧸ N) := hpq.isPerfect_of_surjective_pGroup_kernel q hq hqk
  exact (show PerfectCentralCovering.Cover (J ⧸ N) f.range from
    { toMonoidHom := q, surjective := hq, ker_le_center := hqc,
      isPerfect := inferInstance }).isQuasisimple

/-- Every binary chief factor above J ∩ U(E) is central, for either A7 block type. -/
theorem a7_blockIntersection_hasCentralTwoChiefFactors (ι : J →* E)
    (hι : Function.Injective ι)
    (eE : (E ⧸ pCore 2 E) ≃* alternatingGroup (Fin 7))
    (eJ : (J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5))
    (hp : IsPPerfect 2 J) : HasCentralPChiefFactors 2 (J ⧸ (blockU E).comap ι) := by
  let X := J ⧸ (blockU E).comap ι
  let : IsQuasisimple X := a7_blockIntersection_quotient_quasisimple ι hι eE eJ hp
  apply hasCentralTwoChiefFactors_of_odd_normal_quasisimple_quotient (⊥ : Subgroup X)
  · simp
  · exact IsQuasisimple.of_mulEquiv QuotientGroup.quotientBot.symm

open NoncentralChiefRefinement

/-- Every noncentral binary chief section survives in the literal intersection
filtration with its original J-action, under the actual A5/A7 core markings. -/
@[expose] noncomputable def a7_chiefIntersectionEquiv (ι : J →* E)
    (hι : Function.Injective ι)
    (eE : (E ⧸ pCore 2 E) ≃* alternatingGroup (Fin 7))
    (eJ : (J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5))
    (hp : IsPPerfect 2 J)
    (s : ChiefSeries J) (i : Fin s.length)
    (hi : IsNoncentralTwo (s i.castSucc) (s i.succ)) :
    SectionEquiv ((s.intersectionFiltration (blockIntersection ι)).term i.castSucc)
      ((s.intersectionFiltration (blockIntersection ι)).term i.succ)
      (s i.castSucc) (s i.succ) :=
  chiefIntersectionEquiv ι (a7_blockIntersection_hasCentralTwoChiefFactors ι hι eE eJ hp)
    s i hi

/-- The A5/A7 core markings discharge the chief-pair embedding's quotient premise,
using the same original inclusion and the literal block-module projection. -/
@[expose] noncomputable def a7_chiefPairEmbedding (ι : J →* E) (hι : Function.Injective ι)
    (eE : (E ⧸ pCore 2 E) ≃* alternatingGroup (Fin 7))
    (eJ : (J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5))
    (hp : IsPPerfect 2 J)
    (s : ChiefSeries J) (i j : Fin s.length) (hij : i ≠ j)
    (hi : IsNoncentralTwo (s i.castSucc) (s i.succ))
    (hj : IsNoncentralTwo (s j.castSucc) (s j.succ)) :
    Section (s i.castSucc) (s i.succ) × Section (s j.castSucc) (s j.succ) ↪ BlockModule E :=
  chiefPairEmbedding ι hι (a7_blockIntersection_hasCentralTwoChiefFactors ι hι eE eJ hp)
    s i j hij hi hj

end CFSG.Quasithin.ChapterC
