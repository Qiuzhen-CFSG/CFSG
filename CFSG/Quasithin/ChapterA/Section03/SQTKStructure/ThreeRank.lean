module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.CComponentCommutation
public import Theory.SpecificGroups.SL2.PrimeFieldOddSubgroups
public import Theory.GroupTheory.PrimeRankSylow
public import Theory.Quasithin.CoprimeRank

/-!
# Three-rank two forces a quasisimple C-component head

The noncentral-Fitting alternatives of A.3.6 have Fitting subgroup of order
prime to three and prime-field SL₂ quotient. Its odd Sylow subgroups are
cyclic, so these alternatives have three-rank at most one. Rank at least
two therefore forces quasisimplicity. Odd-prime rank is unchanged when
passing to the actual two-core quotient.

The rank calculations are extracted from the checked intrinsic argument in
Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.
RankTwo.LocalApplication.Intrinsic; the completed A.3.6 noncentral theorem
discharges its earlier structural premise here.

Source: Aschbacher--Smith, A.3.6 and 1.2.1(4), printed pp.43--45 and504;
used by the fixed-coset component argument in 3.3.22, printed p.597.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03
open Chapter1.Section02 Chapter1.Section02.LocalModels
private theorem rank_sl_two_prime {B : Type*} [Group B] [Finite B]
    {p : ℕ} (hp : p.Prime) (h : IsSL B 2 p) : primeRank 3 B ≤ 1 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let : Fact p.Prime := ⟨hp⟩
  let := Fintype.ofFinite F
  let c : F ≃+* ZMod p :=
    (ZMod.ringEquivOfPrime F hp (by simpa only [← Nat.card_eq_fintype_card] using hF)).symm
  let m := Matrix.SpecialLinearGroup.map (n := Fin 2) c.toRingHom
  have hm : Function.Injective m := by
    intro x y he
    apply Subtype.ext
    ext i j
    apply c.injective
    exact congrArg (fun a : SL(2, ZMod p) => a.val i j) he
  let P : Sylow 3 B := Classical.choice inferInstance
  apply P.primeRank_le_one_of_isCyclic
  exact Matrix.SpecialLinearGroup.isCyclic_of_odd_pGroup_injective_primeField
    P.isPGroup' (by decide) (m.comp (e.toMonoidHom.comp (P : Subgroup B).subtype))
    (hm.comp (e.injective.comp (P : Subgroup B).subtype_injective))

private theorem rank_natural {B : Type*} [Group B] [Finite B]
    (h : A36Natural B) : primeRank 3 B ≤ 1 := by
  obtain ⟨p, hp, hlarge, F, _, _, hc, e, f, _⟩ := h.2
  have hn : Nat.Coprime 3 (Nat.card (generalizedFitting B)) := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.Coprime 3 (Nat.card (Fin 2 → F))
    rw [Nat.card_fun, Nat.card_fin, hc]
    exact (Nat.prime_three.coprime_iff_not_dvd.mpr
      (fun hd => (hp.eq_one_or_self_of_dvd 3 hd).elim (by decide) (by omega))).pow_right 2
  have hb := primeRank_le_of_coprime_ker 3 (QuotientGroup.mk' (generalizedFitting B))
    (by rwa [QuotientGroup.ker_mk'])
  exact hb.trans (rank_sl_two_prime hp ⟨F, inferInstance, inferInstance, hc, ⟨f⟩⟩)

private theorem rank_nilpotent {B : Type*} [Group B] [Finite B]
    (h : A36Nilpotent B) : primeRank 3 B ≤ 1 := by
  have hn : Nat.Coprime 3 (Nat.card (generalizedFitting B)) := by
    apply Nat.prime_three.coprime_iff_not_dvd.mpr
    intro hd
    have hh := (h.2.2.2 3 (by decide) hd).1
    norm_num at hh
  exact (primeRank_le_of_coprime_ker 3 (QuotientGroup.mk' (generalizedFitting B))
    (by rwa [QuotientGroup.ker_mk'])).trans (rank_sl_two_prime (by decide) h.2.2.1)


/-- Rank at least two excludes both noncentral-Fitting alternatives of A.3.6. -/
theorem cComponent_quasisimple_of_three_rank
    {G : Type*} [Group G] [Finite G] {κ : GroupClass}
    (hG : IsSQTK κ G) (hO : pCore 2 G = ⊥)
    {B : Subgroup G} (hB : B.IsCComponent) (hr : 2 ≤ primeRank 3 B) :
    IsQuasisimple B := by
  have hf : fittingSubgroup B ≤ center B := by
    by_contra hn
    obtain ⟨ha,_⟩ := CComponentCommutation.noncentralStructureInput κ G hG hO B hB hn
    rcases ha with hnat | hnil
    · have := rank_natural hnat
      omega
    · have := rank_nilpotent hnil
      omega
  have hs : solvableRadical B = center B := le_antisymm
    (solvableRadical_le_center_of_fitting_le_center hf)
    (le_solvableRadical _ inferInstance
      (Group.isSolvable_of_comm fun a b => Subtype.ext (mem_center_iff.mp a.property b).symm))
  let := hB.perfect
  let := hB.isSimpleGroup_quotient_solvableRadical
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hs).symm.isSimpleGroup⟩

/-- In an arbitrary SQTK group, the actual two-core quotient of a rank-two
C-component is quasisimple. -/
theorem cComponent_twoCore_quasisimple_of_three_rank
    {G : Type*} [Group G] [Finite G] {κ : GroupClass}
    (hG : IsSQTK κ G) {B : Subgroup G} (hB : B.IsCComponent)
    (hr : 2 ≤ primeRank 3 B) : IsQuasisimple (B ⧸ pCore 2 B) := by
  have hQ : IsSQTK κ (G ⧸ pCore 2 G) := by
    refine ⟨?_,hG.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 G) pCore_isPGroup).trans
      (hG.stronglyQuasithin p hp ho)
  let : Group.IsNilpotent (pCore 2 G) := pCore_isNilpotent
  let e := cComponentTwoCoreQuotientEquiv hB
  have hbar := hB.map_quotient (pCore 2 G)
  have hrbar : 2 ≤ primeRank 3 (B.map (QuotientGroup.mk' (pCore 2 G))) := by
    rw [← primeRank_equiv 3 e, primeRank_quotient_eq_of_isTwoGroup 3 (by decide)
      (pCore 2 B) pCore_isPGroup]
    exact hr
  let := cComponent_quasisimple_of_three_rank hQ (pCore_quotient_pCore_eq_bot 2) hbar hrbar
  exact IsQuasisimple.of_mulEquiv e.symm
end CFSG.Quasithin.ChapterA.Section03
