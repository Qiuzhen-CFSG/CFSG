module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Pushing
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.FixedSpaces.Quotient
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.PrimeRankZero

/-!
# All odd primes in the containing-component pair

Distinct containing C-components commute after quotienting by the ambient
two-core. The original factor has simple two-core quotient, so its image has
two-group center. Rank addition therefore bounds the other component by one
at every odd prime dividing the original quotient, not just at three or five.
The original factor also supplies the reverse inequality and retains each of
these primes in the containing component's intrinsic two-core quotient.

Distinctness is an explicit, still independent A.3.12 input here.
Source: Aschbacher--Smith, 10.2.6, printed pp.748--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}

namespace ContainingPair

theorem left_le (C : ContainingPair D H t K₁ K₂) : L ≤ H :=
  (le_componentOrbit L T).trans (le_sup_left.trans C.half_le)

theorem right_le (C : ContainingPair D H t K₁ K₂) :
    L.map (MulAut.conj t).toMonoidHom ≤ H :=
  (le_sup_right.trans C.orbit_eq.ge).trans (le_sup_left.trans C.half_le)

/-- Conjugation and inclusion identify the literal second factor with L. -/
def rightEquiv (C : ContainingPair D H t K₁ K₂) :
    L ≃* (L.map (MulAut.conj t).toMonoidHom).subgroupOf H :=
  ((MulAut.conj t).subgroupMap L).trans (subgroupOfEquivOfLe C.right_le).symm

end ContainingPair

private theorem center_le_twoCore {X : Type*} [Group X]
    [IsSimpleGroup (X ⧸ pCore 2 X)] [IsQuasisimple (X ⧸ pCore 2 X)] :
    center X ≤ pCore 2 X := by
  have hz : center (X ⧸ pCore 2 X) = ⊥ :=
    (inferInstance : (center (X ⧸ pCore 2 X)).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative (X ⧸ pCore 2 X)
        (center_eq_top_iff.mp he))
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  have hh : QuotientGroup.mk' (pCore 2 X) x ∈ center (X ⧸ pCore 2 X) := by
    apply mem_center_iff.mpr
    intro a
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) a
    simpa only [map_mul] using
      congrArg (QuotientGroup.mk' (pCore 2 X)) (mem_center_iff.mp hx y)
  simpa only [hz,mem_bot,QuotientGroup.mk'_apply] using hh

private theorem other_component_rank
    {X : Type*} [Group X] [Finite X] (hX : IsSQTK KnownSimple.IsKnownSimple X)
    {I J B : Subgroup X} (hI : I.IsCComponent) (hJ : J.IsCComponent)
    (hne : I ≠ J) (hBJ : B ≤ J)
    [IsSimpleGroup (B ⧸ pCore 2 B)] [IsQuasisimple (B ⧸ pCore 2 B)]
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hp : p ∣ Nat.card (B ⧸ pCore 2 B)) :
    primeRank p I ≤ 1 := by
  let q := QuotientGroup.mk' (pCore 2 X)
  let := pCore_isNilpotent (p := 2) (G := X)
  let E := I.map q
  let F := B.map q
  have hq : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hQ : IsSQTK KnownSimple.IsKnownSimple (X ⧸ pCore 2 X) := by
    refine ⟨?_,hX.isKGroup.quotient _⟩
    intro r hr hor
    let : Fact r.Prime := ⟨hr⟩
    exact (primeRank_quotient_le_of_isTwoGroup r hor _ pCore_isPGroup).trans
      (hX.stronglyQuasithin r hr hor)
  have hcomm : E ≤ centralizer (F : Set (X ⧸ pCore 2 X)) := by
    apply (commutator_eq_bot_iff_le_centralizer.mp
      (ChapterA.Section03.CComponentCommutation.commutator_eq_bot hQ
        (pCore_quotient_pCore_eq_bot 2) (hI.map_quotient _) (hJ.map_quotient _)
        (fun he => hne (hI.eq_of_map_quotient_eq hJ _ he)))).trans
    exact centralizer_le (map_mono hBJ)
  have hk : IsPGroup 2 (q.subgroupMap B).ker := by
    rw [ker_subgroupMap]
    exact hq.comap_of_injective B.subtype B.subtype_injective
  let e := (q.subgroupMap B).pCoreQuotientEquiv (q.subgroupMap_surjective B) hk
  let : IsSimpleGroup (F ⧸ pCore 2 F) := e.symm.isSimpleGroup
  let : IsQuasisimple (F ⧸ pCore 2 F) := IsQuasisimple.of_mulEquiv e
  have hz : Nat.Coprime p (Nat.card (center F)) := by
    obtain ⟨n,hn⟩ := ((pCore_isPGroup (p := 2) (G := F)).to_le center_le_twoCore).exists_card_eq
    rw [hn]
    exact (Nat.coprime_two_right.mpr ho).pow_right n
  have hsum := ResidualCentralizerRank.primeRank_add_le_of_center_coprime E F hcomm hz
  have hpos : 0 < primeRank p (B ⧸ pCore 2 B) :=
    Nat.pos_of_ne_zero (fun he => PrimeRank.eq_zero_iff_not_dvd_card.mp he hp)
  have hF : primeRank p F = primeRank p (B ⧸ pCore 2 B) := by
    rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel ho q hq,
      primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 B) pCore_isPGroup]
  have hE : primeRank p E = primeRank p I :=
    ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel ho q hq I
  have hbound := hQ.stronglyQuasithin p (Fact.out : p.Prime) ho
  omega

private theorem positive_rank_of_quotient_prime
    {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (f : X →* Y) (hf : Function.Injective f)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hp : p ∣ Nat.card (X ⧸ pCore 2 X)) :
    0 < primeRank p Y := by
  have hpos : 0 < primeRank p (X ⧸ pCore 2 X) :=
    Nat.pos_of_ne_zero (fun he => PrimeRank.eq_zero_iff_not_dvd_card.mp he hp)
  rw [primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 X) pCore_isPGroup] at hpos
  exact hpos.trans_le (Theory.GroupTheory.primeRank_le_of_injective p f hf)

/-- The complete odd-prime rank assertion in the first paragraph of 10.2.6,
conditional only on the separate noncontainment/distinctness argument. -/
theorem ContainingPair.odd_ranks (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) (hne : K₁ ≠ K₂)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hp : p ∣ Nat.card (L ⧸ pCore 2 L)) :
    primeRank p K₁ = 1 ∧ primeRank p K₂ = 1 := by
  let e₁ := (subgroupOfEquivOfLe C.left_le).symm
  let e₂ := C.rightEquiv
  let q₁ := QuotientGroup.congr _ _ e₁ (pCore_map_iso 2 e₁)
  let q₂ := QuotientGroup.congr _ _ e₂ (pCore_map_iso 2 e₂)
  let := D.quasisimple
  let := SmallOffender.Recognition.FixedSpaces.quotient_simple D hn
  let : IsQuasisimple ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) :=
    IsQuasisimple.of_mulEquiv q₁
  let : IsSimpleGroup ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) := q₁.symm.isSimpleGroup
  let B := (L.map (MulAut.conj t).toMonoidHom).subgroupOf H
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv q₂
  let : IsSimpleGroup (B ⧸ pCore 2 B) := q₂.symm.isSimpleGroup
  have h₁ := other_component_rank (D.simpleQTKE.twoLocal_sqtk C.maximal.1)
    C.first_component C.second_component hne C.second_le ho
    ((Nat.card_congr q₂.toEquiv) ▸ hp)
  have h₂ := other_component_rank (D.simpleQTKE.twoLocal_sqtk C.maximal.1)
    C.second_component C.first_component hne.symm C.first_le ho
    ((Nat.card_congr q₁.toEquiv) ▸ hp)
  have hl₁ := positive_rank_of_quotient_prime
    ((inclusion C.first_le).comp e₁.toMonoidHom)
    ((inclusion_injective C.first_le).comp e₁.injective) ho hp
  have hl₂ := positive_rank_of_quotient_prime
    ((inclusion C.second_le).comp e₂.toMonoidHom)
    ((inclusion_injective C.second_le).comp e₂.injective) ho hp
  omega

/-- No relevant odd prime is lost in either intrinsic component quotient.
This assertion does not require distinctness of the containing components. -/
theorem ContainingPair.odd_primes_retained (C : ContainingPair D H t K₁ K₂)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hp : p ∣ Nat.card (L ⧸ pCore 2 L)) :
    p ∣ Nat.card (K₁ ⧸ pCore 2 K₁) ∧ p ∣ Nat.card (K₂ ⧸ pCore 2 K₂) := by
  let e₁ := (subgroupOfEquivOfLe C.left_le).symm
  let e₂ := C.rightEquiv
  have h₁ := positive_rank_of_quotient_prime
    ((inclusion C.first_le).comp e₁.toMonoidHom)
    ((inclusion_injective C.first_le).comp e₁.injective) ho hp
  have h₂ := positive_rank_of_quotient_prime
    ((inclusion C.second_le).comp e₂.toMonoidHom)
    ((inclusion_injective C.second_le).comp e₂.injective) ho hp
  constructor <;> by_contra hd
  · have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr hd
    rw [primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 K₁) pCore_isPGroup] at hz
    omega
  · have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr hd
    rw [primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 K₂) pCore_isPGroup] at hz
    omega

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
