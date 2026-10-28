module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.RadicalRankTwoSeed
public import CFSG.KnownSimple.PrimeToFifteen
public import Theory.GroupTheory.CComponent.RadicalPairOrder

/-!
# Identifying a Mathieu cubic-centralizer residual

An M₂₂ radical quotient exhausts the semisimple three-rank of an SQTK
ambient group. A distinct C-component therefore has three-free radical
quotient. If 25 does not divide the ambient order, the independent component
order product also makes that quotient five-free. The full known-simple
K-group theorem makes it solvable, contradicting its nonabelian simplicity.
Thus the Mathieu component is unique, and the proved component generation
identifies it with the whole solvable residual.

The exterior pushing-up application uses the original full J₄ cover. Its
center is a two-group and J₄ has a single factor five, so the order premise
holds in the prescribed cubic centralizer without discarding the cover.
Source: Aschbacher--Smith, 4.2.13, printed p.612, and 1.2.1(1), p.504.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section02
variable {G : Type*} [Group G] [Finite G]

private def radicalImageEquiv (B : Subgroup G) (hB : B.IsCComponent) :
    (B ⧸ solvableRadical B) ≃* B.map (QuotientGroup.mk' (solvableRadical G)) := by
  let q := QuotientGroup.mk' (solvableRadical G)
  let f := q.subgroupMap B
  let : Group.IsSolvable f.ker := by
    rw [show f = q.subgroupMap B from rfl,ker_subgroupMap,QuotientGroup.ker_mk']
    exact Group.isSolvable_of_isSolvable_injective
      (f := B.subtype.subgroupComap (solvableRadical G))
      (fun a b he => Subtype.ext (Subtype.ext
        (congrArg (fun x : solvableRadical G => (x : G)) he)))
  have hr := solvableRadical_eq_bot_of_isSubnormal
    (solvableRadical_quotient_solvableRadical (G := G)) (hB.map_quotient _).subnormal
  exact (solvableRadicalQuotientEquiv f (q.subgroupMap_surjective B)).trans
    ((QuotientGroup.quotientMulEquivOfEq hr).trans QuotientGroup.quotientBot)

private theorem other_radical_three_free
    (hG : IsSQTK KnownSimple.IsKnownSimple G) {B D : Subgroup G}
    (hB : B.IsCComponent) (hD : D.IsCComponent) (hne : B ≠ D)
    (hr : 2 ≤ primeRank 3 (B ⧸ solvableRadical B)) :
    Nat.Coprime 3 (Nat.card (D ⧸ solvableRadical D)) := by
  let q := QuotientGroup.mk' (solvableRadical G)
  let X := B.map q
  let Y := D.map q
  have hX := hB.map_quotient (solvableRadical G)
  have hY := hD.map_quotient (solvableRadical G)
  have hfree := solvableRadical_quotient_solvableRadical (G := G)
  have hc := hX.commutator_eq_bot_of_ne_of_solvableRadical_eq_bot hfree hY
    (fun he => hne (hB.eq_of_map_quotient_eq hD _ he))
  have hd := hX.disjoint_of_commutator_eq_bot_of_solvableRadical_eq_bot hfree hc
  have hadd := X.primeRank_sup_eq_add_of_disjoint_commuting Y hd
    (commutator_eq_bot_iff_le_centralizer.mp hc) 3
  have hbound := (primeRank_mono 3 (sup_le (le_cComponentLayer hX)
    (le_cComponentLayer hY))).trans (Chapter1.Section02.radical_layer_threeRank hG)
  change primeRank 3 (X ⊔ Y : Subgroup _) ≤ 2 at hbound
  have hrX : 2 ≤ primeRank 3 X := by
    rwa [←primeRank_equiv 3 (radicalImageEquiv B hB)]
  have hy : primeRank 3 Y = 0 := by omega
  apply Nat.prime_three.coprime_iff_not_dvd.mpr
  apply PrimeRank.eq_zero_iff_not_dvd_card.mp
  rwa [primeRank_equiv 3 (radicalImageEquiv D hD)]

/-- An M₂₂ radical quotient is the only component when the ambient
order has only one factor five. -/
theorem mathieu_component_unique
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (h25 : ¬ 25 ∣ Nat.card G)
    {B : Subgroup G} (hB : B.IsCComponent)
    (e : (B ⧸ solvableRadical B) ≃* Sporadic.Mathieu.M22)
    {D : Subgroup G} (hD : D.IsCComponent) : D = B := by
  by_contra hne
  have h3 := other_radical_three_free hG hB hD (Ne.symm hne) (by
    rw [primeRank_equiv 3 e,Sporadic.Mathieu.m22_primeRank_three])
  have h5 : Nat.Coprime 5 (Nat.card (D ⧸ solvableRadical D)) := by
    apply Nat.prime_five.coprime_iff_not_dvd.mpr
    intro hd
    apply h25
    have hm : 5 ∣ Nat.card (B ⧸ solvableRadical B) := by
      rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m22_order]
      decide
    exact (Nat.mul_dvd_mul hm hd).trans
      (hB.radical_quotient_card_mul_dvd hD (Ne.symm hne))
  have hs := KnownSimple.isSolvable_of_coprime_three_five _
    ((hG.isKGroup.subgroup D).quotient _) h3 h5
  let := hD.perfect
  let := hD.isSimpleGroup_quotient_solvableRadical
  exact Group.IsPerfect.not_isSolvable (D ⧸ solvableRadical D) hs

/-- The full solvable residual, rather than an arbitrary contained seed,
is the specified Mathieu component. -/
theorem mathieu_component_eq_solvableResidual
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (h25 : ¬ 25 ∣ Nat.card G)
    {B : Subgroup G} (hB : B.IsCComponent)
    (e : (B ⧸ solvableRadical B) ≃* Sporadic.Mathieu.M22) :
    solvableResidual G = B := by
  have hQ : IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G) := by
    refine ⟨?_,hG.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hG.stronglyQuasithin p hp ho)
  have hgen : cComponentLayer G = solvableResidual G :=
    Chapter1.Section02.proposition_1_2_1_one_of_A_3_9
      (fun X _ _ hX hO => ChapterA.Section03.SourceComponents.generation
        (fun Y _ _ => ChapterA.Section02.theoremA_knownSimple (G := Y))
        (ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC
          (fun Y _ _ => ChapterA.Section02.theoremC_knownSimple (G := Y))) hX hO)
      hQ
  rw [←hgen]
  exact le_antisymm (sSup_le fun D hD =>
    (mathieu_component_unique hG h25 hB e hD).le) (le_cComponentLayer hB)

end CFSG.Quasithin.Chapter4.Section02
