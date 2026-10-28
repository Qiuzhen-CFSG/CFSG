module
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.RightHall
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.ActionEscape
public import Theory.SpecificGroups.PSL2.PrimeCoverCartanNormalizer
public import Theory.SpecificGroups.PSL2.TwentyFiveCartanNormalizer
public import Theory.GroupTheory.PrimeRankOrderBound

/-!
# Cubic actors in normal rank-one containing components

When the residual has its actual A₅ two-core quotient, the prescribed
right Hall subgroup B is cubic. Every cubic D of the left Cartan
centralizes B, so DB is elementary abelian. A centerless containing
quotient of three-rank one with two-group outer automorphisms has action
image of order at most three. The embedded B fills that image. Its kernel
normalizes the perfect residual because the containing two-core lies in
the original Sylow. Hence D normalizes the residual.

The prime-field PSL₂ and PSL₂(25) applications discharge the rank,
center and outer-group premises with their actual models. Normality is
relative to Y, and the left exponent is unrestricted.
Source: Aschbacher–Smith 5.1.13, printed p.636.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
variable {G : Type*} [Group G] [Finite G]

/-- The literal quotient action excludes a cubic escape in a rank-one three-section. -/
theorem cubic_normalizes_of_rank_one_container
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hHY : H ≤ Y) (hXY : X ≤ Y) (hXn : (X.subgroupOf Y).Normal)
    (hKX : residual H ≤ X)
    (hA5 : Nonempty ((residual H ⧸ pCore 2 (residual H)) ≃* alternatingGroup (Fin 5)))
    (hz : center (X ⧸ pCore 2 X) = ⊥)
    (hout : IsPGroup 2 (MulAut.Outer (X ⧸ pCore 2 X)))
    (hr : primeRank 3 X ≤ 1)
    (hDA : D ≤ A) (hDY : D ≤ Y) (hDc : Nat.card D = 3) :
    D ≤ normalizer (residual H : Set G) := by
  have hBc := right_hall_card_three_of_residual_A5 h hH hgen c hA5
  let : IsCyclic D := isCyclic_of_prime_card hDc
  let : IsCyclic B := isCyclic_of_prime_card hBc
  let : IsElementaryAbelian 3 D := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun d => by
      simpa only [hDc] using (pow_card_eq_one' (x := d))) }
  let : IsElementaryAbelian 3 B := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun b => by
      simpa only [hBc] using (pow_card_eq_one' (x := b))) }
  have hc := c.centralizes_fermat_actor h (Or.inl rfl) hDA hDc
  let : IsElementaryAbelian 3 (D ⊔ B : Subgroup G) := IsElementaryAbelian.sup_of_le_centralizer hc
  let : Group.IsPerfect (residual H) := residual_perfect h.qtke h.sylow_normalizes hH hgen
  have hYN : Y ≤ normalizer (X : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hXY).mp hXn
  have hTX := (hH.1.1.2.trans hHY).trans hYN
  obtain ⟨P,hP⟩ := exists_sylow_component hTX
  have hQK : X.pCoreIn 2 ≤ normalizer (residual H : Set G) :=
    ((pCoreIn_le_sylow X P).trans_eq hP).trans
      (inf_le_left.trans (hH.1.1.2.trans (le_normalizer_residual H)))
  have hn := CubicCoreQuotientNormalizer.normalizes_of_rank_one
    (residual H) X (D ⊔ B) B hKX
    ((sup_le hDY ((c.right_le.trans inf_le_right).trans hHY)).trans hYN)
    le_sup_right (Global.right_cartan_le_residual c) hQK hBc hz hout hr
  exact le_sup_left.trans hn

/-- Every cubic normalizes the A₅ residual in an odd prime-field PSL₂ container. -/
theorem cubic_normalizes_of_prime_container
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hHY : H ≤ Y) (hXY : X ≤ Y) (hXn : (X.subgroupOf Y).Normal)
    (hKX : residual H ≤ X)
    (hA5 : Nonempty ((residual H ⧸ pCore 2 (residual H)) ≃* alternatingGroup (Fin 5)))
    (hp : p.Prime) (ho : Odd p) (hm : ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 2 p)
    (hDA : D ≤ A) (hDY : D ≤ Y) (hDc : Nat.card D = 3) :
    D ≤ normalizer (residual H : Set G) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  obtain ⟨hz,hout⟩ := Theory.PSL2.primeField_center_outer_of_equiv hp ho hF e
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, hF, ZMod.card])
  have hr : primeRank 3 X ≤ 1 := by
    rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 X) pCore_isPGroup,
      primeRank_congr 3 (e.trans (GorensteinWalter.psl2RingEquiv eF))]
    exact Theory.PSL2.primeField_odd_rank (by decide)
  exact cubic_normalizes_of_rank_one_container h hH hgen c hHY hXY hXn hKX
    hA5 hz hout hr hDA hDY hDc

/-- Every cubic normalizes the A₅ residual in a PSL₂(25) container. -/
theorem cubic_normalizes_of_twentyFive_container
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hHY : H ≤ Y) (hXY : X ≤ Y) (hXn : (X.subgroupOf Y).Normal)
    (hKX : residual H ≤ X)
    (hA5 : Nonempty ((residual H ⧸ pCore 2 (residual H)) ≃* alternatingGroup (Fin 5)))
    (hm : ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 2 25)
    (hDA : D ≤ A) (hDY : D ≤ Y) (hDc : Nat.card D = 3) :
    D ≤ normalizer (residual H : Set G) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have hz : center (X ⧸ pCore 2 X) = ⊥ := by
    apply bot_unique
    intro z hz
    have hh : e z ∈ center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      (centerCongr e ⟨z,hz⟩).property
    rw [GorensteinWalter.psl2_center_eq_bot F,mem_bot] at hh
    exact e.injective (hh.trans e.map_one.symm)
  have hout : IsPGroup 2 (MulAut.Outer (X ⧸ pCore 2 X)) :=
    (Theory.PSL2.OuterSolvable.SmallDegreeSquares.outer_isPGroup_two
      (by decide : Nat.Prime 5) (by decide : Odd 5) (by decide : 2 ≤ 2)
      (show Nat.card F = 5 ^ 2 from hF)).of_equiv (MulAut.outerCongr e).symm
  have hr : primeRank 3 X ≤ 1 := by
    rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 X) pCore_isPGroup,
      primeRank_congr 3 e]
    apply primeRank_le_of_prime_pow_not_dvd
    rw [Theory.PSL2.TwentyFive.card hF]
    decide
  exact cubic_normalizes_of_rank_one_container h hH hgen c hHY hXY hXn hKX
    hA5 hz hout hr hDA hDY hDc

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
