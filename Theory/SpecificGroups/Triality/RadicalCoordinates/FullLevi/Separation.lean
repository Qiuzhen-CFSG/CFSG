module

public import Theory.SpecificGroups.Triality.RadicalCoordinates.FullLevi.Normalization
public import Theory.SpecificGroups.Triality.LeviIdentification
public import Theory.GroupTheory.PCoreProduct
public import Theory.GroupTheory.PCorePrimeToIndex
/-!
# Trivial two-core and radical separation for the full split Levi

The pinned rank-one maps identify the central subsystem with SL₂ and the arms
with a direct product of three SL₂ groups. In characteristic two these groups
have trivial center and two-core, including the binary endpoint. The full
Levi contains this subsystem normally with odd index, since the coroot torus
has odd order. Its two-core therefore vanishes. Relative normality of the
root radical in the parabolic makes its intersection with the full Levi a
normal two-subgroup, proving separation.

Source: GLS3 Theorem 2.6.5(f,g) (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section

open scoped MatrixGroups
namespace Triality.Standard.RadicalCoordinates
open Parabolics ConcreteBruhat TorusCoordinates
noncomputable section

private theorem center_eq_bot_of_equiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (hc : Subgroup.center G = ⊥) : Subgroup.center H = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro h hh
  have hg : e.symm h ∈ Subgroup.center G := by
    apply Subgroup.mem_center_iff.mpr
    intro g
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      Subgroup.mem_center_iff.mp hh (e g)
  have he : e.symm h = 1 := by simpa only [hc, Subgroup.mem_bot] using hg
  exact (e.symm.injective (he.trans e.symm.map_one.symm))

theorem splitLevi_center_eq_bot (P : Parameters) (hp : P.prime = 2) (a : Node) :
    Subgroup.center (splitLevi P a) = ⊥ := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  let D := pinnedRankOneMaps P hp
  cases a
  · let C := armRootCommutation P hp
    let e := (MonoidHom.ofInjective (D.armsProduct_injective C)).trans
      (MulEquiv.subgroupCongr (D.range_armsProduct C))
    apply center_eq_bot_of_equiv e
    rw [Subgroup.center_prod, Subgroup.center_prod, Theory.PSL2.sl2_center_eq_bot,
      Subgroup.bot_prod_bot, Subgroup.bot_prod_bot]
  · let e := (MonoidHom.ofInjective (D.injective 1)).trans
      (MulEquiv.subgroupCongr D.range_central)
    exact center_eq_bot_of_equiv e (Theory.PSL2.sl2_center_eq_bot _)

private theorem pCore_eq_bot_of_equiv {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] (e : G ≃* H) (hc : pCore 2 G = ⊥) : pCore 2 H = ⊥ := by
  rw [← pCore_map_iso 2 e, hc, Subgroup.map_bot]

theorem splitLevi_twoCore_eq_bot (P : Parameters) (hp : P.prime = 2) (a : Node) :
    pCore 2 (splitLevi P a) = ⊥ := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  let D := pinnedRankOneMaps P hp
  cases a
  · let C := armRootCommutation P hp
    let e := (MonoidHom.ofInjective (D.armsProduct_injective C)).trans
      (MulEquiv.subgroupCongr (D.range_armsProduct C))
    apply pCore_eq_bot_of_equiv e
    rw [Subgroup.pCore_prod, Subgroup.pCore_prod,
      Matrix.SL2.twoCore_eq_bot, Subgroup.bot_prod_bot, Subgroup.bot_prod_bot]
  · let e := (MonoidHom.ofInjective (D.injective 1)).trans
      (MulEquiv.subgroupCongr D.range_central)
    exact pCore_eq_bot_of_equiv e (Matrix.SL2.twoCore_eq_bot _)

theorem odd_card_splitTorus (P : Parameters) (hp : P.prime = 2) :
    Odd (Nat.card (splitTorus P)) := by
  rw [card_splitTorus P hp]
  exact ((Nat.odd_mul.mp (odd_torus_order P hp)).1).pow

private theorem pCore_sup_eq_bot_of_odd {G : Type*} [Group G] [Finite G]
    (A B : Subgroup G) (hBA : B ≤ Subgroup.normalizer A)
    (hA : pCore 2 A = ⊥) (hB : Odd (Nat.card B)) : pCore 2 (A ⊔ B : Subgroup G) = ⊥ := by
  let J := A ⊔ B
  let L := A.subgroupOf J
  let T := B.subgroupOf J
  have hL : A ≤ J := le_sup_left
  have hT : B ≤ J := le_sup_right
  have hN : L.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hL).mpr
    (sup_le A.le_normalizer hBA)
  let := hN
  have hgen : L ⊔ T = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hL hT]
    exact Subgroup.subgroupOf_self _
  have hcT : Odd (Nat.card T) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT).toEquiv]
    exact hB
  have hi : ¬ 2 ∣ L.index := by
    apply Nat.prime_two.coprime_iff_not_dvd.mp
    rw [← Subgroup.relIndex_top_right L, ← hgen, Subgroup.relIndex_sup_left]
    exact hcT.coprime_two_left.coprime_dvd_right (Subgroup.relIndex_dvd_card L T)
  have hcore : pCore 2 L = ⊥ :=
    pCore_eq_bot_of_equiv (Subgroup.subgroupOfEquivOfLe hL).symm hA
  apply bot_unique
  have h := pCore_le_map_pCore_of_prime_not_dvd_index L hi
  rwa [hcore, Subgroup.map_bot] at h

theorem splitFullLevi_twoCore_eq_bot (P : Parameters) (hp : P.prime = 2) (a : Node) :
    pCore 2 (splitFullLevi P a) = ⊥ :=
  pCore_sup_eq_bot_of_odd (splitLevi P a) (splitTorus P)
    (splitTorus_le_normalizer_splitLevi P hp a)
    (splitLevi_twoCore_eq_bot P hp a) (odd_card_splitTorus P hp)

theorem disjoint_rootSubgroup_splitFullLevi_of_normal (P : Parameters)
    (hp : P.prime = 2) (a : Node)
    (hN : ((rootSubgroup P a).subgroupOf (splitParabolic P a)).Normal) :
    Disjoint (rootSubgroup P a) (splitFullLevi P a) := by
  have hRP := (rootSubgroup_le_splitRadical P hp a).trans (splitRadical_le_splitParabolic P a)
  have hRN : ((rootSubgroup P a).subgroupOf (splitFullLevi P a)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      ((splitFullLevi_le_splitParabolic P a).trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hRP).mp hN))
  have hc : (rootSubgroup P a).subgroupOf (splitFullLevi P a) ≤
      pCore 2 (splitFullLevi P a) :=
    le_sSup ⟨hRN, (isPGroup_rootSubgroup P hp a).comap_subtype⟩
  rw [splitFullLevi_twoCore_eq_bot P hp a] at hc
  apply Subgroup.disjoint_def.mpr
  intro g hg hj
  exact congrArg Subtype.val (Subgroup.mem_bot.mp
    (hc (show (⟨g, hj⟩ : splitFullLevi P a) ∈
      (rootSubgroup P a).subgroupOf (splitFullLevi P a) from hg)))

end
end Triality.Standard.RadicalCoordinates
