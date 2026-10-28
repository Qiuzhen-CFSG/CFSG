module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.CentralizerAction.Quotient
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Geometry.ResidualInvariance.Model
/-!
# Lifting invariance from the rank-two quotient

The moved/fixed calculation identifies the two quotient axes. A residual is
initially only normal in Y. Its conjugate by an element of YS is also normal
in Y, and the two images agree. Equality of normal two-perfect subgroups lifts
through the restricted two-group kernel, proving normality in YS.

This avoids assuming the invariance needed by the residual-direction
classification. Source: Aschbacher–Smith 15.3.23, printed p.1128 (combined
manuscript, 1 March 2004). The component parabolic must still supply the moved
commutator identity; the fixed direction uses a two-core bound.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.ResidualInvariance
variable {G Q : Type*} [Group G] [Group Q]

private theorem normal_of_image_normal (f : G →* Q) (hk : IsPGroup 2 f.ker)
    (Y A : Subgroup G) [Y.Normal] (hAY : A ≤ Y) [(A.subgroupOf Y).Normal]
    (hp : IsPPerfect 2 A) [(A.map f).Normal] : A.Normal := by
  let N := A.subgroupOf Y
  let fY := f.comp Y.subtype
  have hkY : IsPGroup 2 fY.ker := by
    rw [show fY.ker = f.ker.comap Y.subtype from rfl]
    exact hk.comap_subtype
  have hpN : IsPPerfect 2 N := hp.of_surjective
    (subgroupOfEquivOfLe hAY).symm.toMonoidHom (subgroupOfEquivOfLe hAY).symm.surjective
  have him : N.map fY = A.map f := by
    rw [show fY = f.comp Y.subtype from rfl, ← map_map, map_subgroupOf_eq_of_le hAY]
  constructor
  intro a ha g
  let e : MulAut Y := Y.normalizerMonoidHom ⟨g, le_normalizer_of_normal (mem_top g)⟩
  let : (N.map e.toMonoidHom).Normal := (inferInstance : N.Normal).map _ e.surjective
  have heq : (N.map e.toMonoidHom).map fY = N.map fY := by
    have he : fY.comp e.toMonoidHom = (MulAut.conj (f g)).toMonoidHom.comp fY := by
      ext y
      simp [fY, e, MulAut.conj_apply]
    rw [map_map, he, ← map_map, him]
    exact mem_normalizer_iff_map_conj_eq.mp
      (le_normalizer_of_normal (mem_top (f g)))
  have hN := eq_of_normal_twoPerfect_of_map_eq fY hkY (N.map e.toMonoidHom) N
    (hpN.of_surjective (e.toMonoidHom.subgroupMap N) (e.toMonoidHom.subgroupMap_surjective N)) hpN heq
  have hm := mem_map_of_mem e.toMonoidHom (show (⟨a,hAY ha⟩ : Y) ∈ N from ha)
  rw [hN] at hm
  exact hm

private theorem card_three_of_threePart (A : Subgroup SymmetricThreeProduct.G)
    (hA : A ≤ SymmetricThreeProduct.threeCore.prod SymmetricThreeProduct.threeCore)
    (hc : 3 ^ (Nat.card A).factorization 3 = 3) : Nat.card A = 3 := by
  have hd : Nat.card A ∣ 3 ^ 2 := by
    have hh := (A.subgroupOf (SymmetricThreeProduct.threeCore.prod
      SymmetricThreeProduct.threeCore)).card_subgroup_dvd_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv] at hh
    convert hh using 1
    rw [Nat.card_eq_fintype_card]; decide
  obtain ⟨k, _, hk⟩ := Nat.dvd_prime_pow Nat.prime_three |>.mp hd
  have hk1 : k = 1 := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 3)
    simpa only [hk, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.Prime.factorization_self Nat.prime_three, Finsupp.single_eq_same, mul_one, pow_one] using hc
  rw [hk, hk1, pow_one]

open CFSG.Quasithin.Chapter15.Section03.RankTwo
/-- Invariance of the actual residuals follows from the component Sylow action.
Normality is needed only inside Y; it is not assumed in YS. -/
theorem rankTwoShadow_normalizes_of_moved_fixed [Finite G]
    {Y S A B T : Subgroup G}
    (hY : IsPPerfect 2 Y) (h9 : Nat.card (Y ⧸ pCore 2 Y) = 9)
    (hS : IsPGroup 2 S) (hSY : S ≤ normalizer (Y : Set G))
    (hshadow : RankTwoShadow Y S)
    (hAY : A ≤ Y) (hBY : B ≤ Y)
    (hAn : (A.subgroupOf Y).Normal) (hBn : (B.subgroupOf Y).Normal)
    (hAp : IsPPerfect 2 A) (hBp : IsPPerfect 2 B)
    (hA3 : 3 ^ (Nat.card A).factorization 3 = 3)
    (hB3 : 3 ^ (Nat.card B).factorization 3 = 3)
    (hTS : T ≤ S) (hm : ⁅A,T⁆ = A) (hf : ⁅B,T⁆ ≤ B.pCoreIn 2) :
    Y ⊔ S ≤ normalizer (A : Set G) ∧ Y ⊔ S ≤ normalizer (B : Set G) := by
  obtain ⟨f, _, hk, hYP⟩ := rankTwoShadow_map_data hY h9 hS hSY hshadow
  let H := Y ⊔ S
  let Yn := Y.subgroupOf H
  let An := A.subgroupOf H
  let Bn := B.subgroupOf H
  let Tn := T.subgroupOf H
  have hAH : A ≤ H := hAY.trans le_sup_left
  have hBH : B ≤ H := hBY.trans le_sup_left
  have hTH : T ≤ H := hTS.trans le_sup_right
  let : Yn.Normal := normal_subgroupOf_of_le_normalizer (sup_le Y.le_normalizer hSY)
  let P := SymmetricThreeProduct.threeCore.prod SymmetricThreeProduct.threeCore
  have hAm : An.map f ≤ P := (map_mono (show An ≤ Yn from comap_mono hAY)).trans hYP.le
  have hBm : Bn.map f ≤ P := (map_mono (show Bn ≤ Yn from comap_mono hBY)).trans hYP.le
  have hcard (N : Subgroup G) (hNH : N ≤ H) (hc : 3 ^ (Nat.card N).factorization 3 = 3)
      (hNP : (N.subgroupOf H).map f ≤ P) : Nat.card ((N.subgroupOf H).map f) = 3 := by
    apply card_three_of_threePart _ hNP
    rw [threePart_map_of_twoGroup_kernel f hk,
      Nat.card_congr (subgroupOfEquivOfLe hNH).toEquiv]
    exact hc
  have hmH : ⁅An,Tn⁆ = An := by
    apply map_injective H.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hAH,
      map_subgroupOf_eq_of_le hTH, hm]
  have hfH : ⁅Bn,Tn⁆ ≤ (B.pCoreIn 2).subgroupOf H := by
    intro x hx
    have hx' := mem_map_of_mem H.subtype hx
    rw [map_commutator, map_subgroupOf_eq_of_le hBH,
      map_subgroupOf_eq_of_le hTH] at hx'
    exact hf hx'
  have hcore : ((B.pCoreIn 2).subgroupOf H).map f = ⊥ := by
    have hp2 := (B.isPGroup_pCoreIn 2).comap_subtype.map f
    have hp3 : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [Nat.card_eq_fintype_card]; decide)
    have hle : ((B.pCoreIn 2).subgroupOf H).map f ≤ P :=
      (map_mono (comap_mono (B.pCoreIn_le 2))).trans hBm
    exact eq_bot_iff.mpr fun x hx => (hp2.disjoint_of_coprime hp3 (by decide)).le_bot ⟨hx,hle hx⟩
  have hfm : ⁅Bn.map f,Tn.map f⁆ = ⊥ := by
    rw [← map_commutator]
    exact le_bot_iff.mp ((map_mono hfH).trans hcore.le)
  have hmm : ⁅An.map f,Tn.map f⁆ = An.map f := by rw [← map_commutator, hmH]
  have haxes := shadow_axes_of_moved_fixed (An.map f) (Bn.map f) (Tn.map f)
    hAm hBm (hcard A hAH hA3 hAm) (hcard B hBH hB3 hBm) hmm hfm
  have hnorm : (An.map f).Normal ∧ (Bn.map f).Normal := by
    rcases haxes with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> rw [ha,hb] <;>
      dsimp only [SymmetricThreeProduct.leftThree, SymmetricThreeProduct.rightThree] <;>
      exact ⟨inferInstance,inferInstance⟩
  have lift (N : Subgroup G) (hNY : N ≤ Y) (hn : (N.subgroupOf Y).Normal)
      (hp : IsPPerfect 2 N) (hnf : ((N.subgroupOf H).map f).Normal) :
      H ≤ normalizer (N : Set G) := by
    have hNH := hNY.trans (show Y ≤ H from le_sup_left)
    let : ((N.subgroupOf H).subgroupOf Yn).Normal := normal_subgroupOf_of_le_normalizer
      ((comap_mono ((normal_subgroupOf_iff_le_normalizer hNY).mp hn)).trans
        (le_normalizer_comap H.subtype))
    let := hnf
    have hp' : IsPPerfect 2 (N.subgroupOf H) := hp.of_surjective
      (subgroupOfEquivOfLe hNH).symm.toMonoidHom (subgroupOfEquivOfLe hNH).symm.surjective
    have hnH := normal_of_image_normal f hk Yn (N.subgroupOf H) (comap_mono hNY) hp'
    exact (normal_subgroupOf_iff_le_normalizer hNH).mp hnH
  exact ⟨lift A hAY hAn hAp hnorm.1, lift B hBY hBn hBp hnorm.2⟩
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.ResidualInvariance

end
