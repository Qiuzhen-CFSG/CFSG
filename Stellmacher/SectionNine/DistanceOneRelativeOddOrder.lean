module
public import Stellmacher.SectionNine.DistanceOneRelativeDoubleSL2
/-!
# Orders of the actual relative odd commutator and elementary image

For the original distance-one extraction and any faithful quotient witness
on the initial center, put X=image(V) and F=[O₂′(bar G),X]. Then F has
order nine and X has order four. Neither the order of the whole initial
center nor its final faithful classification is an input.

The actual relative double-SL₂ theorem gives |F X|=36. Since X is a
two-group of order at least four, its order divides36 and hence equals4.
The odd subgroup F and X intersect trivially, and X normalizes F. Their
normalized product cardinality formula therefore gives |F|=9. Every
subgroup and action instance is taken from the supplied witness.

Source: Stellmacher (9.1)(7), Journal of Algebra190 (1997), printed p.47,
refs/files/stellmacher-n-group.pdf. This supplies the order-nine subgroup
used to recognize the odd core of the whole faithful initial quotient.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem distance_one_relative_odd_order
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (data : DistanceOneActionData ctx)
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓ Subgroup.centralizer
        (ZAt ctx.Γ ctx.criticalPath.a : Set G)) (ZAt ctx.Γ ctx.criticalPath.a)) :
    let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
    let V := (z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next) ⊔
      (z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a)
    let _ := w.groupX
    let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
    let X := (V.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection
    let F := ⁅SectionOne.oddCore w.X,X⁆
    Nat.card F = 9 ∧ Nat.card X = 4 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := Γ.act data.x⁻¹ cp.a
  let P := GAt Γ cp.a
  let Za := ZAt Γ cp.a
  let V := (z Γ cp.a ⊓ stabilizer Γ next) ⊔ (z Γ next ⊓ stabilizer Γ cp.a)
  let _ := w.groupX
  let _ := w.finiteX
  let _ := MulDistribMulAction.compHom Za w.action
  let X := (V.subgroupOf P).map w.projection
  let F := ⁅SectionOne.oddCore w.X,X⁆
  change Nat.card F = 9 ∧ Nat.card X = 4
  obtain ⟨e⟩ := (distance_one_relative_double_sl2 ctx hb data w).1
  have hsl : Nat.card SL2Two = 6 :=
    SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨MulEquiv.refl _⟩
  have hE : Nat.card (F ⊔ X : Subgroup w.X) = 36 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, hsl]
  let _ := distance_one_image_elementary ctx data w
  have hXp : IsPGroup 2 X := IsElementaryAbelian.isPGroup 2 X
  have hlarge : 4 ≤ Nat.card X := (distance_one_image_m_two ctx hb data w).1
  have hXdvd : Nat.card X ∣ 36 := by
    rw [← hE]
    exact Subgroup.card_dvd_of_le (le_sup_right : X ≤ F ⊔ X)
  obtain ⟨n,hn⟩ := hXp.exists_card_eq
  have hnsmall : n ≤ 2 := by
    by_contra hnot
    have h8 : 8 ∣ Nat.card X := by
      rw [hn]
      exact pow_dvd_pow 2 (by omega : 3 ≤ n)
    have hbad := h8.trans hXdvd
    norm_num at hbad
  have hXfour : Nat.card X = 4 := by
    interval_cases n
    · simp only [pow_zero] at hn
      omega
    · simp only [pow_one] at hn
      omega
    · simpa only [show (2 : ℕ) ^ 2 = 4 from rfl] using hn
  let _ : (SectionOne.oddCore w.X).Normal := pPrimeCore_normal
  have hFW : F ≤ SectionOne.oddCore w.X := Subgroup.commutator_le_left _ _
  have hFodd : Nat.Coprime 2 (Nat.card F) :=
    (pPrimeCore_coprime_card (p := 2) (G := w.X)).of_dvd_right
      (Subgroup.card_dvd_of_le hFW)
  have hcop : Nat.Coprime (Nat.card F) (Nat.card X) := by
    rw [hn]
    exact hFodd.symm.pow_right n
  have hdis : F ⊓ X = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hprod := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes F X
    (Subgroup.normalizer_commutator_ge_right _ _)
  rw [hdis,Subgroup.card_bot,hE,hXfour] at hprod
  exact ⟨by omega,hXfour⟩
end Stellmacher.SectionNine
