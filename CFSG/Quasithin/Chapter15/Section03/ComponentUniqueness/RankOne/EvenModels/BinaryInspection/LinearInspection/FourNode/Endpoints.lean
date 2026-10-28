module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection.LinearInspection.Contracts
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.ResidualTransport
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.SpecificGroups.PSL3Two.Cardinality


/-!
# The cubic residual excludes the degree-four endpoints

Each endpoint parabolic has a surjective action on a three-dimensional
binary section. The actual GL₃(2) is simple, has order 168, and is generated
by its three-elements. Prime-power residuals commute with finite surjections,
so the endpoint's three-residual has order divisible by seven. The source
actor, transported through the actual component equivalence, has order
2^k * 3. Thus neither endpoint can be the literal local intersection.

This keeps the prime-to-three residual O^{3'} distinct from O³ and O².
It uses only the existing checked GL₃(2) facts and the supplied simplicity
of the degree-four component; no additional model certification is assumed.

Source: Aschbacher--Smith, 15.3.43(a),(e) and its n = 1 paragraph,
printed pp.1139--1140, with A.2.3--4, p.33.
-/

public section

open Subgroup
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection.LinearInspection
private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

private theorem linearThree_card : Nat.card (LinearGroup 3) = 168 := by
  rw [← Nat.card_congr (slEquivLinear 3).toEquiv]
  exact Matrix.PSL3Two.card_SL

private theorem linearThree_threeGenerated : primePowerGenerated 3 (LinearGroup 3) = ⊤ := by
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup (LinearGroup 3) := (projectiveEquivLinear (by decide : 0 < 3)).symm.isSimpleGroup
  rcases (inferInstance : (primePowerGenerated 3 (LinearGroup 3)).Normal).eq_bot_or_eq_top with he | he
  · have hd : 3 ∣ Nat.card (LinearGroup 3) := by rw [linearThree_card]; decide
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hd
    have hm : x ∈ primePowerGenerated 3 (LinearGroup 3) :=
      mem_primePowerGenerated_of_pow (n := 1) (by simpa only [pow_one, hx] using pow_orderOf_eq_one x)
    have hx1 : x = 1 := he.le hm
    simp [hx1] at hx
  · exact he

private theorem threeGenerated_top {H : Type*} [Group H] :
    threeResidualIn (⊤ : Subgroup H) = primePowerGenerated 3 H := by
  rw [threeResidualIn, map_primePowerGenerated_subtype]
  simp only [mem_top, true_and]
  rfl

private theorem threeGenerated_map {A B : Type*} [Group A] [Group B] [Finite A]
    (f : A →* B) (hf : Function.Surjective f) :
    (primePowerGenerated 3 A).map f = primePowerGenerated 3 B := by
  have h := threeResidualIn_map (⊤ : Subgroup A) f
  rwa [threeGenerated_top, map_top_of_surjective f hf, threeGenerated_top] at h

private theorem no_linearThree_quotient {H : Type*} [Group H] [Finite H]
    (k : ℕ) (hk : Nat.card (primePowerGenerated 3 H) = 2 ^ k * 3)
    (f : H →* LinearGroup 3) (hf : Function.Surjective f) : False := by
  have hm : (primePowerGenerated 3 H).map f = ⊤ := by
    rw [threeGenerated_map f hf, linearThree_threeGenerated]
  have hd := (primePowerGenerated 3 H).card_map_dvd f
  rw [hm, card_top, linearThree_card, hk] at hd
  have h7 : 7 ∣ 2 ^ k * 3 := (by decide : 7 ∣ 168).trans hd
  rcases (by decide : Nat.Prime 7).dvd_mul.mp h7 with h | h
  · exact (by decide : ¬ 7 ∣ 2) ((by decide : Nat.Prime 7).dvd_of_dvd_pow h)
  · exact (by decide : ¬ 7 ∣ 3) h

private theorem endpoint_has_linearThree_quotient (b : Basis 3) (i : Fin 3)
    (hi : i = 0 ∨ i = 2) :
    ∃ f : parabolic (cutSpace b i) →* LinearGroup 3, Function.Surjective f := by
  let W := cutSpace b i
  have hs : Function.Surjective (SmallParabolicLevi.subspaceAction W) := by
    intro g
    obtain ⟨x, hx⟩ := SmallParabolicLevi.blockAction_surjective W (g, 1)
    exact ⟨x, congrArg Prod.fst hx⟩
  have hq : Function.Surjective (SmallParabolicLevi.quotientAction W) := by
    intro g
    obtain ⟨x, hx⟩ := SmallParabolicLevi.blockAction_surjective W (1, g)
    exact ⟨x, congrArg Prod.snd hx⟩
  rcases hi with hi | hi
  · have hd : Module.finrank (ZMod 2) (Space 4 ⧸ W) = 3 := by
      have h := W.finrank_quotient_add_finrank
      have hw : Module.finrank (ZMod 2) W = 1 := by
        dsimp only [W]; rw [cutSpace_finrank, hi]; rfl
      rw [hw, Module.finrank_fin_fun] at h
      change Module.finrank (ZMod 2) (Space 4 ⧸ W) + 1 = 4 at h
      omega
    let e : (Space 4 ⧸ W) ≃ₗ[ZMod 2] Space 3 :=
      LinearEquiv.ofFinrankEq _ _ (by rw [hd, Module.finrank_fin_fun])
    exact ⟨(SmallParabolicLevi.linearGroupCongr e).toMonoidHom.comp
      (SmallParabolicLevi.quotientAction W),
        (SmallParabolicLevi.linearGroupCongr e).surjective.comp hq⟩
  · have hd : Module.finrank (ZMod 2) W = 3 := by
      dsimp only [W]; rw [cutSpace_finrank, hi]; rfl
    let e : W ≃ₗ[ZMod 2] Space 3 :=
      LinearEquiv.ofFinrankEq _ _ (by rw [hd, Module.finrank_fin_fun])
    exact ⟨(SmallParabolicLevi.linearGroupCongr e).toMonoidHom.comp
      (SmallParabolicLevi.subspaceAction W),
        (SmallParabolicLevi.linearGroupCongr e).surjective.comp hs⟩

variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}
variable (c : ReducedConfiguration Yplus S M I L V₁ V₂)

/-- The literal component residual excludes either degree-four endpoint parabolic. -/
theorem four_endpoint_excluded (hs : IsSimpleGroup L)
    (e : c.toComponentAction.image L ≃* LinearGroup 4) (b : Basis 3)
    (i : Fin 3) (hi : i = 0 ∨ i = 2) :
    ((c.toComponentAction.image (M ⊓ L)).subgroupOf
      (c.toComponentAction.image L)).map e.toMonoidHom ≠ parabolic (cutSpace b i) := by
  let d := c.toComponentAction
  let K := d.image L
  let J := d.image (M ⊓ L)
  let Y := d.image Yplus
  let A := (Y.subgroupOf K).map e.toMonoidHom
  let P := (J.subgroupOf K).map e.toMonoidHom
  have hYK : Y ≤ K := map_mono (comap_mono c.y_le_component)
  have hJK : J ≤ K := map_mono (comap_mono inf_le_right)
  have hr : Y.subgroupOf K = threeResidualIn (J.subgroupOf K) := by
    apply map_injective K.subtype_injective
    rw [map_subgroupOf_eq_of_le hYK, threeResidualIn_map,
      map_subgroupOf_eq_of_le hJK]
    dsimp only [Y, J, d]
    rw [quotient_intersection_eq c, ParabolicInspection.quotient_residual_on_component c]
  have hA : A = threeResidualIn P := by
    dsimp only [A, P]
    rw [hr, threeResidualIn_map]
  let u : Y ≃* A := (subgroupOfEquivOfLe hYK).symm.trans
    (e.subgroupMap (Y.subgroupOf K))
  have hidx : (pCore 2 A).index = 3 := by
    rw [← pCore_map_iso 2 u, index_map_of_bijective u.bijective]
    exact quotient_actor_index c hs
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
  have hc : Nat.card A = 2 ^ k * 3 := by
    rw [← (pCore 2 A).card_mul_index, hk, hidx]
  have hR : Nat.card (primePowerGenerated 3 P) = 2 ^ k * 3 := by
    rw [hA, threeResidualIn, card_map_of_injective P.subtype_injective] at hc
    exact hc
  intro he
  change P = parabolic (cutSpace b i) at he
  obtain ⟨f, hf⟩ := endpoint_has_linearThree_quotient b i hi
  let ep := MulEquiv.subgroupCongr he
  exact no_linearThree_quotient k hR (f.comp ep.toMonoidHom) (hf.comp ep.surjective)

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection.LinearInspection
