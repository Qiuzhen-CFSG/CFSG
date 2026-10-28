module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.ResidualProduct.CoreAction
public import Theory.GroupTheory.PResidual.NormalizedGenerators

/-!
# Generation from the genuine plane-action quotient

The two opposite A₄ actors have nontrivial, disjoint order-three images in the
order-nine action quotient. Their images therefore generate it. The kernel of
this action is trivial modulo the two-core in the elementary-nine case, and
is the center (hence Frattini subgroup) in the extraspecial case. Lifting across
that Frattini subgroup gives a two-core supplement. Two-perfectness then
removes the normalizing two-group from the generating set.

The action map below is anchored by its exact centralizer kernel. The resulting
generation assertion is proved, not postulated. Source: Aschbacher--Smith,
15.3.7 and the last paragraph of 15.3.40, printed pp.1122 and 1138.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.ResidualProduct
variable {G D : Type*} [Group G] [Group D]

private theorem centralizer_join (U W : Subgroup G) :
    centralizer (U ⊔ W : Subgroup G) = centralizer (U : Set G) ⊓ centralizer (W : Set G) := by
  apply le_antisymm
  · exact le_inf (centralizer_le (show U ≤ U ⊔ W from le_sup_left))
      (centralizer_le (show W ≤ U ⊔ W from le_sup_right))
  · exact le_centralizer_iff.mpr (sup_le
      (le_centralizer_iff.mp inf_le_left) (le_centralizer_iff.mp inf_le_right))

theorem opposite_images_disjoint {Y A B U W : Subgroup G} (f : Y →* D)
    (hk : f.ker = (centralizer (U ⊔ W : Subgroup G)).subgroupOf Y)
    (hAU : A ≤ centralizer (U : Set G)) (hBW : B ≤ centralizer (W : Set G)) :
    Disjoint ((A.subgroupOf Y).map f) ((B.subgroupOf Y).map f) := by
  apply Subgroup.disjoint_def.mpr
  rintro z ⟨a, ha, rfl⟩ ⟨b, hb, he⟩
  have hab : b⁻¹ * a ∈ f.ker := (MonoidHom.eq_iff f).mp he.symm
  rw [hk] at hab
  have habW : ((b : G)⁻¹ * a) ∈ centralizer (W : Set G) :=
    (centralizer_le (show W ≤ U ⊔ W from le_sup_right)) hab
  have haW : (a : G) ∈ centralizer (W : Set G) := by
    simpa using (centralizer (W : Set G)).mul_mem (hBW hb) habW
  apply MonoidHom.mem_ker.mp
  rw [hk]
  change (a : G) ∈ centralizer (U ⊔ W : Subgroup G)
  rw [centralizer_join]
  exact ⟨hAU ha, haW⟩

theorem plane_image_ne_bot {Y A U W : Subgroup G} (f : Y →* D)
    (hk : f.ker = (centralizer (U ⊔ W : Subgroup G)).subgroupOf Y)
    (hAY : A ≤ Y) (hW : W ≠ ⊥) (hcomm : ⁅W, A⁆ = W) :
    (A.subgroupOf Y).map f ≠ ⊥ := by
  intro he
  have hAC : A ≤ centralizer (W : Set G) := by
    have h := (map_eq_bot_iff (A.subgroupOf Y)).mp he
    rw [hk] at h
    intro a ha
    exact (centralizer_le (show W ≤ U ⊔ W from le_sup_right))
      (h (show (⟨a, hAY ha⟩ : Y) ∈ A.subgroupOf Y from ha))
  exact hW (hcomm.symm.trans
    (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hAC)))

private theorem image_card_three [Finite G] [Finite D]
    {Y A : Subgroup G} (f : Y →* D) (hAY : A ≤ Y)
    (hA : Nat.card A = 12) (hD : Nat.card D = 9)
    (hne : (A.subgroupOf Y).map f ≠ ⊥) :
    Nat.card ((A.subgroupOf Y).map f) = 3 := by
  have hdA := (A.subgroupOf Y).card_map_dvd f
  rw [Nat.card_congr (subgroupOfEquivOfLe hAY).toEquiv, hA] at hdA
  have hdD := ((A.subgroupOf Y).map f).card_subgroup_dvd_card
  rw [hD] at hdD
  have hd : Nat.card ((A.subgroupOf Y).map f) ∣ 3 := Nat.dvd_gcd hdA hdD
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
  · exact (hne (card_eq_one.mp h)).elim
  · exact h

theorem action_image_generated [Finite G] [Finite D]
    {Y A B U W : Subgroup G} (f : Y →* D)
    (hk : f.ker = (centralizer (U ⊔ W : Subgroup G)).subgroupOf Y)
    (hAY : A ≤ Y) (hBY : B ≤ Y)
    (hAU : A ≤ centralizer (U : Set G)) (hBW : B ≤ centralizer (W : Set G))
    (hc : A ≤ centralizer (B : Set G))
    (hA : Nat.card A = 12) (hB : Nat.card B = 12) (hD : Nat.card D = 9)
    (hAW : ⁅W, A⁆ = W) (hBU : ⁅U, B⁆ = U) (hU : U ≠ ⊥) (hW : W ≠ ⊥) :
    ((A ⊔ B).subgroupOf Y).map f = ⊤ := by
  have ha := plane_image_ne_bot f hk hAY hW hAW
  have hk' : f.ker = (centralizer (W ⊔ U : Subgroup G)).subgroupOf Y := by
    simpa only [sup_comm] using hk
  have hb := plane_image_ne_bot f hk' hBY hU hBU
  have ha3 := image_card_three f hAY hA hD ha
  have hb3 := image_card_three f hBY hB hD hb
  have hcab : A.subgroupOf Y ≤ centralizer (B.subgroupOf Y : Set Y) := by
    intro a ha b hb
    exact Subtype.ext (hc ha b hb)
  have hcmap : (A.subgroupOf Y).map f ≤ centralizer ((B.subgroupOf Y).map f : Set D) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator, commutator_eq_bot_iff_le_centralizer.mpr hcab, Subgroup.map_bot]
  obtain ⟨e, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting _ _
    (opposite_images_disjoint f hk hAU hBW) hcmap
  have hcard : Nat.card ((A.subgroupOf Y).map f ⊔ (B.subgroupOf Y).map f : Subgroup D) = 9 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, ha3, hb3]
  rw [subgroupOf_sup hAY hBY, Subgroup.map_sup]
  exact eq_of_le_of_card_ge le_top (by simpa [hD] using hcard.ge)

/-- Lifting across the Frattini kernel is a generation proof, not a generation premise. -/
theorem supplement_core_of_action_image [Finite G]
    {Y H : Subgroup G} (f : Y →* D)
    (hf : (H.subgroupOf Y).map f = ⊤)
    (hk : f.ker.map (QuotientGroup.mk' (pCore 2 Y)) ≤ frattini (Y ⧸ pCore 2 Y)) :
    H.subgroupOf Y ⊔ pCore 2 Y = ⊤ := by
  let q := QuotientGroup.mk' (pCore 2 Y)
  have hsup : H.subgroupOf Y ⊔ f.ker = ⊤ := by
    simpa only [comap_map_eq, comap_top] using congrArg (Subgroup.comap f) hf
  have himage : (H.subgroupOf Y).map q ⊔ frattini (Y ⧸ pCore 2 Y) = ⊤ := by
    apply top_unique
    have hh := congrArg (Subgroup.map q) hsup
    rw [Subgroup.map_sup, map_top_of_surjective q (QuotientGroup.mk'_surjective _)] at hh
    rw [← hh]
    exact sup_le_sup_left hk _
  have hh := congrArg (Subgroup.comap q) (frattini_nongenerating himage)
  simpa only [comap_map_eq, comap_top, q, QuotientGroup.ker_mk'] using hh

theorem residual_generated {Y A B Q : Subgroup G}
    (hY : IsPPerfect 2 Y) (hA : IsPPerfect 2 A) (hB : IsPPerfect 2 B)
    (hQ : IsPGroup 2 Q) (hAY : A ≤ Y) (hBY : B ≤ Y)
    (hQA : Q ≤ normalizer (A : Set G)) (hQB : Q ≤ normalizer (B : Set G))
    (hgen : Y ≤ (A ⊔ B) ⊔ Q) : Y = A ⊔ B := by
  let K := (A ⊔ B) ⊔ Q
  have hAK : A ≤ K := le_sup_left.trans le_sup_left
  have hBK : B ≤ K := le_sup_right.trans le_sup_left
  have hQK : Q ≤ K := le_sup_right
  have hpA : IsPPerfect 2 (A.subgroupOf K) :=
    hA.of_surjective (subgroupOfEquivOfLe hAK).symm.toMonoidHom
      (subgroupOfEquivOfLe hAK).symm.surjective
  have hpB : IsPPerfect 2 (B.subgroupOf K) :=
    hB.of_surjective (subgroupOfEquivOfLe hBK).symm.toMonoidHom
      (subgroupOfEquivOfLe hBK).symm.surjective
  have hnA : Q.subgroupOf K ≤ normalizer (A.subgroupOf K : Set K) := by
    intro q hq
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp (hQA hq) a
  have hnB : Q.subgroupOf K ≤ normalizer (B.subgroupOf K : Set K) := by
    intro q hq
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp (hQB hq) a
  have he := pResidual_eq_sup_of_normalized_generators
    (A.subgroupOf K) (B.subgroupOf K) (Q.subgroupOf K)
    hpA hpB hQ.comap_subtype hnA hnB (by
      rw [← subgroupOf_sup hAK hBK,
        ← subgroupOf_sup (show A ⊔ B ≤ K from le_sup_left) hQK]
      exact subgroupOf_self K)
  have hpY : IsPPerfect 2 (Y.subgroupOf K) :=
    hY.of_surjective (subgroupOfEquivOfLe hgen).symm.toMonoidHom
      (subgroupOfEquivOfLe hgen).symm.surjective
  have hle := le_pResidual_of_isPPerfect (Y.subgroupOf K) hpY
  rw [he, ← subgroupOf_sup hAK hBK] at hle
  exact le_antisymm (fun y hy => hle (show (⟨y, hgen hy⟩ : K) ∈ Y.subgroupOf K from hy))
    (sup_le hAY hBY)

end CFSG.Quasithin.Chapter15.Section03.RankTwo.ResidualProduct
