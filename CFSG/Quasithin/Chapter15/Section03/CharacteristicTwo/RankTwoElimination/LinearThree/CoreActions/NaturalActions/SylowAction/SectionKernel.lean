module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions.SylowAction
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.InnerSplitting.SectionAction

/-!
# Cubic centralizers without a whole-core action hypothesis

The genuine residual Y_C lies in the kernel of the action on L/O₂(L),
independently of its action on [O₂(L),L]. Consequently Y has the full inner
A₄ image of the marked component parabolic. A two-element in C_S(P)
preserves this residual and centralizes a nontrivial cubic image, so the
marked S₄ calculation makes it trivial on the component quotient.

This separates the cubic-centralizer conclusion from the natural-core
classification used elsewhere. The original source consumer supplies the
parabolic and residual geometry; no pointwise fixation of the core is used.

Source: Aschbacher–Smith, proof of 15.3.23, final paragraph, printed p.1129.
-/

public section
open Subgroup Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions.SylowAction
variable {G : Type*} [Group G]

/-- The literal section centralizer is killed by the marked quotient action. -/
theorem action_sectionCentralizer (L : Subgroup G) (e : (L ⧸ pCore 2 L) ≃* SL)
    (n : normalizer (L : Set G)) (hn : (n : G) ∈ Chapter4.sectionCentralizer L) :
    action L e n = 1 := by
  change MulAut.congr e (ComponentIntersection.InnerSplitting.sectionAction L n) = 1
  rw [(ComponentIntersection.InnerSplitting.sectionAction_eq_one_iff L n).mpr hn,
    map_one]

variable [Finite G]

/-- The actual residual product has full inner A₄ image even when Y_C acts
nontrivially on the two-core. -/
theorem action_image_Y_section (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* SL)
    (hY : d.Y = YL d L ⊔ YC d L)
    (hSYL : d.S ≤ normalizer (YL d L : Set G)) (M : Subgroup SL)
    (hM : ((YL d L ⊔ (d.S ⊓ L)).subgroupOf L).map (quotientMap L e) = M) :
    (d.Y.subgroupOf (normalizer (L : Set G))).map (action L e) =
      (residual M).map MulAut.conj := by
  have hAL : YL d L ≤ L :=
    (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  have hAN := hAL.trans L.le_normalizer
  have hCN := (YC_section_action d L).1
  have hzero : ((YC d L).subgroupOf (normalizer (L : Set G))).map (action L e) = ⊥ := by
    apply le_bot_iff.mp
    rintro _ ⟨n,hn,rfl⟩
    exact action_sectionCentralizer L e n
      (((ComponentIntersection.centralizerResidual_le _ _).trans inf_le_right) hn)
  rw [hY, subgroupOf_sup hAN hCN, Subgroup.map_sup, hzero, sup_bot_eq,
    action_image_of_le L (YL d L) e hAL, YL_image d L e hSYL M hM]

private theorem sylow_cubic_image {H K : Type*} [Group H] [Finite H] [Group K]
    (f : H →* K) (hcard : Nat.card f.range = 12) (P : Sylow 3 H) :
    ∃ b ∈ (P : Subgroup H).map f, b ^ 3 = 1 ∧ b ≠ 1 := by
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let Q := P.mapSurjective f.rangeRestrict_surjective
  have hdiv : 3 ∣ Nat.card Q := Q.dvd_card_of_dvd_card (by rw [hcard]; decide)
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := Q) 3 hdiv
  have hpow : b ^ 3 = 1 := by simpa only [hb] using pow_orderOf_eq_one b
  have hb1 : b ≠ 1 := by intro h; simp [h] at hb
  refine ⟨((b : f.range) : K), ?_, congrArg (fun z : Q => ((z : f.range) : K)) hpow, ?_⟩
  · have hm : (b : f.range) ∈ (P : Subgroup H).map f.rangeRestrict := b.property
    obtain ⟨p, hp, he⟩ := hm
    exact ⟨p, hp, congrArg Subtype.val he⟩
  · intro h
    exact hb1 (Subtype.ext (Subtype.ext h))

/-- The centralizer of every actual Sylow three-subgroup of Y fixes the
component quotient under either standard parabolic marking. -/
theorem sylow_centralizer_standard_section (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* SL)
    (hSL : d.S ≤ normalizer (L : Set G))
    (hSYL : d.S ≤ normalizer (YL d L : Set G))
    (hY : d.Y = YL d L ⊔ YC d L)
    (M : Subgroup SL) (hstd : M = pointParabolicSL ∨ M = lineParabolicSL)
    (hM : ((YL d L ⊔ (d.S ⊓ L)).subgroupOf L).map (quotientMap L e) = M)
    (P : Sylow 3 d.Y) :
    d.S ⊓ centralizer (sylowThree d P : Set G) ≤ Chapter4.sectionCentralizer L := by
  have hAL : YL d L ≤ L :=
    (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  have hYN : d.Y ≤ normalizer (L : Set G) := by
    rw [hY]
    exact sup_le (hAL.trans L.le_normalizer) (YC_section_action d L).1
  let f : d.Y →* MulAut SL := (action L e).comp (inclusion hYN)
  have hr : f.range = (d.Y.subgroupOf (normalizer (L : Set G))).map (action L e) := by
    ext α
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨inclusion hYN y, y.property, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n,hn⟩, rfl⟩
  have hf : f.range = (residual M).map MulAut.conj :=
    hr.trans (action_image_Y_section d L e hY hSYL M hM)
  have hcard : Nat.card f.range = 12 := by
    rw [hf, ← Nat.card_congr ((residual M).equivMapOfInjective MulAut.conj conj_injective).toEquiv]
    rcases hstd with rfl | rfl
    · exact card_point_residual
    · exact card_line_residual
  obtain ⟨β, hβP, hβ3, hβ1⟩ := sylow_cubic_image f hcard P
  have hβ : β ∈ (residual M).map MulAut.conj :=
    hf ▸ (map_le_range _ _ hβP)
  apply le_sectionCentralizer_of_action L _ e (inf_le_left.trans hSL)
  intro x
  let n : normalizer (L : Set G) := ⟨x, hSL x.property.1⟩
  have hpres := action_preserves_image L (YL d L) e n (hSYL x.property.1)
  rw [YL_image d L e hSYL M hM] at hpres
  have htwo : ∃ k : ℕ, action L e n ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := d.T.isPGroup' ⟨x, (show d.S ≤ (d.T : Subgroup G) from inf_le_left) x.property.1⟩
    have hn : n ^ (2 ^ k) = 1 :=
      Subtype.ext (congrArg (fun t : d.T => (t : G)) hk)
    exact ⟨k, by rw [← map_pow, hn, map_one]⟩
  apply two_preserver_cubic M hstd (action L e n) β hpres htwo hβ hβ3 hβ1
  obtain ⟨p, hp, rfl⟩ := hβP
  have hc : n * inclusion hYN p = inclusion hYN p * n := by
    apply Subtype.ext
    exact (x.property.2 p (mem_map_of_mem d.Y.subtype hp)).symm
  change action L e n * action L e (inclusion hYN p) =
    action L e (inclusion hYN p) * action L e n
  rw [← map_mul, ← map_mul, hc]

/-- The actual Sylow centralizer acts trivially on L/O₂(L), with either
conjugate parabolic marking. All inputs preceding the final paragraph of
15.3.23 are explicit; the Sylow group belongs to Y, not necessarily to L. -/
theorem sylow_centralizer_of_parabolic_section (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hSL : d.S ≤ normalizer (c.L : Set G))
    (hSYL : d.S ≤ normalizer (YL d c.L : Set G))
    (hY : d.Y = YL d c.L ⊔ YC d c.L)
    (M : Subgroup SL) (hstd : M = pointParabolicSL ∨ M = lineParabolicSL)
    (g : SL)
    (hM : ((YL d c.L ⊔ (d.S ⊓ c.L)).subgroupOf c.L).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L))) = M.conjBy g)
    (P : Sylow 3 d.Y) :
    d.S ⊓ centralizer (sylowThree d P : Set G) ≤ Chapter4.sectionCentralizer c.L := by
  let e' : (c.L ⧸ pCore 2 c.L) ≃* SL := e.trans (MulAut.conj g⁻¹)
  apply sylow_centralizer_standard_section d c.L e' hSL hSYL hY M hstd _ P
  have hq : quotientMap c.L e' = (MulAut.conj g⁻¹).toMonoidHom.comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L))) := rfl
  rw [hq, ← Subgroup.map_map, hM]
  exact M.conjBy_inv g


end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions.SylowAction
