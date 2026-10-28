module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions.Residual
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.Frattini
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions.SylowAction.Image
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions.SylowAction.Model

/-!
# The Sylow centralizer fixes the actual component quotient

The normalizer action maps Y onto the inner A₄ residual of its marked
parabolic. An actual Sylow three-subgroup of Y therefore has nontrivial cubic
image. An element of C_S(P) preserves the residual, excluding graph action,
and centralizes that cubic image. Its two-power-order inner action is trivial
by the S₄ centralizer calculation. The resulting kernel is the literal
sectionCentralizer L, with no containment P ≤ L required.

Both point and line parabolics and arbitrary inner conjugate markings are
retained. The earlier normalization, product and parabolic conclusions and
Y_C ≤ C_G(L) are explicit inputs. The latter is supplied by the natural-layer
residual theorem; assembling source 15.3.23 remains with the parent module.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.23, final paragraph on printed p.1129, with C.2.7(3) on p.1128.
-/

public section
open Subgroup Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions.SylowAction
variable {G : Type*} [Group G] [Finite G]

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
theorem sylow_centralizer_standard (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* SL)
    (hSL : d.S ≤ normalizer (L : Set G))
    (hSYL : d.S ≤ normalizer (YL d L : Set G))
    (hY : d.Y = YL d L ⊔ YC d L)
    (hC : YC d L ≤ centralizer (L : Set G))
    (M : Subgroup SL) (hstd : M = pointParabolicSL ∨ M = lineParabolicSL)
    (hM : ((YL d L ⊔ (d.S ⊓ L)).subgroupOf L).map (quotientMap L e) = M)
    (P : Sylow 3 d.Y) :
    d.S ⊓ centralizer (sylowThree d P : Set G) ≤ Chapter4.sectionCentralizer L := by
  have hAL : YL d L ≤ L :=
    (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  have hYN : d.Y ≤ normalizer (L : Set G) := by
    rw [hY]
    exact sup_le (hAL.trans L.le_normalizer) (hC.trans (Subgroup.centralizer_le_normalizer _))
  let f : d.Y →* MulAut SL := (action L e).comp (inclusion hYN)
  have hr : f.range = (d.Y.subgroupOf (normalizer (L : Set G))).map (action L e) := by
    ext α
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨inclusion hYN y, y.property, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n,hn⟩, rfl⟩
  have hf : f.range = (residual M).map MulAut.conj :=
    hr.trans (action_image_Y d L e hY hC hSYL M hM)
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
theorem sylow_centralizer_of_parabolic (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hSL : d.S ≤ normalizer (c.L : Set G))
    (hSYL : d.S ≤ normalizer (YL d c.L : Set G))
    (hY : d.Y = YL d c.L ⊔ YC d c.L)
    (hC : YC d c.L ≤ centralizer (c.L : Set G))
    (M : Subgroup SL) (hstd : M = pointParabolicSL ∨ M = lineParabolicSL)
    (g : SL)
    (hM : ((YL d c.L ⊔ (d.S ⊓ c.L)).subgroupOf c.L).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L))) = M.conjBy g)
    (P : Sylow 3 d.Y) :
    d.S ⊓ centralizer (sylowThree d P : Set G) ≤ Chapter4.sectionCentralizer c.L := by
  let e' : (c.L ⧸ pCore 2 c.L) ≃* SL := e.trans (MulAut.conj g⁻¹)
  apply sylow_centralizer_standard d c.L e' hSL hSYL hY hC M hstd _ P
  have hq : quotientMap c.L e' = (MulAut.conj g⁻¹).toMonoidHom.comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L))) := rfl
  rw [hq, ← Subgroup.map_map, hM]
  exact M.conjBy_inv g

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions.SylowAction
