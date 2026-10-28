module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.TwoFactors.Placement
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.OneFactor.SimpleMarking
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.QuotientMarks

/-!
# The invariant cubic subgroup in both marked local models

The compatible A₆ point action gives |L₁|₃ = 3. The compatible hexacode
cover action maps L₁ into the point parabolic of order 72, and sends the
literal central residual L₀ onto the cubic center. These supply the order
restriction needed for rank placement, without assuming a residual
factorization, a cubic subgroup, or any factor-placement conclusion.

Placement makes L₁* a three-group. In the simple case its order is three,
since the two-kernel cannot remove its three-part. In the covered case
the image of L₀ is cubic: its intrinsic two-core quotient agrees with that
of L₀*, and the latter's two-core is trivial. This uses no normality of
L₀* in H*. Both subgroups are normalized by the actual image of T.
The previously proved Sylow and normal-generation obstruction gives the
complete conditional two-factor contradiction.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1, printed p.877; proof of 13.8.5, p.947 (PDF p.964).
Only intrinsic marked-model calculations are reused from SourceMarking.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter13.Section08
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
open Components.Swapped.LinearThree.MarkedAutomizer
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable.TwoFactors
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem star_card_dvd (H X : Subgroup G) (hX : X ≤ H) :
    Nat.card (Source.starImage H X) ∣ Nat.card X :=
  card_dvd_of_surjective (starMap H X hX) (starMap_surjective H X hX)

omit [Finite G] in
private theorem star_normalizes (H A B : Subgroup G)
    (hn : A ≤ normalizer (B : Set G)) :
    Source.starImage H A ≤ normalizer (Source.starImage H B : Set (Source.Hstar H)) := by
  apply le_normalizer_iff.mpr
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  refine ⟨a * b * a⁻¹, le_normalizer_iff.mp hn a.val ha b.val hb, ?_⟩
  simp only [map_mul, map_inv]

private theorem threeGroup_core_eq_bot {A : Type*} [Group A] (hA : IsPGroup 3 A) :
    pCore 2 A = ⊥ := by
  exact disjoint_self.mp (IsPGroup.disjoint_of_ne 2 3 (by decide) _ _ pCore_isPGroup
    (hA.to_subgroup (pCore 2 A)))

private theorem star_card_of_threeGroup (H X : Subgroup G) (hX : X ≤ H)
    (h3 : IsPGroup 3 (Source.starImage H X)) :
    Nat.card (Source.starImage H X) = Nat.card (X ⧸ pCore 2 X) := by
  have he := Nat.card_congr (starCoreQuotientEquiv H X hX).toEquiv
  rw [threeGroup_core_eq_bot h3,
    Nat.card_congr (QuotientGroup.quotientBot).toEquiv] at he
  exact he.symm

private theorem card_three_of_threeGroup (X : Subgroup G) (h3 : IsPGroup 3 X)
    (hne : X ≠ ⊥) {n : ℕ} (hd : Nat.card X ∣ 3 * 2 ^ n) : Nat.card X = 3 := by
  obtain ⟨k, hk⟩ := h3.exists_card_eq
  have hc : Nat.Coprime (Nat.card X) (2 ^ n) := by
    rw [hk]
    exact (by decide : Nat.Coprime 3 2).pow k n
  have hd3 : Nat.card X ∣ 3 := hc.dvd_of_dvd_mul_right hd
  rcases (Nat.dvd_prime Nat.prime_three).mp hd3 with h | h
  · exact False.elim (hne (Subgroup.card_eq_one.mp h))
  · exact h

private theorem three_dvd_star_card (H X : Subgroup G) (hX : X ≤ H)
    (hd : 3 ∣ Nat.card X) : 3 ∣ Nat.card (Source.starImage H X) := by
  let f := starMap H X hX
  obtain ⟨n, hn⟩ := (starMap_kernel_isPGroup H X hX).exists_card_eq
  have he := card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f
    (starMap_surjective H X hX)).toEquiv, hn] at he
  rw [he] at hd
  apply ((Nat.Prime.dvd_mul Nat.prime_three).mp hd).resolve_right
  intro hd'
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd')

/-- The nontrivial three-part survives the two-kernel; after placement
the entire simple-case L₁* is the invariant cubic subgroup. -/
theorem simple_star_card_three (H L T V V₁ : Subgroup G)
    (hLV : L ≤ normalizer (V : Set G)) (d : SimplePointModel L V hLV)
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (L : Set G))
    (hV₁V : V₁ ≤ V) (hc : Nat.card V₁ = 2)
    (hLH : one L T V₁ ≤ H)
    (h3 : IsPGroup 3 (Source.starImage H (one L T V₁))) :
    Nat.card (Source.starImage H (one L T V₁)) = 3 := by
  obtain ⟨hval, n, hncard⟩ := OneFactor.simple_marked_order_data L T V V₁ hLV d hT hn hV₁V hc
  have hd : 3 ∣ Nat.card (one L T V₁) := by
    apply Nat.dvd_of_factorization_pos
    change (Nat.card (markedResidual L T V₁)).factorization 3 ≠ 0
    omega
  have hdstar := three_dvd_star_card H (one L T V₁) hLH hd
  apply card_three_of_threeGroup _ h3
  · intro he
    rw [he, card_bot] at hdstar
    norm_num at hdstar
  · exact (star_card_dvd H (one L T V₁) hLH).trans hncard

private theorem binaryPoint_stabilizer_card (x : Theory.SpecificGroups.SymmetricSix.BinaryPoint) :
    Nat.card (MulAction.stabilizer Theory.SpecificGroups.SymmetricSix.A6 x) = 24 := by
  open Theory.SpecificGroups.SymmetricSix in
  have he : MulAction.stabilizer A6 x =
      MulAction.stabilizer A6 (duadPolarEquiv.symm x) := by
    ext g
    change g.val • x = x ↔ g.val • duadPolarEquiv.symm x = duadPolarEquiv.symm x
    rw [← duadPolarEquiv.injective.eq_iff, duadPolarEquiv_equivariant]
    simp
  open Theory.SpecificGroups.SymmetricSix in
  have hg := Classical.choose_spec (a6_duad_transitive 0 (duadPolarEquiv.symm x))
  rw [he, Nat.card_congr (MulAction.stabilizerEquivStabilizer hg.symm).symm.toEquiv,
    Theory.SpecificGroups.SymmetricSix.a6_duad_stabilizer_zero,
    Theory.SpecificGroups.SymmetricSix.a6DuadStabilizer_card]

private theorem cover_parabolic_card (x : Theory.SpecificGroups.SymmetricSix.BinaryPoint) :
    Nat.card (Model.parabolic x) = 72 := by
  let f : Model.parabolic x →* MulAction.stabilizer Theory.SpecificGroups.SymmetricSix.A6 x :=
    Atlas.Codes.hexEvenCoordinate.subgroupComap
      (MulAction.stabilizer Theory.SpecificGroups.SymmetricSix.A6 x)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨g, hg⟩ := Atlas.Codes.hexEvenCoordinate_surjective y.val
    refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
    change Atlas.Codes.hexEvenCoordinate g ∈ MulAction.stabilizer Theory.SpecificGroups.SymmetricSix.A6 x
    rw [hg]
    exact y.property
  have hk : f.ker = (center Model.Cover).subgroupOf (Model.parabolic x) := by
    ext g
    change f g = 1 ↔ g.val ∈ center Model.Cover
    rw [← Representation.Hexacode.even_kernel_eq_center]
    exact Subtype.ext_iff
  have hkcard : Nat.card f.ker = 3 := by
    rw [hk, Nat.card_congr (subgroupOfEquivOfLe (CoverPointModel.center_le_parabolic x)).toEquiv]
    exact Representation.Hexacode.even_center_card
  have he := card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv,
    binaryPoint_stabilizer_card, hkcard] at he
  exact he

/-- Only the point stabilizer of the actual cover is used for the order bound. -/
theorem cover_one_order_data (L T V V₁ : Subgroup G)
    (hLV : L ≤ normalizer (V : Set G)) (d : CoverPointModel L V hLV)
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (L : Set G))
    (hV₁V : V₁ ≤ V) (hc : Nat.card V₁ = 2) :
    ∃ m n : ℕ, Nat.card (one L T V₁) ∣ 2 ^ m * 3 ^ n := by
  obtain ⟨z, hz, _⟩ := (Nat.card_eq_two_iff' (1 : V₁)).mp hc
  let x := d.markedPoint V₁ hV₁V z hz
  let hRL := markedResidual_le_left L T V₁ hT hn
  let hr := d.markedResidual_image T V₁ hT hn hV₁V hc z hz
  let f := d.toModelResidual (markedResidual L T V₁) hRL x hr
  have hf := d.toModelResidual_surjective (markedResidual L T V₁) hRL x hr
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 ((d.subgroupMap (markedResidual L T V₁) hRL).codRestrict _ _).ker
    rw [MonoidHom.ker_codRestrict, d.subgroupMap_ker]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hRL)
  obtain ⟨n, hn⟩ := hk.exists_card_eq
  have he := card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv, hn] at he
  have hd : Nat.card (Model.residual x) ∣ 72 := by
    rw [← cover_parabolic_card x]
    exact card_dvd_of_le (map_subtype_le _)
  refine ⟨n + 3, 2, ?_⟩
  change Nat.card (markedResidual L T V₁) ∣ _
  rw [he]
  convert Nat.mul_dvd_mul_right hd (2 ^ n) using 1
  ring

/-- The source L₀ quotient is cubic, from the actual center of the cover. -/
theorem cover_zero_quotient_card (L V : Subgroup G)
    (hLV : L ≤ normalizer (V : Set G)) (d : CoverPointModel L V hLV) :
    Nat.card (zero L ⧸ pCore 2 (zero L)) = 3 := by
  have hm : (Source.starImage L (zero L)).map d.quotientEquiv.toMonoidHom = center Model.Cover := by
    change (((zero L).subgroupOf L).map (QuotientGroup.mk' (pCore 2 L))).map
      d.quotientEquiv.toMonoidHom = _
    rw [map_map]
    exact d.zero_image
  have hn := localImage_normal L (zero L) (zero_le L) (L_normalizes_zero L)
  rw [Nat.card_congr (normalStarEquiv L (zero L) (zero_le L) hn).toEquiv,
    Nat.card_congr ((Source.starImage L (zero L)).equivMapOfInjective
      d.quotientEquiv.toMonoidHom d.quotientEquiv.injective).toEquiv, hm]
  exact Representation.Hexacode.even_center_card

/-- The central mark gives a T-invariant cubic subgroup inside the literal L₁*. -/
theorem cover_invariant_cubic (H L T V V₁ : Subgroup G)
    (hLV : L ≤ normalizer (V : Set G)) (d : CoverPointModel L V hLV)
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (L : Set G))
    (hV₁V : V₁ ≤ V) (hc : Nat.card V₁ = 2)
    (hLH : one L T V₁ ≤ H)
    (h3 : IsPGroup 3 (Source.starImage H (one L T V₁))) :
    Nat.card (Source.starImage H (zero L)) = 3 ∧
      Source.starImage H (zero L) ≤ Source.starImage H (one L T V₁) ∧
      Source.starImage H T ≤ normalizer (Source.starImage H (zero L) : Set (Source.Hstar H)) := by
  obtain ⟨z, hz, _⟩ := (Nat.card_eq_two_iff' (1 : V₁)).mp hc
  have hzle : zero L ≤ one L T V₁ := d.zero_le_markedResidual T V₁ hT hn hV₁V hc z hz
  have hzstar : Source.starImage H (zero L) ≤ Source.starImage H (one L T V₁) :=
    map_mono (subgroupOf_mono H hzle)
  refine ⟨?_, hzstar, star_normalizes H T (zero L)
    (hn.trans (normalizer_le_zero_normalizer L))⟩
  rw [star_card_of_threeGroup H (zero L) (hzle.trans hLH) (h3.to_le hzstar)]
  exact cover_zero_quotient_card L V hLV d

variable {H L V V₁ V₃ G₁ M : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- Both genuine marked local models exclude two factors. The factor
placement, cubic subgroup and its Sylow invariance are conclusions of the proof. -/
theorem two_factors_impossible_of_marked_models (T : Sylow 2 G)
    (hH : H ∈ Source.Hz (one L (T : Subgroup G) V₁) T G₁ M)
    (hLV : L ≤ normalizer (V : Set G))
    (hmodels : Nonempty (SimplePointModel L V hLV) ∨ Nonempty (CoverPointModel L V hLV))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTV : (T : Subgroup G) ≤ normalizer (V₁ : Set G))
    (hV₁V : V₁ ≤ V) (hV₁ : Nat.card V₁ = 2) (hrank : primeRank 3 H ≤ 2)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (t : Source.Hstar H) (ht : IsTransvection ρ t)
    (d : ChapterB.SolvableFFFactors (ρ.comp (normalClosure ({t} : Set (Source.Hstar H))).subtype))
    (hJ : offenderSubgroup (ρ.comp (normalClosure ({t} : Set (Source.Hstar H))).subtype) = ⊤)
    (hc : d.count = 2) : False := by
  have hLH : one L (T : Subgroup G) V₁ ≤ H := le_sup_left.trans hH.1.2
  rcases hmodels with hs | hs
  · obtain ⟨s⟩ := hs
    obtain ⟨_, n, hn⟩ := OneFactor.simple_marked_order_data L T V V₁ hLV s
      T.isPGroup' hTL hV₁V hV₁
    have hord : ∃ m n : ℕ,
        Nat.card (Source.starImage H (one L (T : Subgroup G) V₁)) ∣ 2 ^ m * 3 ^ n := by
      refine ⟨n, 1, ?_⟩
      simpa only [pow_one, mul_comm] using (star_card_dvd H _ hLH).trans hn
    obtain ⟨hplace, h3⟩ := source_one_le_normalClosure_and_isThreeGroup L T V₁ G₁ M H hH
      ρ t d hJ hc hrank hord
    exact source_no_invariant_cubic T H _ G₁ M V₃ V₁ hH ρ t ht d hJ hc _ hplace
      (simple_star_card_three H L T V V₁ hLV s T.isPGroup' hTL hV₁V hV₁ hLH h3)
      (star_normalizes H T _ (T_normalizes_one L T V₁ hTV))
  · obtain ⟨s⟩ := hs
    obtain ⟨m, n, hn⟩ := cover_one_order_data L T V V₁ hLV s
      T.isPGroup' hTL hV₁V hV₁
    have hord : ∃ m n : ℕ,
        Nat.card (Source.starImage H (one L (T : Subgroup G) V₁)) ∣ 2 ^ m * 3 ^ n :=
      ⟨m, n, (star_card_dvd H _ hLH).trans hn⟩
    obtain ⟨hplace, h3⟩ := source_one_le_normalClosure_and_isThreeGroup L T V₁ G₁ M H hH
      ρ t d hJ hc hrank hord
    obtain ⟨hcard, hle, hnorm⟩ := cover_invariant_cubic H L T V V₁ hLV s
      T.isPGroup' hTL hV₁V hV₁ hLH h3
    exact source_no_invariant_cubic T H _ G₁ M V₃ V₁ hH ρ t ht d hJ hc _
      (hle.trans hplace) hcard hnorm

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable.TwoFactors

end
