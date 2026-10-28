module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Models
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry.Torus

/-!
# Odd-prime ranks of the three surviving inner Sylow normalizers

For each actual SL₃(q), Sp₄(q), or G₂(q) component image, transport its
specified Sylow subgroup to the concrete carrier. The Sylow normalizer
modulo its two-core is the full split torus Fˣ × Fˣ, including the cubic
scalar center in the SL₃ row. Each prime dividing q−1 consequently has
rank exactly two. The literal inclusion in KzT/C(VK) transfers this rank
to the radical-image normalizer whenever it contains this inner normalizer.

The containment is still local root geometry owned by
qt-d-1222-shadow-component-comparison; it is not assumed proved here.
The model premise is supplied by the completed B.4/B.5 image sieve.
Source: Aschbacher--Smith, 11.4.2, printed p.777. Imported concrete G₂
calculations retain LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall

private def normalizerEquiv {A B : Type*} [Group A] [Group B] [Finite A]
    (e : A ≃* B) (P : Sylow 2 A) :
    normalizer (P : Set A) ≃* normalizer (P.mapSurjective (f := e.toMonoidHom) e.surjective : Set B) :=
  (e.subgroupMap (normalizer (P : Set A))).trans
    (MulEquiv.subgroupCongr (map_equiv_normalizer_eq (P : Subgroup A) e))

private theorem torus_primeRank {F : Type*} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hd : p ∣ Nat.card F - 1) :
    primeRank p (Fˣ × Fˣ) = 2 := by
  have hu : primeRank p Fˣ = 1 := by
    apply le_antisymm
    · exact (Sylow.nonempty.some : Sylow p Fˣ).primeRank_le_one_of_isCyclic inferInstance
    · apply Theory.Quasithin.one_le_primeRank_of_dvd_card
      simpa only [Nat.card_units] using hd
  rw [primeRank_prod_eq_add,hu]

private theorem normalizer_rank_of_torus_quotient
    {A F : Type*} [Group A] [Finite A] [Field F] [Finite F]
    (P : Sylow 2 A)
    (e : (normalizer (P : Set A) ⧸ pCore 2 (normalizer (P : Set A))) ≃* (Fˣ × Fˣ))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hd : p ∣ Nat.card F - 1) :
    primeRank p (normalizer (P : Set A)) = 2 := by
  rw [← primeRank_quotient_eq_of_isTwoGroup p hp (pCore 2 _) pCore_isPGroup,
    primeRank_equiv p e, torus_primeRank hd]

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- Every inner Sylow normalizer of each surviving actual component image
has rank two at every prime dividing the original q minus one. -/
theorem rankTwo_sylow_normalizer_primeRank (hm : RankTwoModel E)
    (P : Sylow 2 ((component E).map (projection E)))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hd : p ∣ 2 ^ E.input.field.degree - 1) :
    primeRank p (normalizer (P : Set ((component E).map (projection E)))) = 2 := by
  rcases hm with hm | hm | hm
  · obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
    let _ : Field F := hF
    let _ : Finite F := hfin
    rw [primeRank_equiv p (normalizerEquiv e P)]
    apply normalizer_rank_of_torus_quotient _
      (Matrix.PSL3.CartanActions.BorelQuotient.sylowSLNormalizerQuotientEquiv
        F E.input.field.degree_pos hcard _) hp
    simpa only [hcard] using hd
  · obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
    let _ : Field F := hF
    let _ : Finite F := hfin
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
    rw [primeRank_equiv p (normalizerEquiv e P)]
    let a := Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.sylowNormalizerEquiv
      hcard E.input.field.degree_pos (P.mapSurjective (f := e.toMonoidHom) e.surjective)
    apply normalizer_rank_of_torus_quotient _
      ((QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans
        (Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.quotientTorusEquiv hcard)) hp
    simpa only [hcard] using hd
  · obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
    let _ : Field F := hF
    let _ : Finite F := hfin
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
    rw [primeRank_equiv p (normalizerEquiv e P)]
    apply normalizer_rank_of_torus_quotient _
      (Atlas.G2.EvenBorelTorus.sylowNormalizerQuotientEquiv _) hp
    simpa only [hcard] using hd

/-- Normalization of the actual radical image by an inner Sylow normalizer
supplies its required rank. The literal embedding into KzT/C(VK) is retained. -/
theorem radical_image_normalizer_rank_of_model (hm : RankTwoModel E)
    (P : Sylow 2 ((component E).map (projection E)))
    (hN : (normalizer (P : Set ((component E).map (projection E)))).map
        ((component E).map (projection E)).subtype ≤
      normalizer ((radical E).map (projection E) : Set (ActionQuotient E)))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hd : p ∣ 2 ^ E.input.field.degree - 1) :
    2 ≤ primeRank p (normalizer
      ((radical E).map (projection E) : Set (ActionQuotient E))) := by
  have hr := primeRank_mono p hN
  rw [← primeRank_equiv p ((normalizer (P : Set ((component E).map (projection E)))).equivMapOfInjective
    ((component E).map (projection E)).subtype Subtype.val_injective),
    rankTwo_sylow_normalizer_primeRank E hm P hp hd] at hr
  exact hr

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall
