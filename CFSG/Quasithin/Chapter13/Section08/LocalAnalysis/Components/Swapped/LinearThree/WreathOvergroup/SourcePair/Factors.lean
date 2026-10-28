module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.ProductCoordinates
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel

/-!
# The actual two PSL₃(2) factors

Distinct relative C-components have commuting star images. The supplied
PSL₃(2) isomorphism makes the first image centerless, so these images form
an internal direct product. The second model is transported by the actual
moving conjugation; the multiplication coordinates retain both embeddings.
In particular their product has order 168².

Source: Aschbacher–Smith, proof of 13.8.16(1), printed p.952, using
13.8.15 and F.9.18(5). No PSL₂ model identification is used here.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.WreathOvergroup.SourcePair
variable {G : Type*} [Group G] [Finite G]

/-- The actual PSL₃(2) model has trivial center. -/
theorem center_eq_bot_of_model {A : Type*} [Group A]
    (e : A ≃* Matrix.PSL3Two.PSL) : center A = ⊥ := by
  let f := e.trans Matrix.PSL3Two.equiv.symm
  apply eq_bot_iff.mpr
  intro x hx
  have hz : f x ∈ center Matrix.PSL3Two.SL := (centerCongr f ⟨x, hx⟩).property
  rw [Matrix.PSL3Two.center_eq_bot] at hz
  exact f.injective ((mem_bot.mp hz).trans (map_one f).symm)

/-- Centerlessness makes the commuting component images disjoint. -/
theorem star_disjoint (H K J : Subgroup G) (hKH : K ≤ H) (hJH : J ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hJ : (J.subgroupOf H).IsCComponent)
    (hne : K ≠ J) (hqK : IsQuasisimple (Source.starImage H K))
    (hqJ : IsQuasisimple (Source.starImage H J))
    (e : Source.starImage H K ≃* Matrix.PSL3Two.PSL) :
    Disjoint (Source.starImage H K) (Source.starImage H J) := by
  have hc := LinearTwo.starImages_commute H K J hKH hJH hK hJ hne hqK hqJ
  apply disjoint_def.mpr
  intro x hx hy
  have hz : (⟨x, hx⟩ : Source.starImage H K) ∈ center (Source.starImage H K) := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact (commutator_eq_bot_iff_le_centralizer.mp hc y.property x hy).symm
  rw [center_eq_bot_of_model e] at hz
  exact congrArg Subtype.val (mem_bot.mp hz)

/-- Multiplication coordinates for the two genuine star images. -/
theorem exists_factor_coordinates (H K J : Subgroup G)
    (hKH : K ≤ H) (hJH : J ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hJ : (J.subgroupOf H).IsCComponent)
    (hne : K ≠ J) (hqK : IsQuasisimple (Source.starImage H K))
    (hqJ : IsQuasisimple (Source.starImage H J))
    (e : Source.starImage H K ≃* Matrix.PSL3Two.PSL) :
    ∃ f : Source.starImage H K × Source.starImage H J ≃*
        Source.starImage H (K ⊔ J),
      ∀ a b, (f (a, b) : Source.Hstar H) = (a : Source.Hstar H) * b := by
  have hc := LinearTwo.starImages_commute H K J hKH hJH hK hJ hne hqK hqJ
  obtain ⟨f, hf⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting _ _
    (star_disjoint H K J hKH hJH hK hJ hne hqK hqJ e)
    (commutator_eq_bot_iff_le_centralizer.mp hc)
  exact ⟨f.trans (MulEquiv.subgroupCongr
    (LinearTwo.starImage_sup H K J hKH hJH).symm), hf⟩

/-- The second model and its embedding are obtained from the specified mover. -/
theorem exists_moving_coordinates (H K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent)
    (hqK : IsQuasisimple (Source.starImage H K))
    (e : Source.starImage H K ≃* Matrix.PSL3Two.PSL)
    {t : G} (ht : t ∈ H) (hm : t ∉ normalizer (K : Set G)) :
    ∃ f : Source.starImage H K × Source.starImage H K ≃*
        Source.starImage H (K ⊔ K.conjBy t),
      ∀ a b, (f (a, b) : Source.Hstar H) = (a : Source.Hstar H) *
        (QuotientGroup.mk' (pCore 2 H) ⟨t, ht⟩ * b *
          (QuotientGroup.mk' (pCore 2 H) ⟨t, ht⟩)⁻¹) := by
  let c := LinearTwo.starConjugateEquiv H K hKH ht
  let _ := hqK
  have hqJ : IsQuasisimple (Source.starImage H (K.conjBy t)) :=
    IsQuasisimple.of_mulEquiv c
  obtain ⟨hJH, hJ⟩ := conjugate_isCComponent H K hKH hK ht
  have hne : K ≠ K.conjBy t := fun he => hm (mem_normalizer_iff_map_conj_eq.mpr he.symm)
  obtain ⟨f, hf⟩ := exists_factor_coordinates H K (K.conjBy t)
    hKH hJH hK hJ hne hqK hqJ e
  exact ⟨(MulEquiv.prodCongr (MulEquiv.refl _) c).trans f, fun a b => hf a (c b)⟩

/-- The order of the actual component-orbit image, not a family-tag bound. -/
theorem card_moving_star (H K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent)
    (hqK : IsQuasisimple (Source.starImage H K))
    (e : Source.starImage H K ≃* Matrix.PSL3Two.PSL)
    {t : G} (ht : t ∈ H) (hm : t ∉ normalizer (K : Set G)) :
    Nat.card (Source.starImage H (K ⊔ K.conjBy t)) = 168 ^ 2 := by
  obtain ⟨f, _⟩ := exists_moving_coordinates H K hKH hK hqK e ht hm
  rw [← Nat.card_congr f.toEquiv, Nat.card_prod, Nat.card_congr e.toEquiv,
    Matrix.PSL3Two.card_PSL, pow_two]

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.WreathOvergroup.SourcePair
end
