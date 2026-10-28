module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeBranch.NaturalSelection.Structure.CubicParity
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.SourceActions.MarkedImages

/-!
# The partial-inverter obstruction in the even four-plus-three stabilizer

The two-residual of the original local intersection has a quotient of
order nine. Its point subgroup has quotient of order three and supplements
the fixed centralizer residual. An even permutation in the four-plus-three
stabilizer acts by one scalar on the two cubic coordinates. Transport
through the full two-kernel makes this incompatible with the source actor,
which inverts the point cubic and fixes its supplement.

The group and actor in this lemma remain arbitrary; the source construction
and the actual partition placement are supplied by the sibling modules.
Source: Aschbacher–Smith 14.7.50, printed p.1064.
-/

public noncomputable section
open Subgroup Equiv
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.FourExclusion
open Chapter13.Section08.ComponentSieve.Seven
open FourThreeBranch.NaturalSelection
open Chapter13.Section08.Components.Swapped.LinearTwo.SourceActions
open Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement

private theorem cube_eq_one_and_self_inverse {E : Type*} [Group E]
    (x : E) (hc : x ^ 3 = 1) (hi : x = x⁻¹) : x = 1 := by
  have h2 : x ^ 2 = 1 := (pow_two x).trans (eq_inv_iff_mul_eq_one.mp hi)
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, h2, one_mul] at hc
  exact hc

private theorem quotient_eq_one_of_image_square {B : Type*} [Group B]
    (hc : ∀ x : B ⧸ pCore 2 B, x ^ 3 = 1)
    (f : B →* S7) (hk : IsPGroup 2 f.ker) (x : B)
    (hx : (f x) ^ 2 = 1) : QuotientGroup.mk' (pCore 2 B) x = 1 := by
  have hle : f.ker ≤ pCore 2 B := le_sSup ⟨inferInstance, hk⟩
  have h2 : (QuotientGroup.mk' (pCore 2 B) x) ^ 2 = 1 := by
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    apply hle
    change f (x ^ 2) = 1
    rwa [map_pow]
  have h3 := hc (QuotientGroup.mk' (pCore 2 B) x)
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, h2, one_mul] at h3
  exact h3

/-- The full two-kernel transports the even scalar alternatives to the
intrinsic two-core quotient of the original group. -/
theorem even_scalar_on_cubic_quotient {B : Type*} [Group B]
    (hc : ∀ x : B ⧸ pCore 2 B, x ^ 3 = 1)
    (f : B →* S7) (hk : IsPGroup 2 f.ker) (hf : f.range ≤ fourThreeTheta)
    (τ : B →* B) (t : S7) (ht : t ∈ fourThreeStabilizer) (he : t.sign = 1)
    (ha : ∀ x, f (τ x) = t * f x * t⁻¹) :
    (∀ x, QuotientGroup.mk' (pCore 2 B) (τ x) = QuotientGroup.mk' (pCore 2 B) x) ∨
    (∀ x, QuotientGroup.mk' (pCore 2 B) (τ x) = (QuotientGroup.mk' (pCore 2 B) x)⁻¹) := by
  rcases CubicParity.even_scalar_square t ht he with hs | hs
  · left
    intro x
    have hx := hs (f x) (hf ⟨x, rfl⟩)
    have hz := quotient_eq_one_of_image_square hc f hk (τ x * x⁻¹) (by
      simpa only [map_mul, map_inv, ha] using hx)
    exact mul_inv_eq_one.mp (by simpa only [map_mul, map_inv] using hz)
  · right
    intro x
    have hx := hs (f x) (hf ⟨x, rfl⟩)
    have hz := quotient_eq_one_of_image_square hc f hk (τ x * x) (by
      simpa only [map_mul, ha] using hx)
    exact eq_inv_iff_mul_eq_one.mpr (by simpa only [map_mul] using hz)

/-- An even four-plus-three actor cannot invert the point cubic while fixing
its centralizer-residual supplement in the actual order-nine quotient. -/
theorem no_even_partial_inverter {G : Type*} [Group G] [Finite G]
    (B A D : Subgroup G) (hgen : A ⊔ D = B)
    (hcard : Nat.card (B ⧸ pCore 2 B) = 9)
    (hcube : ∀ x : B ⧸ pCore 2 B, x ^ 3 = 1)
    (hAcard : Nat.card (A ⧸ pCore 2 A) = 3)
    (g : normalizer (B : Set G))
    (hgA : g.val ∈ normalizer (A : Set G))
    (hgD : g.val ∈ normalizer (D : Set G))
    (hinv : ∀ x, coreAction A ⟨g.val,hgA⟩ x = x⁻¹)
    (hfix : coreAction D ⟨g.val,hgD⟩ = 1)
    (f : B →* S7) (hk : IsPGroup 2 f.ker) (hf : f.range ≤ fourThreeTheta)
    (t : S7) (ht : t ∈ fourThreeStabilizer) (he : t.sign = 1)
    (ha : ∀ x, f (B.normalizerMonoidHom g x) = t * f x * t⁻¹) : False := by
  let E := B ⧸ pCore 2 B
  let q : B →* E := QuotientGroup.mk' (pCore 2 B)
  let α := coreAction B g
  have hAB : A ≤ B := hgen ▸ le_sup_left
  have hDB : D ≤ B := hgen ▸ le_sup_right
  have hq : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have ho : Odd (Nat.card E) := by rw [hcard]; decide
  have heq (x : B) : α (q x) = q (B.normalizerMonoidHom g x) := coreAction_mk B g x
  let P := Markings.image B A q
  let Y := Markings.image B D q
  have hPcard : Nat.card P = 3 := (Markings.image_card B A hAB q hq ho).trans hAcard
  have hPinv := Markings.image_inverted B A hAB q hq ho g hgA α heq hinv
  have hYfix := Markings.image_fixed B D hDB q hq ho g hgD α heq hfix
  have hPY : P ⊔ Y = ⊤ := by
    have hs : A.subgroupOf B ⊔ D.subgroupOf B = ⊤ := by
      apply map_injective B.subtype_injective
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hAB,map_subgroupOf_eq_of_le hDB,
        ←MonoidHom.range_eq_map,range_subtype,hgen]
    change (A.subgroupOf B).map q ⊔ (D.subgroupOf B).map q = ⊤
    rw [←Subgroup.map_sup,hs,←MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr
      (QuotientGroup.mk'_surjective _)]
  rcases even_scalar_on_cubic_quotient hcube f hk hf
      (B.normalizerMonoidHom g).toMonoidHom t ht he ha with hs | hs
  · have hall (x : E) : α x = x := by
      obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) x
      exact (heq x).trans (hs x)
    have hP : P = ⊥ := by
      apply eq_bot_iff.mpr
      intro x hx
      exact cube_eq_one_and_self_inverse x (hcube x) ((hall x).symm.trans (hPinv x hx))
    rw [hP,card_bot] at hPcard
    omega
  · have hall (x : E) : α x = x⁻¹ := by
      obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) x
      exact (heq x).trans (hs x)
    have hY : Y = ⊥ := by
      apply eq_bot_iff.mpr
      intro x hx
      exact cube_eq_one_and_self_inverse x (hcube x) ((hYfix x hx).symm.trans (hall x))
    rw [hY,sup_bot_eq] at hPY
    rw [hPY,card_top,hcard] at hPcard
    omega

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.FourExclusion
