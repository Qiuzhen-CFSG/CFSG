module

public import Theory.GroupTheory.SylowThreeNormalizerSection
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# The two factors of a Sylow three-subgroup

Suppose Y/R is elementary abelian of order nine, R is a normal two-subgroup
of Y, and Y = A D, with R contained in both A and D and A ∩ D contained in R.
For every Sylow three-subgroup X of Y, multiplication identifies
(X ∩ A) × (X ∩ D) with X. The equivalence retains its multiplication formula.

The Sylow supplement X R = Y lifts each factor modulo R into X. Coprime
intersection makes the quotient injective on X, so X is abelian and the
lifted factors multiply bijectively onto X. Only normality relative to Y
is used.

Source: Aschbacher--Smith, proof of 15.3.38, combined manuscript
(1 March 2004), printed p.1136, the clause X = X_L × X_D.
-/

public section

open Subgroup
open scoped Pointwise
namespace SylowThreeNormalizer
variable {G : Type*} [Group G] [Finite G]

/-- The actual multiplication equivalence for the two Sylow intersections. -/
theorem exists_product_equiv (Y R A D : Subgroup G) [(R.subgroupOf Y).Normal]
    (hRY : R ≤ Y) (hYR : Y ≤ normalizer (R : Set G))
    (e : (Y ⧸ R.subgroupOf Y) ≃* Multiplicative (Fin 2 → ZMod 3))
    (hAY : A ≤ Y) (hDY : D ≤ Y) (hRA : R ≤ A) (hRD : R ≤ D)
    (hAD : A ⊓ D ≤ R) (hprod : (Y : Set G) = (A : Set G) * (D : Set G))
    (X : Sylow 3 Y) (hR : IsPGroup 2 R) :
    let P := (X : Subgroup Y).map Y.subtype
    ∃ f : ((P ⊓ A : Subgroup G) × (P ⊓ D : Subgroup G)) ≃* P,
      ∀ z, (f z : G) = (z.1 : G) * (z.2 : G) := by
  let P := (X : Subgroup Y).map Y.subtype
  have hPY : P ≤ Y := map_subtype_le _
  have hq : IsPGroup 3 (Y ⧸ R.subgroupOf Y) := by
    apply IsPGroup.of_card (n := 2)
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card]
  have hgen := SylowThreeNormalizer.sylow_supplement Y R hRY hq X
  have hPR : Disjoint P R :=
    (IsPGroup.disjoint_of_ne 2 3 (by decide) R P hR (X.isPGroup'.map Y.subtype)).symm
  let q := QuotientGroup.mk' (R.subgroupOf Y)
  let qP : P →* (Y ⧸ R.subgroupOf Y) := q.comp (inclusion hPY)
  have hi : Function.Injective qP := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply le_bot_iff.mp
    intro p hp
    apply Subtype.ext
    exact disjoint_def.mp hPR p.property
      ((QuotientGroup.eq_one_iff (inclusion hPY p)).mp hp)
  have hc (p u : P) : Commute p u := by
    apply hi
    apply e.injective
    simp only [map_mul]
    exact mul_comm _ _
  have hlift (B : Subgroup G) (hBY : B ≤ Y) (hRB : R ≤ B)
      (b : B) : ∃ p : (P ⊓ B : Subgroup G), q (inclusion hPY ⟨p, p.property.1⟩) =
        q (inclusion hBY b) := by
    have hb : (b : G) ∈ P ⊔ R := hgen.symm ▸ hBY b.property
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right P R (hPY.trans hYR)] at hb
    obtain ⟨p, hp, r, hr, hpr⟩ := hb
    have hpB : p ∈ B := by
      have := B.mul_mem b.property (B.inv_mem (hRB hr))
      rwa [← hpr, mul_inv_cancel_right] at this
    refine ⟨⟨p, hp, hpB⟩, ?_⟩
    let pY : Y := ⟨p, hPY hp⟩
    let rY : Y := ⟨r, hRY hr⟩
    have hrq : q rY = 1 := (QuotientGroup.eq_one_iff rY).mpr hr
    have hprY : pY * rY = inclusion hBY b := Subtype.ext hpr
    change q pY = _
    rw [← hprY, map_mul, hrq, mul_one]
  let fA : (P ⊓ A : Subgroup G) →* P := inclusion inf_le_left
  let fD : (P ⊓ D : Subgroup G) →* P := inclusion inf_le_left
  let f := fA.noncommCoprod fD (fun a d => hc (fA a) (fD d))
  have hinj : Function.Injective f := by
    apply (MonoidHom.noncommCoprod_injective fA fD _).mpr
    refine ⟨inclusion_injective _, inclusion_injective _, ?_⟩
    apply disjoint_def.mpr
    rintro p ⟨a, rfl⟩ ⟨d, hd⟩
    apply Subtype.ext
    apply disjoint_def.mp hPR a.property.1
    apply hAD
    exact ⟨a.property.2, (congrArg (fun p : P => (p : G)) hd) ▸ d.property.2⟩
  have hsurj : Function.Surjective f := by
    intro x
    have hx : (x : G) ∈ (A : Set G) * (D : Set G) := hprod ▸ hPY x.property
    obtain ⟨a, ha, d, hd, had⟩ := hx
    obtain ⟨pa, hpa⟩ := hlift A hAY hRA ⟨a, ha⟩
    obtain ⟨pd, hpd⟩ := hlift D hDY hRD ⟨d, hd⟩
    refine ⟨(pa, pd), hi ?_⟩
    change q (inclusion hPY (fA pa * fD pd)) = q (inclusion hPY x)
    rw [map_mul, map_mul]
    change q (inclusion hPY ⟨pa, pa.property.1⟩) *
      q (inclusion hPY ⟨pd, pd.property.1⟩) = _
    rw [hpa, hpd, ← map_mul]
    congr 1
    exact Subtype.ext had
  exact ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩, fun _ => rfl⟩
end SylowThreeNormalizer
