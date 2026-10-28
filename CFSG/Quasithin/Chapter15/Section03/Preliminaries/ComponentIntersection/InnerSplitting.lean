module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.Basic
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.QuotientCoordinates
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.InnerSplitting.Comparison
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.InnerSplitting.QuotientProduct
public import Theory.ElementaryAbelian.Extraspecial

/-!
# Inner splitting and quotient orders in 15.3.12(2)

Under Hypothesis 15.3.10, let `I` be an outside overgroup and let `L ≤ I`
be a C-component of three-rank one. The inner action of `Y₊` on
`L/O₂(L)` has the same image as the actual residual `Y_L = O²(Y₊ ∩ L)`.
The proof obtains this comparison from cyclic Sylow three-subgroups and
transfer, rather than assuming equality of the images. Passing to the
residual of the actual section-action kernel gives `Y₊ = Y_L Y_C`.
The factors have two-group intersection. Their disjoint quotient images
rule out the extraspecial order-27 alternative, leaving the elementary
abelian quotient of order nine and `|Y_L|₃ = |Y_C|₃ = 3`.

`inner_splitting_of_preliminary_facts` is the conditional helper requested
for independent work on 15.3.12. Nontriviality and the order-three two-core
quotient of `Y_L` remain explicit inputs from the odd-rank argument.
The theta equality and the E₉/extraspecial quotient alternatives are the
used parts of 15.3.11(6),(5i); the exponent-three quotient property also
remains explicit. Their assembly owners must discharge these inputs in
the full source theorem. All exponent assertions concern two-core
quotients. The corrected conclusion is the three-part of `|Y_C|`, not its
full order; `Basic.printed_order_obstruction` explains that distinction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.12(2), printed p.1125 (PDF p.1142), especially the proof's final sentence.
-/

public section

open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.ComponentIntersection
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem quotient_alternative_facts {Y : Subgroup G}
    (halt : Nonempty (TwoCoreQuotient Y ≃* ElementaryNine) ∨
      (IsExtraspecial 3 (TwoCoreQuotient Y) ∧ Nat.card (TwoCoreQuotient Y) = 27)) :
    IsPGroup 3 (TwoCoreQuotient Y) ∧
      (Nat.card (TwoCoreQuotient Y) = 9 ∨
        (Nat.card (TwoCoreQuotient Y) = 27 ∧ ¬ IsMulCommutative (TwoCoreQuotient Y))) := by
  rcases halt with halt | halt
  · obtain ⟨e⟩ := halt
    have hc : Nat.card (TwoCoreQuotient Y) = 9 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Fin 2 → ZMod 3) = 9
      simp only [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
      decide
    exact ⟨IsPGroup.of_card (n := 2) hc, Or.inl hc⟩
  · obtain ⟨hx, h27⟩ := halt
    let := hx
    refine ⟨IsExtraspecial.isPGroup 3 _, Or.inr ⟨h27, ?_⟩⟩
    intro hcomm
    have hz := IsExtraspecial.center_order_p 3 (TwoCoreQuotient Y)
    rw [center_eq_top_iff.mpr hcomm, card_top, h27] at hz
    omega

private theorem residual_quotient_orders
    {Y I L : Subgroup G}
    (hLI : L ≤ I) (hL : (L.subgroupOf I).IsCComponent)
    (hr : primeRank 3 L = 1) (hi : InducesInnerOnTwoCoreQuotient Y L)
    (ha : Nat.card (TwoCoreQuotient (intersectionResidual Y L)) = 3)
    (hq : IsPGroup 3 (TwoCoreQuotient Y))
    (hshape : Nat.card (TwoCoreQuotient Y) = 9 ∨
      (Nat.card (TwoCoreQuotient Y) = 27 ∧ ¬ IsMulCommutative (TwoCoreQuotient Y)))
    (hprod : (Y : Set G) =
      (intersectionResidual Y L : Set G) * (centralizerResidual Y L : Set G)) :
    Nat.card (TwoCoreQuotient Y) = 9 ∧
      Nat.card (TwoCoreQuotient (centralizerResidual Y L)) = 3 := by
  let A := intersectionResidual Y L
  let C := centralizerResidual Y L
  have hAY : A ≤ Y := (intersectionResidual_le Y L).trans inf_le_left
  have hCY : C ≤ Y := (centralizerResidual_le Y L).trans inf_le_left
  let A₀ := A.subgroupOf Y
  let C₀ := C.subgroupOf Y
  let : A₀.Normal := normal_subgroupOf_of_le_normalizer
    (normalizes_intersectionResidual hi.normalizes)
  let : C₀.Normal := normal_subgroupOf_of_le_normalizer
    (normalizes_centralizerResidual hi.normalizes)
  have hgen : A₀ ⊔ C₀ = ⊤ := by
    apply top_unique
    intro y _
    have hy : (y : G) ∈ (Y : Set G) := y.property
    rw [hprod] at hy
    obtain ⟨a, ha, c, hc, he⟩ := hy
    exact mem_sup_of_normal_left.mpr
      ⟨⟨a, hAY ha⟩, ha, ⟨c, hCY hc⟩, hc, Subtype.ext he⟩
  have hinf : IsPGroup 2 (A₀ ⊓ C₀ : Subgroup Y) :=
    (InnerSplitting.residual_intersection_isTwoGroup hLI hL hr ha).comap_subtype
  let eA : A₀ ≃* A := subgroupOfEquivOfLe hAY
  let eC : C₀ ≃* C := subgroupOfEquivOfLe hCY
  let eAQ := QuotientGroup.congr (pCore 2 A₀) (pCore 2 A) eA (pCore_map_iso 2 eA)
  let eCQ := QuotientGroup.congr (pCore 2 C₀) (pCore 2 C) eC (pCore_map_iso 2 eC)
  have hAc : Nat.card (A₀ ⧸ pCore 2 A₀) = 3 := (Nat.card_congr eAQ.toEquiv).trans ha
  obtain ⟨hYc, hCc⟩ := InnerSplitting.quotient_orders_of_normal_product A₀ C₀ hgen hinf hAc hq hshape
  exact ⟨hYc, (Nat.card_congr eCQ.toEquiv).symm.trans hCc⟩

/-- The inner-action conclusion of 15.3.12(2), with the corrected three-part
assertion. The earlier local facts and the independent odd-rank outputs are
explicit inputs; their source assembly remains with their respective owners. -/
theorem inner_splitting_of_preliminary_facts
    {M Y S V₁ Yplus I L : Subgroup G}
    (_hHyp : Hypothesis15310 M Y S V₁ Yplus)
    (_hI : I ∈ outsideFamily Yplus S M)
    (hLI : L ≤ I) (hL : (L.subgroupOf I).IsCComponent)
    (hLrank : primeRank 3 L = 1) (_hYrank : primeRank 3 Yplus = 2)
    (hinner : InducesInnerOnTwoCoreQuotient Yplus L)
    (hne : intersectionResidual Yplus L ≠ ⊥)
    (hAcard : Nat.card (TwoCoreQuotient (intersectionResidual Yplus L)) = 3)
    (htheta : theta (M ⊓ I) = Yplus)
    (halt : Nonempty (TwoCoreQuotient Yplus ≃* ElementaryNine) ∨
      (IsExtraspecial 3 (TwoCoreQuotient Yplus) ∧ Nat.card (TwoCoreQuotient Yplus) = 27))
    (hexponent : Monoid.exponent (TwoCoreQuotient Yplus) ∣ 3) :
    (Yplus : Set G) =
        (intersectionResidual Yplus L : Set G) * (centralizerResidual Yplus L : Set G) ∧
      IsPGroup 2 (intersectionResidual Yplus L ⊓ centralizerResidual Yplus L : Subgroup G) ∧
      Nat.card (TwoCoreQuotient Yplus) = 9 ∧
      Nat.card (TwoCoreQuotient (centralizerResidual Yplus L)) = 3 ∧
      Nonempty (TwoCoreQuotient Yplus ≃* ElementaryNine) ∧
      3 ^ (Nat.card (intersectionResidual Yplus L)).factorization 3 = 3 ∧
      3 ^ (Nat.card (centralizerResidual Yplus L)).factorization 3 = 3 := by
  obtain ⟨hq, hshape⟩ := quotient_alternative_facts halt
  have hprod := InnerSplitting.residual_factorization_of_local_facts htheta hLI hL hLrank
    hinner hne hAcard hq hexponent
  have hinf := InnerSplitting.residual_intersection_isTwoGroup hLI hL hLrank hAcard
  obtain ⟨hYc, hCc⟩ := residual_quotient_orders hLI hL hLrank hinner hAcard hq hshape hprod
  exact ⟨hprod, hinf, hYc, hCc, quotient_equiv_elementaryNine_of_card hYc hexponent,
    three_part_eq_three_of_quotient_card hAcard, three_part_eq_three_of_quotient_card hCc⟩

end CFSG.Quasithin.Chapter15.Section03.ComponentIntersection

end
