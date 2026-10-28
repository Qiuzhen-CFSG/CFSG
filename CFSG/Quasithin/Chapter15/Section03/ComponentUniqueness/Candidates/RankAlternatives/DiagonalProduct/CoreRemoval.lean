module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.Alternatives
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.Basic
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Removing the two-core supplement in the diagonal branch

Write A = O²(Y₊ ∩ L). A cover Y₊ ⊆ A⟨y⟩O₂(Y) does not by itself
give Y₊ = A⟨y⟩. The additional action bound used here is
[Y₊ ∩ O₂(Y), y] ≤ A. It makes A⟨y⟩ normal in Y₊; the cover then makes
the quotient a two-group. Since Y₊ = θ(M ∩ I) is two-perfect, the quotient
is trivial. Neither O₂(Y) = 1 nor exponent three for Y₊ is assumed.

`DiagonalCoreCover` records the cover and action bound as outputs still to
be constructed from the local matrix action. The core is the core of the
displayed Y, not silently the core of Y₊. Only its intersection with Y₊
is used, so no inclusion O₂(Y) ≤ Y₊ is required.

We also check that the compatible outer quotient actions really have
actors outside L. This uses the actual quotient homomorphism and model
equivalence, without a center or order recognition argument.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), final
paragraph of 15.3.37, printed p.1135. The local cover and core-action
construction, and the exclusion of the unitary branch, remain obligations.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.Candidates
variable {G : Type*} [Group G]

/-- The intermediate cover with the source two-core, together with the
action bound needed to remove it. This is an output predicate, not an
assertion that the local setup supplies these two facts. -/
def DiagonalCoreCover (Y Yplus L : Subgroup G) (y : G) : Prop :=
  (Yplus : Set G) ⊆
    ((componentPart Yplus L : Set G) * (zpowers y : Set G)) * (Y.pCoreIn 2 : Set G) ∧
  ∀ q ∈ Yplus, q ∈ Y.pCoreIn 2 → ⁅q, y⁆ ∈ componentPart Yplus L

private theorem not_mem_of_outer_quotient {H : Type*} [Group H]
    {L : Subgroup G} {y : G} (α : MulAut L) (β : MulAut H)
    (f : L →* H) (hf : Function.Surjective f)
    (hconj : ConjugationOn L y α) (houter : β ∉ MulAut.innerSubgroup H)
    (hcompat : ∀ x : L, f (α x) = β (f x)) : y ∉ L := by
  intro hy
  apply houter
  refine ⟨f ⟨y, hy⟩, ?_⟩
  ext z
  obtain ⟨x, rfl⟩ := hf z
  change f ⟨y, hy⟩ * f x * (f ⟨y, hy⟩)⁻¹ = β (f x)
  rw [← hcompat x, ← map_inv, ← map_mul, ← map_mul]
  apply congrArg f
  exact Subtype.ext (hconj x).symm

/-- A compatible linear outer action cannot be induced by an element of L. -/
theorem LinearDiagonalOnTwoQuotient.not_mem {L : Subgroup G} {y : G} {q : ℕ}
    (h : LinearDiagonalOnTwoQuotient L y q) : y ∉ L := by
  obtain ⟨F, _, _, _, e, α, d, hc, ho, he⟩ := h
  exact not_mem_of_outer_quotient α (Matrix.PSL3.OuterSolvable.linearConj F d)
    (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hc ho he

/-- The unitary action has the same genuine outer-actor consequence. -/
theorem UnitaryDiagonalOnTwoQuotient.not_mem {L : Subgroup G} {y : G} {q : ℕ}
    (h : UnitaryDiagonalOnTwoQuotient L y q) : y ∉ L := by
  obtain ⟨F, _, _, J, _, _, e, α, d, hc, ho, he⟩ := h
  exact not_mem_of_outer_quotient α (J.unitaryConjHom d)
    (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hc ho he

private theorem normalizes_join_of_commutator {A Q : Subgroup G} {y : G}
    (hQA : Q ≤ normalizer (A : Set G))
    (hcomm : ∀ q ∈ Q, ⁅q, y⁆ ∈ A) :
    Q ≤ normalizer ((A ⊔ zpowers y : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro q hq d hd
  have hmap : (A ⊔ zpowers y).map (MulAut.conj q).toMonoidHom ≤ A ⊔ zpowers y := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    apply sup_le
    · exact (mem_normalizer_iff_map_conj_eq.mp (hQA hq)).le.trans le_sup_left
    · apply zpowers_le.mpr
      change q * y * q⁻¹ ∈ A ⊔ zpowers y
      have hh := (A ⊔ zpowers y).mul_mem (mem_sup_left (hcomm q hq))
        (mem_sup_right (mem_zpowers y))
      simpa only [commutatorElement_def, inv_mul_cancel_right] using hh
  exact hmap (mem_map_of_mem (MulAut.conj q).toMonoidHom hd)

private theorem product_of_two_group_cover {Y A Q : Subgroup G} {y : G}
    (hY : IsPPerfect 2 Y) (hAY : A ≤ Y) (hy : y ∈ Y)
    (hYA : Y ≤ normalizer (A : Set G)) (hQ : IsPGroup 2 Q)
    (hcomm : ∀ q ∈ Y, q ∈ Q → ⁅q, y⁆ ∈ A)
    (hcover : (Y : Set G) ⊆ ((A : Set G) * (zpowers y : Set G)) * (Q : Set G)) :
    (Y : Set G) = (A : Set G) * (zpowers y : Set G) := by
  let D := A ⊔ zpowers y
  let R := Y ⊓ Q
  have hDY : D ≤ Y := sup_le hAY (zpowers_le.mpr hy)
  have hRY : R ≤ Y := inf_le_left
  have hD : (D : Set G) = (A : Set G) * (zpowers y : Set G) :=
    coe_mul_of_right_le_normalizer_left A (zpowers y) (zpowers_le.mpr (hYA hy))
  have hgen : D ⊔ R = Y := by
    apply le_antisymm (sup_le hDY hRY)
    intro x hx
    obtain ⟨d, hd, q, hq, he⟩ := hcover hx
    have hdD : d ∈ D := by rwa [← hD] at hd
    have hqY : q ∈ Y := by
      have hh := Y.mul_mem (Y.inv_mem (hDY hdD)) hx
      simpa only [← he, inv_mul_cancel_left] using hh
    rw [← he]
    exact (D ⊔ R).mul_mem (mem_sup_left hdD) (mem_sup_right ⟨hqY, hq⟩)
  have hYD : Y ≤ normalizer (D : Set G) := by
    rw [← hgen]
    exact sup_le D.le_normalizer
      (normalizes_join_of_commutator (hRY.trans hYA) (fun q hq => hcomm q hq.1 hq.2))
  let : (D.subgroupOf Y).Normal := normal_subgroupOf_of_le_normalizer hYD
  have htop : D.subgroupOf Y = ⊤ := by
    have hpR : IsPGroup 2 R := hQ.to_le inf_le_right
    have hp : IsPGroup 2 (Y ⧸ D.subgroupOf Y) :=
      isPGroup_quotient_of_sup_eq_top (D.subgroupOf Y) (R.subgroupOf Y)
        hpR.comap_subtype (by rw [← subgroupOf_sup hDY hRY, hgen, subgroupOf_self])
    have hr : pResidual 2 Y ≤ D.subgroupOf Y := sInf_le ⟨inferInstance, hp⟩
    rw [(pResidual_eq_top_iff 2 Y).mpr hY] at hr
    exact top_unique hr
  have hYD' : Y ≤ D := by
    intro x hx
    exact (show (⟨x, hx⟩ : Y) ∈ D.subgroupOf Y from htop ▸ mem_top _)
  exact (congrArg (fun H : Subgroup G => (H : Set G))
    (le_antisymm hYD' hDY)).trans hD

variable [Finite G]

/-- Two-perfectness removes the displayed two-core only after its action
on the chosen actor has been controlled. All normality is relative to Y₊. -/
theorem DiagonalCoreCover.product {Y Yplus L : Subgroup G} {y : G}
    (h : DiagonalCoreCover Y Yplus L y)
    (hY : IsPPerfect 2 Yplus) (hy : y ∈ Yplus)
    (hn : Yplus ≤ normalizer (L : Set G)) :
    (Yplus : Set G) = (componentPart Yplus L : Set G) * (zpowers y : Set G) := by
  exact product_of_two_group_cover hY ((map_subtype_le _).trans inf_le_left) hy
    (ComponentIntersection.normalizes_intersectionResidual hn)
    (Y.isPGroup_pCoreIn 2) h.2 h.1

end CFSG.Quasithin.Chapter15.Section03.Candidates
