module
public import Theory.ElementaryAbelian.Quotient
public import Theory.Representation.ElementaryAbelianAction
public import Theory.Representation.IrreducibleFixedPoints
public import Mathlib.GroupTheory.Index

/-!
# Centralizers above an irreducible quotient

If E maps onto the actor of an irreducible conjugation action on V/Z
of dimension at least two, every element of C_V(E) belongs to Z.
The proof sends an actual centralizing element into the quotient and
uses the vanishing of the global fixed space. No ambient normality of
V or Z is required: normalization is relative to the specified actor.

A companion counting lemma excludes H intersect K <= Z whenever
|H| > |Z| [Y : Y intersect K] and H <= Y. Together they supply the
centralizer contradiction in DGS85, Groups and Graphs (1985), (12.7),
printed pp.184--185, with the original subgroup and quotient maps.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G M : Type*} [Group G] [Group M]

/-- A subgroup surjecting onto the irreducible actor fixes only the denominator. -/
theorem centralizer_le_layer_of_irreducible_quotient
    (A V Z E : Subgroup G) [IsElementaryAbelian 2 V]
    [(Z.subgroupOf V).Normal]
    (hAV : A ≤ normalizer (V : Set G))
    (f : A →* M)
    (hgen : (E.subgroupOf A).map f = ⊤)
    (ρ : Representation (ZMod 2) M (Additive (V ⧸ Z.subgroupOf V)))
    [ρ.IsIrreducible]
    (hdim : 2 ≤ Module.finrank (ZMod 2) (Additive (V ⧸ Z.subgroupOf V)))
    (hact : ∀ a : A, ∀ v : V,
      (ρ (f a) (Additive.ofMul (QuotientGroup.mk v))).toMul =
        QuotientGroup.mk ⟨(a : G) * v * (a : G)⁻¹,
          le_normalizer_iff.mp hAV a a.property v v.property⟩) :
    V ⊓ centralizer (E : Set G) ≤ Z := by
  intro v hv
  let w : V := ⟨v,hv.1⟩
  have hfixed : Additive.ofMul (QuotientGroup.mk w) ∈
      Representation.OneCohomology.fixed ρ := by
    intro a
    obtain ⟨b,hb,rfl⟩ := mem_map.mp (show a ∈ (E.subgroupOf A).map f from hgen ▸ mem_top a)
    change (ρ (f b) (Additive.ofMul (QuotientGroup.mk w))).toMul = QuotientGroup.mk w
    rw [hact]
    congr 1
    apply Subtype.ext
    change (b : G) * v * (b : G)⁻¹ = v
    have hc : (b : G) * v = v * (b : G) := hv.2 _ hb
    rw [hc, mul_inv_cancel_right]
  rw [Representation.OneCohomology.fixed_eq_bot_of_irreducible_finrank ρ hdim,
    Submodule.mem_bot] at hfixed
  exact (QuotientGroup.eq_one_iff w).mp (congrArg Additive.toMul hfixed)

/-- An index bound prevents a large subgroup from having too small an intersection. -/
theorem inf_not_le_of_card_gt_index_mul_card
    (H Y K Z : Subgroup G) [Finite H] [Finite Y] [Finite Z]
    (hHY : H ≤ Y) {q : ℕ} (hi : K.relIndex Y ≤ q)
    (hcard : Nat.card Z * q < Nat.card H) : ¬ H ⊓ K ≤ Z := by
  intro hle
  let : Finite (H ⊓ K : Subgroup G) := Finite.of_injective
    (inclusion (show H ⊓ K ≤ H from inf_le_left)) (inclusion_injective _)
  have hc : Nat.card (H ⊓ K : Subgroup G) ≤ Nat.card Z :=
    Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective _)
  have hi' : (H ⊓ K).relIndex H ≤ q := by
    rw [inf_relIndex_left]
    exact (relIndex_le_of_le_right hHY index_ne_zero_of_finite).trans hi
  have he := relIndex_mul_relIndex (⊥ : Subgroup G) (H ⊓ K) H bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left] at he
  exact (not_lt_of_ge (he ▸ Nat.mul_le_mul hc hi')) hcard

end Subgroup
