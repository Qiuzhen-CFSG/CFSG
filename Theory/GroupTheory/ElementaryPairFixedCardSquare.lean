module

public import Theory.GroupTheory.ElementaryPairFixedCard
public import Theory.GroupTheory.ElementaryQuotientCocycles

/-!
# Counting fixed points of an exchanged elementary pair

Let an involution exchange two elementary binary subgroups A and B, both
normal in their join R. Write V for their intersection. If |C_V(a)|² = |V|,
then |C_R(a)|·|V| = |A|·|C_V(a)|.

The elementary square-root count makes every fixed element of V a
coboundary. The fixed-point counting theorem then corrects the diagonal norms
and compares the two literal quotient maps to R/B, whose kernels are V and
C_V(a). Normality of A and B puts the derived group of R in V.

Source: Aschbacher, *Sporadic Groups* (1994), Exercise 2.8, used in
Aschbacher--Smith 14.3.21(2), printed p.998.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- An exchanged elementary generating pair has the fixed-cardinality ratio
provided the fixed subgroup of its intersection has square-root order. -/
theorem elementary_pair_fixed_card_mul_of_fixed_square
    (R A B V : Subgroup G)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B] [IsElementaryAbelian 2 V]
    (hgen : A ⊔ B = R) (hnA : R ≤ normalizer (A : Set G))
    (hnB : R ≤ normalizer (B : Set G)) (hi : A ⊓ B = V)
    (a : MulAut G) (ha : Function.Involutive a) (hAB : A.map a.toMonoidHom = B)
    (hc : Nat.card (V ⊓ a.toMonoidHom.eqLocus (MonoidHom.id G) : Subgroup G) ^ 2 =
      Nat.card V) :
    Nat.card (R ⊓ a.toMonoidHom.eqLocus (MonoidHom.id G) : Subgroup G) * Nat.card V =
      Nat.card A * Nat.card (V ⊓ a.toMonoidHom.eqLocus (MonoidHom.id G) : Subgroup G) := by
  have hAR : A ≤ R := le_sup_left.trans_eq hgen
  have hBR : B ≤ R := le_sup_right.trans_eq hgen
  have hder : ⁅R, R⁆ ≤ V := by
    rw [← hi]
    apply le_inf
    · rw [← hgen]
      exact commutator_sup_le_of_normalized_derived A B (hBR.trans hnA)
        (by rw [commutator_self_eq_bot_iff.mpr inferInstance]; exact bot_le)
    · rw [← hgen, sup_comm A B]
      exact commutator_sup_le_of_normalized_derived B A (hAR.trans hnB)
        (by rw [commutator_self_eq_bot_iff.mpr inferInstance]; exact bot_le)
  have hA {x : G} (hx : x ∈ A) : a x ∈ B := hAB ▸ mem_map_of_mem _ hx
  have hB {x : G} (hx : x ∈ B) : a x ∈ A := by
    obtain ⟨y, hy, he⟩ := (show x ∈ A.map a.toMonoidHom from hAB.symm ▸ hx)
    change a y = x at he
    rw [← he, ha]
    exact hy
  have hV (x : G) (hx : x ∈ V) : a x ∈ V := by
    have hx' : x ∈ A ⊓ B := hi.symm ▸ hx
    exact hi ▸ (show a x ∈ A ⊓ B from ⟨hB hx'.2, hA hx'.1⟩)
  let b : V →* V := a.toMonoidHom.restrict hV
  let E : b.eqLocus (MonoidHom.id V) ≃
      ↥(V ⊓ a.toMonoidHom.eqLocus (MonoidHom.id G)) :=
    { toFun := fun x => ⟨x.val.val, x.val.property, congrArg Subtype.val x.property⟩
      invFun := fun x => ⟨⟨x.val, x.property.1⟩, Subtype.ext x.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hb : Function.Involutive b := fun x => Subtype.ext (ha x.val)
  have hcb : Nat.card (b.eqLocus (MonoidHom.id V)) ^ 2 = Nat.card V := by
    rw [Nat.card_congr E]
    exact hc
  apply elementary_pair_fixed_card_mul R A B V hgen hnA hi hder a ha hAB
  intro z hz hzfix
  obtain ⟨w, hw⟩ := Theory.GroupTheory.elementary_fixed_is_coboundary b hb hcb
    ⟨z, hz⟩ (Subtype.ext hzfix)
  refine ⟨w, w.property, ?_⟩
  have he := congrArg Subtype.val hw
  change z = (w : G) * a ((w : G)⁻¹) at he
  simpa only [map_inv] using he
end Subgroup
