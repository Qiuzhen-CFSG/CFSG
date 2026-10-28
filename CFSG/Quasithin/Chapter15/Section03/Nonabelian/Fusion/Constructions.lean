module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Constructions
public import Theory.GroupAction.AutomorphismFixedSubgroup

/-!
# Marked involutions and the blocks in 15.3.61

The definitions keep `U_a` tied to the actual conjugation action on `U/Z`,
and fix `B_i = C_P(D_i)V` and `E_i = B_i ∩ U`. Joins are used for subgroup
products, with a product equation under the source centralization hypothesis.
The order-two subgroups supply actual generating ambient involutions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
printed pp.1150–1151. No action recognition or fusion assertion is assumed by
these definitions.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion
variable {G : Type*} [Group G]

/-- The block `B_i = C_P(D_i)V`, expressed as a subgroup join. -/
def fusionBlock (P V D : Subgroup G) : Subgroup G :=
  (P ⊓ centralizer (D : Set G)) ⊔ V

open scoped Pointwise in
/-- Centralization in the source identifies the defining join with `C_P(D)V`. -/
theorem fusionBlock_eq_product (P V D : Subgroup G)
    (hVP : V ≤ centralizer (P : Set G)) :
    (fusionBlock P V D : Set G) =
      (P ⊓ centralizer (D : Set G) : Subgroup G) * (V : Set G) := by
  apply coe_mul_of_right_le_normalizer_left
  exact (hVP.trans (centralizer_le (show
    ((P ⊓ centralizer (D : Set G) : Subgroup G) : Set G) ⊆ P from inf_le_left))).trans
      (Subgroup.centralizer_le_normalizer _)

/-- The source's `E_i = B_i ∩ U`. -/
def blockIntersection (P V D Z ZS : Subgroup G) : Subgroup G :=
  fusionBlock P V D ⊓ closureU Z ZS

/-- The preimage in `U` of the fixed points of the actual action of `a` on `U/Z`. -/
noncomputable def fixedLift (Z ZS : Subgroup G) [(Z.subgroupOf (closureU Z ZS)).Normal]
    (a : centralizerH Z) : Subgroup G :=
  ((MulAut.fixedSubgroup (quotientAction Z ZS a)).comap
    (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)))).map (closureU Z ZS).subtype

theorem mem_fixedLift_iff (Z ZS : Subgroup G)
    [(Z.subgroupOf (closureU Z ZS)).Normal] (a : centralizerH Z) (x : G) :
    x ∈ fixedLift Z ZS a ↔ ∃ hx : x ∈ closureU Z ZS,
      quotientAction Z ZS a (QuotientGroup.mk' _ ⟨x, hx⟩) =
        QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) ⟨x, hx⟩ := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u.property, (MulAut.mem_fixedSubgroup _ _).mp hu⟩
  · rintro ⟨hx, he⟩
    exact ⟨⟨x, hx⟩, (MulAut.mem_fixedSubgroup _ _).mpr he, rfl⟩

/-- An order-two subgroup has an actual ambient involution as generator. -/
theorem exists_generator_of_card_two (A : Subgroup G) (hA : Nat.card A = 2) :
    ∃ a : G, a ∈ A ∧ orderOf a = 2 ∧ zpowers a = A := by
  obtain ⟨a, ha, _⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
  have ho : orderOf a = 2 := orderOf_eq_prime (by
    simpa only [hA] using (pow_card_eq_one' (x := a))) ha
  refine ⟨a, a.property, (Subgroup.orderOf_coe a).trans ho, ?_⟩
  have hf : Finite A := Nat.finite_of_card_ne_zero (by omega)
  let := hf
  apply eq_of_le_of_card_ge (zpowers_le.mpr a.property)
  rw [Nat.card_zpowers, Subgroup.orderOf_coe, ho, hA]

/-- Construct the source markings `Z = ⟨z⟩` and `Z_S ∩ V₁ = ⟨v⟩`. -/
theorem exists_marked_involutions (Z ZS V₁ : Subgroup G)
    (hZ : Nat.card Z = 2) (hV₁ : Nat.card (ZS ⊓ V₁ : Subgroup G) = 2) :
    ∃ z v : G, orderOf z = 2 ∧ orderOf v = 2 ∧
      zpowers z = Z ∧ zpowers v = ZS ⊓ V₁ := by
  obtain ⟨z, _, hz, hzg⟩ := exists_generator_of_card_two Z hZ
  obtain ⟨v, _, hv, hvg⟩ := exists_generator_of_card_two (ZS ⊓ V₁) hV₁
  exact ⟨z, v, hz, hv, hzg, hvg⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion
