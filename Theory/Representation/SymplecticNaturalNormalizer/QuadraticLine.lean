module
public import Theory.Representation.SymplecticNaturalNormalizer.QuadraticOuter
/-!
# Quadratic actors preserving a natural field line

A field-linear quadratic actor fixing a field line setwise fixes it pointwise:
its scalar has square-zero difference from one. In an ambient natural
symplectic action over F4, any quadratic actor moving such a line therefore
has an outer field twist and has order at most two.

Source application: MS93 (3.4), first index-two contradiction, printed p.868.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
namespace SymplecticNaturalNormalizer
variable {F G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [Group G]

omit [Finite F] [CharP F 2] in
theorem quadratic_fixes_invariant_line_of_le_component
    (B : Subgroup G) (e : B ≃* Sp F) (ρ : Representation (ZMod 2) G (Vector F))
    (hB : ∀ b : B, ∀ w, ρ (b:G) w = symplecticNatural 2 (e b) w)
    (A : Subgroup G) (hq : IsQuadratic ρ A) (hAB : A ≤ B)
    (v : Vector F) (hv : v ≠ 0)
    (hline : ∀ a ∈ A, ∃ c : F, ρ a v = c • v) :
    ∀ a ∈ A, ∀ c : F, ρ a (c • v) = c • v := by
  intro a ha c
  have hlin (r : F) (w : Vector F) : ρ a (r • w) = r • ρ a w := by
    rw [hB ⟨a,hAB ha⟩,hB ⟨a,hAB ha⟩]
    exact map_smul (symplecticNatural 2 (e ⟨a,hAB ha⟩)) r w
  obtain ⟨r,hr⟩ := hline a ha
  have hquadratic := hq a ha a ha v
  have hdisp : ρ a v-v = (r-1) • v := by rw [hr,sub_smul,one_smul]
  rw [hdisp,hlin,hr] at hquadratic
  have hz : ((r-1)*(r-1)) • v = 0 := by
    rw [mul_sub,mul_one,sub_smul,mul_smul,hquadratic,sub_self]
  have hr1 : r=1 := sub_eq_zero.mp (mul_self_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hv))
  rw [hlin,hr,hr1,one_smul]

theorem quadratic_card_le_two_of_moves_invariant_line
    (hF : Nat.card F = 4) (B : Subgroup G) [B.Normal]
    (hcent : centralizer (B : Set G) ≤ B)
    (e : B ≃* Sp F) (ρ : Representation (ZMod 2) G (Vector F))
    (hfaith : Function.Injective ρ)
    (hB : ∀ b : B, ∀ w, ρ (b:G) w = symplecticNatural 2 (e b) w)
    (A : Subgroup G) (hq : IsQuadratic ρ A)
    (v : Vector F) (hv : v ≠ 0)
    (hline : ∀ a ∈ A, ∃ c : F, ρ a v = c • v)
    (hmove : ∃ a ∈ A, ∃ c : F, ρ a (c • v) ≠ c • v) : Nat.card A ≤ 2 := by
  apply quadratic_card_le_two_of_not_le_component hF B hcent e ρ hfaith hB A hq
  intro hAB
  obtain ⟨a,ha,c,hc⟩ := hmove
  exact hc (quadratic_fixes_invariant_line_of_le_component B e ρ hB A hq hAB v hv hline a ha c)

end SymplecticNaturalNormalizer

