module

public import Theory.GroupTheory.ElementaryNineMarkedResiduals
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.CentralFactors.Construction

/-!
# Identifying the marked elementary-nine residual lifts

The genuine quotient `L₁ / O₂(L₁) ≃ C₃ × C₃`, its two marked cubic images,
and the specified fixing/inverting actor identify an invariant nontrivial
proper two-perfect subgroup with `L₀` or `X = L₁,+`. The residual argument
also proves normality of both marked factors inside `L₁`.

The final adapter applies this result to the centralizer residual constructed
in `Construction`. Its two-perfectness, containment and invariance are derived
there. Nontriviality, properness, the quotient marking and the actor remain
explicit geometric inputs for the source assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Notation 13.2.1
and 13.2.2(3), printed pp.877–878; proof of 13.7.5(7), p.938; proof of 13.8.20,
p.955. Two-perfectness is the essential residual condition in the p.938 form.
-/

open CFSG.Quasithin.Chapter13.Section08
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.CentralFactors.MarkedNine

variable {G : Type*} [Group G]

private theorem perfect_subgroupOf {Y D : Subgroup G} (hle : Y ≤ D)
    (hY : IsPPerfect 2 Y) : IsPPerfect 2 (Y.subgroupOf D) :=
  hY.of_surjective (subgroupOfEquivOfLe hle).symm.toMonoidHom
    (subgroupOfEquivOfLe hle).symm.surjective

private theorem core_normalizes_subgroupOf {Y D : Subgroup G} (hle : Y ≤ D)
    (hn : D.pCoreIn 2 ≤ normalizer (Y : Set G)) :
    pCore 2 D ≤ normalizer (Y.subgroupOf D : Set D) := by
  rw [← subgroupOf_normalizer_eq hle]
  intro x hx
  exact hn (mem_map.mpr ⟨x, hx, rfl⟩)

/-- The marked residual lifts are normal in L₁, with no assertion of
normality in the ambient group. -/
public theorem marked_normal (L₁ L₀ X : Subgroup G)
    (e : L₁ ⧸ pCore 2 L₁ ≃* Multiplicative (ZMod 3) × Multiplicative (ZMod 3))
    (hgen : L₀ ⊔ X = L₁) (h₀ : IsPPerfect 2 L₀) (hX : IsPPerfect 2 X)
    (hn₀ : L₁.pCoreIn 2 ≤ normalizer (L₀ : Set G))
    (hnX : L₁.pCoreIn 2 ≤ normalizer (X : Set G)) :
    (L₀.subgroupOf L₁).Normal ∧ (X.subgroupOf L₁).Normal := by
  have h₀le : L₀ ≤ L₁ := le_sup_left.trans_eq hgen
  have hXle : X ≤ L₁ := le_sup_right.trans_eq hgen
  exact ⟨Theory.GroupTheory.ElementaryNineMarkedResiduals.normal_of_elementaryNine e
      (L₀.subgroupOf L₁) (perfect_subgroupOf h₀le h₀) (core_normalizes_subgroupOf h₀le hn₀),
    Theory.GroupTheory.ElementaryNineMarkedResiduals.normal_of_elementaryNine e
      (X.subgroupOf L₁) (perfect_subgroupOf hXle hX) (core_normalizes_subgroupOf hXle hnX)⟩

/-- Source adapter for the marked residuals L₀ and X = L₁,+. The automorphism
acts on the actual subgroup L₁ and the images are taken in its actual two-core
quotient. Nontriviality and properness remain explicit obligations. -/
public theorem eq_L0_or_X (L₁ L₀ X Y : Subgroup G)
    (e : L₁ ⧸ pCore 2 L₁ ≃* Multiplicative (ZMod 3) × Multiplicative (ZMod 3))
    (hgen : L₀ ⊔ X = L₁) (hYL : Y ≤ L₁)
    (h₁ : IsPPerfect 2 L₁) (h₀ : IsPPerfect 2 L₀)
    (hX : IsPPerfect 2 X) (hY : IsPPerfect 2 Y)
    (hn₀ : L₁.pCoreIn 2 ≤ normalizer (L₀ : Set G))
    (hnX : L₁.pCoreIn 2 ≤ normalizer (X : Set G))
    (hnY : L₁.pCoreIn 2 ≤ normalizer (Y : Set G))
    (hc₀ : Nat.card ((L₀.subgroupOf L₁).map (QuotientGroup.mk' (pCore 2 L₁))) = 3)
    (hcX : Nat.card ((X.subgroupOf L₁).map (QuotientGroup.mk' (pCore 2 L₁))) = 3)
    (τ : MulAut L₁)
    (hfix : ∀ a : L₁, a.val ∈ L₀ →
      QuotientGroup.mk' (pCore 2 L₁) (τ a) = QuotientGroup.mk' (pCore 2 L₁) a)
    (hinv : ∀ b : L₁, b.val ∈ X →
      QuotientGroup.mk' (pCore 2 L₁) (τ b) = (QuotientGroup.mk' (pCore 2 L₁) b)⁻¹)
    (hτY : ∀ y : L₁, y.val ∈ Y → (τ y).val ∈ Y)
    (hne : Y ≠ ⊥) (hproper : Y ≠ L₁) : Y = L₀ ∨ Y = X := by
  have h₀le : L₀ ≤ L₁ := le_sup_left.trans_eq hgen
  have hXle : X ≤ L₁ := le_sup_right.trans_eq hgen
  have hgen' : L₀.subgroupOf L₁ ⊔ X.subgroupOf L₁ = ⊤ := by
    apply map_injective L₁.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le h₀le,
      map_subgroupOf_eq_of_le hXle, ← MonoidHom.range_eq_map, range_subtype, hgen]
  have hne' : Y.subgroupOf L₁ ≠ ⊥ := by
    intro h
    apply hne
    rw [← map_subgroupOf_eq_of_le hYL, h, Subgroup.map_bot]
  have hproper' : Y.subgroupOf L₁ ≠ ⊤ := by
    intro h
    apply hproper
    rw [← map_subgroupOf_eq_of_le hYL, h, ← MonoidHom.range_eq_map, range_subtype]
  have he := Theory.GroupTheory.ElementaryNineMarkedResiduals.eq_marked_of_elementaryNine e h₁
    (L₀.subgroupOf L₁) (X.subgroupOf L₁) (Y.subgroupOf L₁)
    (perfect_subgroupOf h₀le h₀) (perfect_subgroupOf hXle hX) (perfect_subgroupOf hYL hY)
    (core_normalizes_subgroupOf h₀le hn₀) (core_normalizes_subgroupOf hXle hnX)
    (core_normalizes_subgroupOf hYL hnY) hgen' hc₀ hcX τ hfix hinv hτY hne' hproper'
  have he := he.imp (congrArg (fun S : Subgroup L₁ => S.map L₁.subtype))
    (congrArg (fun S : Subgroup L₁ => S.map L₁.subtype))
  simpa only [map_subgroupOf_eq_of_le hYL, map_subgroupOf_eq_of_le h₀le,
    map_subgroupOf_eq_of_le hXle] using he

/-- Apply the marked-line identification to the actual centralizer residual.
The quotient marking and its actor remain explicit. The construction supplies
the candidate's two-perfectness and invariance; its nontriviality and properness
are the remaining geometric obligations of the caller. -/
public theorem centralFactor_eq_L0_or_X [Finite G]
    (H K L₁ L₀ X T : Subgroup G) [(Source.starImage H K).Normal]
    (e : L₁ ⧸ pCore 2 L₁ ≃* Multiplicative (ZMod 3) × Multiplicative (ZMod 3))
    (hgen : L₀ ⊔ X = L₁) (hL₁H : L₁ ≤ H) (hTH : T ≤ H)
    (h₁ : IsPPerfect 2 L₁) (h₀ : IsPPerfect 2 L₀) (hX : IsPPerfect 2 X)
    (hn₀ : L₁.pCoreIn 2 ≤ normalizer (L₀ : Set G))
    (hnX : L₁.pCoreIn 2 ≤ normalizer (X : Set G))
    (hQT : L₁.pCoreIn 2 ≤ T) (hTL₁ : T ≤ normalizer (L₁ : Set G))
    (hc₀ : Nat.card ((L₀.subgroupOf L₁).map (QuotientGroup.mk' (pCore 2 L₁))) = 3)
    (hcX : Nat.card ((X.subgroupOf L₁).map (QuotientGroup.mk' (pCore 2 L₁))) = 3)
    (t : normalizer (L₁ : Set G)) (ht : t.val ∈ T)
    (hfix : ∀ a : L₁, a.val ∈ L₀ →
      QuotientGroup.mk' (pCore 2 L₁) (L₁.normalizerMonoidHom t a) =
        QuotientGroup.mk' (pCore 2 L₁) a)
    (hinv : ∀ b : L₁, b.val ∈ X →
      QuotientGroup.mk' (pCore 2 L₁) (L₁.normalizerMonoidHom t b) =
        (QuotientGroup.mk' (pCore 2 L₁) b)⁻¹)
    (hne : centralFactor H K L₁ ≠ ⊥) (hproper : centralFactor H K L₁ ≠ L₁) :
    centralFactor H K L₁ = L₀ ∨ centralFactor H K L₁ = X := by
  have hTY := centralFactor_T_invariant H K L₁ T hL₁H hTH hTL₁
  apply eq_L0_or_X L₁ L₀ X (centralFactor H K L₁) e hgen
    (centralFactor_le H K L₁) h₁ h₀ hX (centralFactor_isPPerfect H K L₁)
    hn₀ hnX (hQT.trans hTY) hc₀ hcX (L₁.normalizerMonoidHom t) hfix hinv
    _ hne hproper
  intro y hy
  exact (mem_normalizer_iff.mp (hTY ht) y.val).mp hy

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.CentralFactors.MarkedNine
