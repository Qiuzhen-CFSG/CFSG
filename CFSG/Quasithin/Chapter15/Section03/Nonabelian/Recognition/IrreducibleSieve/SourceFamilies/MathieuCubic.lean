module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.MarkedAutomorphism
public import Theory.Mathieu.SylowFixedCubic

/-!
# Direct source exclusions for the three Mathieu components

The source marked involution induces an involutory automorphism of its
normal component and fixes an intrinsic Sylow two-subgroup pointwise.
In each of M₁₂, M₂₂ and M₂₄ the model calculation supplies a fixed cubic.
Transport through the literal component inclusion contradicts the source
prime-to-three condition on the marked involution's centralizer.

These are group-level exclusions using the actual source action, with no
module-classification premise. Source: Aschbacher--Smith, 15.3.58, p.1149.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve
open Sporadic.Mathieu

variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {X K : Subgroup H} {T : Sylow 2 H}
  {v : H} {s : ℕ}

private theorem exclude_of_fixed_cubic {D : Type*} [Group D] [Finite D]
    (h : SourceData ρ X T v s) (hK : ComponentData ρ K) (e : K ≃* D)
    (hmodel : ∀ (a : MulAut D), orderOf a = 2 → ∀ S : Sylow 2 D,
      (∀ x ∈ S, a x = x) → ∃ c : D, orderOf c = 3 ∧ a c = c) : False := by
  obtain ⟨a, ha, ⟨S, hS⟩, hcomm⟩ := h.marked_automorphism hK e
  obtain ⟨c, hc, hfix⟩ := hmodel a ha S hS
  exact h.no_model_cubic_commuting e c hc ((hcomm c).mp hfix)

/-- A single M₁₂ component contradicts the marked source centralizer condition. -/
theorem SourceData.not_m12_component (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) (e : K ≃* M12) : False :=
  exclude_of_fixed_cubic h hK e m12_fixed_cubic_of_fixes_sylow

/-- A single M₂₂ component contradicts the marked source centralizer condition. -/
theorem SourceData.not_m22_component (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) (e : K ≃* M22) : False :=
  exclude_of_fixed_cubic h hK e m22_fixed_cubic_of_fixes_sylow

/-- A single M₂₄ component contradicts the marked source centralizer condition. -/
theorem SourceData.not_m24_component (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) (e : K ≃* M24) : False :=
  exclude_of_fixed_cubic h hK e m24_fixed_cubic_of_fixes_sylow

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve
