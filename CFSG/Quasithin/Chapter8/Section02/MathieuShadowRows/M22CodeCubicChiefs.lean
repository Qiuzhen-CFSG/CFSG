module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CubicChiefCount
public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion.CodeParabolic.Cubic

/-!
# Three cubic chief factors in the marked M22 code row

The literal outer code has displacement six for every subgroup of order
three. Equivariant coordinates preserve that displacement, and cyclic duality
preserves it on the dual module. Binary cubic chief-factor counting therefore
constructs an actual complete invariant flag with exactly three noncentral
factors in both actions.

This proves the cubic count invoked in original 8.2.2(1), while retaining
the actual actor map. Original centralizer-kernel placement is handled by the
Chapter12 application, not assumed to disappear here.
Source: Aschbacher--Smith, printed pp.714--715, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender MathieuCode
open BinaryLinearThree.ParabolicCyclic.ChiefCounts
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open Section02.Offenders.Parabolic.Exclusion.CodeParabolic

/-- Every cubic in the full original code actor has three noncentral factors,
with the actual restricted action and its dual retained. -/
theorem marked_m22_code_cubic_chiefs
    {X W : Type*} [Group X] [Finite X] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) X W)
    (f : X →* m22PairStabilizer) (hf : Function.Injective f)
    (E : W ≃ₗ[ZMod 2] M22Code)
    (hE : ∀ x v, E (ρ x v) = m22OuterCodeRepresentation (f x) (E v))
    (hX : Nat.card X = 3) :
    HasCount ρ 3 ∧ HasCount ρ.dual 3 := by
  let : Finite (Module.Dual (ZMod 2) W) :=
    Finite.of_injective (fun f : Module.Dual (ZMod 2) W => (f : W → ZMod 2)) DFunLike.coe_injective
  have hc := (outer_cubic_displacement ((⊤ : Subgroup X).map f)
    ((card_map_of_injective hf).trans (card_top.trans hX))).1
  have hd : fixedCodim ρ ⊤ = 6 :=
    (fixedCodim_map_equivariant ρ m22OuterCodeRepresentation f E hE ⊤).trans hc
  have hdual : fixedCodim ρ.dual ⊤ = 6 := by
    let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    let : IsCyclic X := isCyclic_of_prime_card hX
    obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α := X)
    have he : zpowers g = ⊤ := top_unique (fun x _ => hg x)
    rw [← he, fixedCodim_zpowers_dual, he]
    exact hd
  exact ⟨NormalizedShadowRows.cubic_count_of_fixedCodim ρ hX 3 hd,
    NormalizedShadowRows.cubic_count_of_fixedCodim ρ.dual hX 3 hdual⟩

end CFSG.Quasithin.Chapter8.MathieuShadowRows
