module

public import CFSG.Quasithin.Chapter12.Section08.Actions
public import BenderSuzuki.MatrixGroups.SuzukiZero
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Theory.Representation.ElementaryPerfectSplit
public import Theory.Representation.BinaryPrimeDegree.Quotient

/-!
# The degree lower bound for the original quintic quotient

The literal action of H on the tilded local span has kernel O₂(H).
When H/O₂(H) is D₁₀ or Sz(2), its order is divisible by five. The
binary general-linear-group order formula then forces dimension at
least four, because two has multiplicative order four modulo five.
No irreducibility assumption is required.

This supplies the lower bound for the actual quotient module in the
index-five branch of Aschbacher--Smith, Theorem 14.2.20(1), printed
p.988, using the kernel established in 14.2.6 and 12.8.4(4).
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02
open Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

/-- The original faithful quotient has binary degree at least four in
both quintic local models. -/
theorem index_five_tilde_finrank_ge_four {T : Sylow 2 G} {V : Subgroup G} (F : InvariantFlag T V 2)
    (H : Subgroup G) (hHF : H ≤ F.H)
    [IsElementaryAbelian 2 (F.tilde (F.UH H))]
    (hker : (F.localTildeAction H hHF).ker = pCore 2 H)
    (hmodel : Nonempty ((H ⧸ pCore 2 H) ≃* DihedralGroup 5) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)) :
    4 ≤ Module.finrank (ZMod 2) (Additive (F.tilde (F.UH H))) := by
  let ρ := Representation.elementaryRepresentation (p := 2) (F.localTildeAction H hHF)
  have hk : ρ.ker ≤ pCore 2 H := by
    rw [← hker]
    intro h hh
    rw [MonoidHom.mem_ker] at hh ⊢
    apply MulEquiv.ext
    intro v
    exact congrArg Additive.toMul (congrArg
      (fun f : Module.End (ZMod 2) (Additive (F.tilde (F.UH H))) => f (Additive.ofMul v)) hh)
  have hdiv : 5 ∣ (pCore 2 H).index := by
    rw [index_eq_card]
    rcases hmodel with hmodel | hmodel
    · obtain ⟨f⟩ := hmodel
      rw [Nat.card_congr f.toEquiv, DihedralGroup.nat_card]
      decide
    · obtain ⟨f⟩ := hmodel
      rw [Nat.card_congr f.toEquiv, BenderSuzuki.MatrixGroups.suzukiZero_card]
      decide
  simpa only [Representation.BinaryPrimeDegree.orderOf_two_mod_five] using
    Representation.BinaryPrimeDegree.orderOf_le_finrank_of_kernel_le
      ρ (pCore 2 H) hk (p := 5) (by decide) (by decide) hdiv

end CFSG.Quasithin.Chapter14.Section02
