module
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.PGroupCore
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Pointwise kernels on self-perpendicular binary subspaces

An isometry fixing a self-perpendicular subspace has every displacement in
that subspace, and hence has square one. If the original representation has
a two-group kernel, the pointwise kernel on an invariant self-perpendicular
subspace is a normal two-group and lies in the intrinsic two-core.

The chapter consumer applies this to the literal image of C_V(z) in V/V5.
It keeps the native invariant-form construction and the quotient action
kernel as explicit earlier-source obligations.

Source: Aschbacher--Smith, H.16.2(8), printed pp.402--403.
-/

public section
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- A binary isometry fixing a self-perpendicular space has square one. -/
theorem square_fixes_of_fixes_self_perp
    (ρ : Representation (ZMod 2) G V) (B : LinearMap.BilinForm (ZMod 2) V)
    (I : Submodule (ZMod 2) V) (hI : B.orthogonal I = I)
    (g : G) (hg : ∀ x y, B (ρ g x) (ρ g y) = B x y)
    (hf : ∀ v ∈ I, ρ g v = v) : ρ (g ^ 2) = 1 := by
  have hd (v : V) : ρ g v - v ∈ I := by
    rw [← hI]
    intro w hw
    rw [map_sub, ← hf w hw, hg, hf w hw, sub_self]
  ext v
  have he := hf (ρ g v - v) (hd v)
  rw [map_sub] at he
  have htwo (w : V) : w + w = 0 := by
    calc
      w + w = ((1 : ZMod 2) + 1) • w := by rw [add_smul, one_smul]
      _ = 0 := by rw [show (1 : ZMod 2) + 1 = 0 by decide, zero_smul]
  change ρ (g ^ 2) v = v
  rw [pow_two, map_mul, Module.End.mul_apply]
  apply sub_eq_zero.mp
  calc
    ρ g (ρ g v) - v = (ρ g (ρ g v) - ρ g v) + (ρ g v - v) := by abel
    _ = 0 := by rw [he, htwo]

/-- With a two-group representation kernel, the pointwise kernel on an
invariant self-perpendicular space is contained in the intrinsic two-core. -/
theorem pointwise_self_perp_le_pCore
    (ρ : Representation (ZMod 2) G V) (B : LinearMap.BilinForm (ZMod 2) V)
    (I : Submodule (ZMod 2) V) (hI : B.orthogonal I = I)
    (hB : ∀ g x y, B (ρ g x) (ρ g y) = B x y)
    (hs : ∀ g v, v ∈ I → ρ g v ∈ I) (hk : IsPGroup 2 ρ.ker)
    (g : G) (hg : ∀ v ∈ I, ρ g v = v) : g ∈ pCore 2 G := by
  let τ : Representation (ZMod 2) G I := {
    toFun := fun a => (ρ a).restrict (hs a)
    map_one' := by ext; simp
    map_mul' x y := by ext; simp }
  have hp : IsPGroup 2 τ.ker := by
    intro a
    have ha : ∀ v ∈ I, ρ a.val v = v := fun v hv =>
      congrArg Subtype.val (LinearMap.congr_fun a.property ⟨v, hv⟩)
    have ha2 : a.val ^ 2 ∈ ρ.ker :=
      square_fixes_of_fixes_self_perp ρ B I hI a.val (hB a.val) ha
    obtain ⟨n, hn⟩ := hk ⟨a.val ^ 2, ha2⟩
    refine ⟨n + 1, Subtype.ext ?_⟩
    have he : (a.val ^ 2) ^ (2 ^ n) = 1 := congrArg Subtype.val hn
    change a.val ^ (2 ^ (n + 1)) = 1
    rw [Nat.pow_succ', pow_mul]
    exact he
  have hle : τ.ker ≤ pCore 2 G := le_sSup ⟨inferInstance, hp⟩
  apply hle
  apply LinearMap.ext
  intro v
  exact Subtype.ext (hg v v.property)

end Representation.BinaryOffender
