module
public import Theory.GroupAction.CommutingIrreducibleSupports
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.RepresentationTheory.Irreducible

/-!
# The order of an abelian irreducible binary action

An abelian group commutes with its own image. An element of the faithful
image fixing a nonzero vector fixes the entire irreducible module, so the
image acts freely away from zero. Its order therefore divides the number
of nonzero vectors. This supplies the full Cartan-image bound in the
linear/unitary octagon argument of Fong--Seitz I (6F), pp.45--46.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupAction

theorem abelian_irreducible_image_card_dvd
    {H A : Type*} [Group H] [IsMulCommutative H] [Finite H]
    [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (ρ : H →* MulAut A)
    (τ : Representation (ZMod 2) H (Additive A))
    (heq : ∀ h a, τ h (Additive.ofMul a) = Additive.ofMul (ρ h a))
    [τ.IsIrreducible] : Nat.card ρ.range ∣ Nat.card A - 1 := by
  let actH : MulDistribMulAction H A := MulDistribMulAction.compHom A ρ
  let actR : MulDistribMulAction ρ.range A := MulDistribMulAction.compHom A ρ.range.subtype
  let faithfulR : FaithfulSMul ρ.range A := ⟨fun {a b} hab => Subtype.ext (MulEquiv.ext hab)⟩
  apply @ActionSupport.card_dvd_card_sub_one_of_commuting_irreducible
    H ρ.range A _ _ _ _ _ actH actR faithfulR
  · intro h a x
    obtain ⟨k,hk⟩ := a.property
    change ρ h (a.val x) = a.val (ρ h x)
    rw [←hk]
    have he : ρ h * ρ k = ρ k * ρ h := by rw [←map_mul,←map_mul,mul_comm h k]
    exact DFunLike.congr_fun he x
  · intro D hD
    let W : Subrepresentation τ := {
      toSubmodule := AddSubgroup.toZModSubmodule 2 D.toAddSubgroup
      apply_mem_toSubmodule := by
        intro h x hx
        change (τ h x).toMul ∈ D
        rw [show x = Additive.ofMul x.toMul from rfl,heq]
        exact (hD.invariant h x.toMul).mp hx }
    rcases (inferInstance : τ.IsIrreducible).eq_bot_or_eq_top W with hb | ht
    · left
      apply bot_unique
      intro x hx
      have hm : Additive.ofMul x ∈ W := hx
      rw [hb] at hm
      exact hm
    · right
      apply top_unique
      intro x hx
      have hm : Additive.ofMul x ∈ W := ht ▸ Submodule.mem_top
      exact hm

end Theory.GroupAction
