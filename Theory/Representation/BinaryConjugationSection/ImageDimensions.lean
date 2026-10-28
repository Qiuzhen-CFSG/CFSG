module

public import Theory.Representation.BinaryConjugationSection.QuadraticPair
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Dimensions of literal section images and dual displacement

The original coordinate kernel computes subgroup image orders and image
codimension from relative indices. Fixation on a dual subspace forces
primal displacement into its annihilator, with the inverse actor retained.
These are the actual-section bridges for Aschbacher--Smith13.7.12(2), p.942.
-/

public section

open Subgroup
namespace Representation.BinaryConjugationSection
variable {G:Type*} [Group G] {H S E:Subgroup G}
  {W:Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ:Representation (ZMod 2) H W} (c:BinaryConjugationSection H S E ρ)
theorem imageSpace_card_eq_relIndex (B:Subgroup G) (hB:B≤S) :
    Nat.card (c.imageSpace B)=E.relIndex B := by
  change Nat.card ((B.subgroupOf S).map c.coordinates)=_
  rw [←relIndex_ker,c.kernel_eq]
  have he:=relIndex_map_map_of_injective (E.subgroupOf S) (B.subgroupOf S) S.subtype_injective
  rw [map_subgroupOf_eq_of_le c.kernel_le,map_subgroupOf_eq_of_le hB] at he
  exact he.symm

theorem imageSpace_finrank_of_index [Finite S] (B:Subgroup G) (hB:B≤S)
    (n:ℕ) (hi:E.relIndex B=2^n) : Module.finrank (ZMod 2) (c.imageSpace B)=n := by
  let :Finite W:=Finite.of_surjective (fun x:S=>(c.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  have he:=c.imageSpace_card_eq_relIndex B hB
  rw [hi,Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=c.imageSpace B),Nat.card_zmod] at he
  exact Nat.pow_right_injective (by decide : 1<2) he

theorem imageSpace_codimension_of_index [Finite S] (B:Subgroup G) (_hB:B≤S) (hEB:E≤B)
    (n:ℕ) (hi:B.relIndex S=2^n) :
    Module.finrank (ZMod 2) (c.imageSpace B)+n=Module.finrank (ZMod 2) W := by
  let :Finite W:=Finite.of_surjective (fun x:S=>(c.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  let D:Subgroup (Multiplicative W):=(B.subgroupOf S).map c.coordinates
  have hd:D.index=2^n := by
    rw [index_map_eq _ c.onto (by rw [c.kernel_eq];exact comap_mono hEB)]
    exact hi
  have hc:=D.card_mul_index
  rw [hd] at hc
  change Nat.card (c.imageSpace B)*2^n=Nat.card W at hc
  rw [Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=c.imageSpace B),
    Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=W),Nat.card_zmod,←pow_add] at hc
  exact Nat.pow_right_injective (by decide : 1<2) hc
end Representation.BinaryConjugationSection

namespace Representation
variable {G:Type*} [Group G] {W:Type*} [AddCommGroup W] [Module (ZMod 2) W]
theorem displacement_le_coannihilator_of_dual_fixed (ρ:Representation (ZMod 2) G W)
    (a:G) (P:Submodule (ZMod 2) (Module.Dual (ZMod 2) W))
    (hf:∀φ∈P,ρ.dual a⁻¹ φ=φ) :
    LinearMap.range (ρ a-1)≤P.dualCoannihilator := by
  rintro _ ⟨v,rfl⟩
  rw [Submodule.mem_dualCoannihilator]
  intro φ hφ
  have he:=congrArg (fun f:Module.Dual (ZMod 2) W=>f v) (hf φ hφ)
  change φ (ρ a⁻¹⁻¹ v)=φ v at he
  rw [inv_inv] at he
  change φ (ρ a v-v)=0
  rw [map_sub,he,sub_self]
end Representation
