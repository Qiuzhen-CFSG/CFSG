module
public import Theory.LinearAlgebra.BinaryFourPointStabilizer
public import Theory.ElementaryAbelian.Injective
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Theory.GroupTheory.PCoreLocalSetup
/-! A self-centralizing elementary sixteen-group with a fixed nonidentity
point bounds its normalizing centralizer by the full binary-four point stabilizer. -/
public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
theorem card_le_of_elementary_sixteen_fixed_point (H A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : Nat.card A=16) (hAH : A≤H) (hHN : H≤normalizer (A : Set G))
    (z : G) (hz : z∈A) (hne : z≠1) (hHz : H≤centralizer ({z} : Set G))
    (hself : H⊓centralizer (A : Set G)≤A) : Nat.card H≤21504 := by
  let autLinear : MulAut A ≃* (Additive A ≃ₗ[ZMod 2] Additive A) :=
    { toFun := fun aut => { aut.toAdditive with map_smul' := ZMod.map_smul aut.toAdditive }
      invFun := fun aut => MulEquiv.toAdditive.symm aut.toAddEquiv
      left_inv := by intro aut; ext; rfl
      right_inv := by intro aut; ext; rfl
      map_mul' := by intro aut other; ext; rfl }
  let : Finite (Additive A ≃ₗ[ZMod 2] Additive A) :=
    Finite.of_injective (fun b : Additive A ≃ₗ[ZMod 2] Additive A => (b : Additive A → Additive A)) DFunLike.coe_injective
  let f := autLinear.toMonoidHom.comp (A.normalizerMonoidHom.comp (inclusion hHN))
  let v : Additive A := Additive.ofMul ⟨z,hz⟩
  let S := Theory.LinearAlgebra.BinaryFivePointStabilizer.stabilizer v
  have hdim : Module.finrank (ZMod 2) (Additive A)=4 := by
    have hh := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive A)
    change Nat.card A=_ at hh
    rw [hA,Nat.card_zmod] at hh
    exact Nat.pow_right_injective (by decide : 1<2) hh.symm
  have hv : v≠0 := fun he => hne (congrArg (fun w : Additive A => (w.toMul:G)) he)
  have hS : Nat.card S=1344 := Theory.LinearAlgebra.BinaryFourPointStabilizer.card_stabilizer v hv hdim
  have hfixed : f.range≤S := by
    rintro _ ⟨g,rfl⟩
    change f g v=v
    apply Additive.toMul.injective
    apply Subtype.ext
    change (g:G)*z*(g:G)⁻¹=z
    rw [mem_centralizer_singleton_iff.mp (hHz g.property),mul_inv_cancel_right]
  have hker : f.ker≤A.subgroupOf H := by
    intro g hg
    have hf : f g=1 := hg
    have hact : A.normalizerMonoidHom (inclusion hHN g)=1 := by
      apply autLinear.injective
      exact hf.trans autLinear.map_one.symm
    apply hself
    refine ⟨g.property,?_⟩
    intro a ha
    have hh := congrArg (fun b : MulAut A => (b ⟨a,ha⟩:G)) hact
    change (g:G)*a*(g:G)⁻¹=a at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hkcard : Nat.card f.ker≤16 :=
    (card_le_of_le hker).trans_eq ((Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv).trans hA)
  have hrcard : Nat.card f.range≤1344 := (card_le_of_le hfixed).trans_eq hS
  have hh := f.ker.card_mul_index
  rw [index_ker] at hh
  nlinarith

/-- A contained subgroup of the maximum order is the entire group. -/
theorem eq_of_card_elementary_sixteen_fixed_point
    (Y H A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : Nat.card A=16) (hAH : A≤H) (hHN : H≤normalizer (A : Set G))
    (z : G) (hz : z∈A) (hne : z≠1) (hHz : H≤centralizer ({z} : Set G))
    (hself : H⊓centralizer (A : Set G)≤A)
    (hYH : Y≤H) (hY : Nat.card Y=21504) : Y=H := by
  apply eq_of_le_of_card_ge hYH
  rw [hY]
  exact card_le_of_elementary_sixteen_fixed_point H A hA hAH hHN z hz hne hHz hself

end Theory.GroupTheory
