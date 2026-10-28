module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.CartanAction

/-!
# A fixed supplement to the diagonal cubic in a paired torus

If a factor-permuting automorphism inverts a diagonal cubic P and fixes
a supplement D, every displacement lies in P. Factor preservation would
put each axis displacement in P's trivial intersection with that axis,
forcing the whole automorphism to be the identity. Hence the automorphism
exchanges factors. The surjective displacement projection then bounds
each factor's order by three. No order-two hypothesis on the automorphism,
field automorphism classification or second marking is required.

Source application: Aschbacher–Smith, proof of 14.7.32, printed p.1056,
refs/quasithin.pdf. BinaryTorus constructs this supplement and the actual
inverter on the original Borel quotient.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.CartanAction
variable {C : Type*} [CommGroup C] [Finite C]

/-- A fixed supplement to a cubic diagonal bounds the full displacement,
forcing any factor-permuting inverter to exchange factors of order at most three. -/
theorem exchanges_and_card_le_of_fixed_supplement
    (α : MulAut (C × C)) (P D : Subgroup (C × C))
    (hP : Nat.card P = 3)
    (hfst : Function.Injective (fun x : P => (x : C × C).1))
    (hsnd : Function.Injective (fun x : P => (x : C × C).2))
    (hgen : P ⊔ D = ⊤) (hfix : ∀ d ∈ D, α d = d)
    (hinv : ∀ p ∈ P, α p = p⁻¹)
    (hperm : PreservesFactors α ∨ ExchangesFactors α) :
    ExchangesFactors α ∧ Nat.card C ≤ 3 := by
  let δ : (C × C) →* C × C := α.toMonoidHom * (MonoidHom.id _ )⁻¹
  have hδ (x : C × C) : δ x = α x * x⁻¹ := rfl
  have hle : δ.range ≤ P := by
    rintro _ ⟨x,rfl⟩
    have hx : x ∈ P ⊔ D := hgen ▸ mem_top x
    obtain ⟨p,hp,d,hd,rfl⟩ := mem_sup_of_normal_right.mp hx
    rw [map_mul,hδ,hδ,hinv p hp,hfix d hd,mul_inv_cancel,mul_one]
    exact P.mul_mem (P.inv_mem hp) (P.inv_mem hp)
  have hdis : displacement α ≤ P := by
    rw [displacement,closure_le]
    rintro _ ⟨x,rfl⟩
    exact hle ⟨x,rfl⟩
  have hex : ExchangesFactors α := by
    rcases hperm with hp | he
    · exfalso
      have hleft (x : C) : α (x,1) = (x,1) := by
        have hm : α (x,1) * (x,1)⁻¹ ∈ P := hdis (displacement_mem α _)
        have hy : (α (x,1)).2 = 1 := (mem_firstFactor _).mp
          (hp.1.le (mem_map_of_mem α.toMonoidHom (by simp)))
        have hz : (⟨α (x,1) * (x,1)⁻¹,hm⟩ : P) = 1 := hsnd (by simp [hy])
        exact mul_inv_eq_one.mp (congrArg Subtype.val hz)
      have hright (x : C) : α (1,x) = (1,x) := by
        have hm : α (1,x) * (1,x)⁻¹ ∈ P := hdis (displacement_mem α _)
        have hy : (α (1,x)).1 = 1 := (mem_secondFactor _).mp
          (hp.2.le (mem_map_of_mem α.toMonoidHom (by simp)))
        have hz : (⟨α (1,x) * (1,x)⁻¹,hm⟩ : P) = 1 := hfst (by simp [hy])
        exact mul_inv_eq_one.mp (congrArg Subtype.val hz)
      have hall (x : C × C) : α x = x := by
        have he : x = (x.1,1) * (1,x.2) := by ext <;> simp
        conv_lhs => rw [he,map_mul,hleft,hright]
        exact he.symm
      have hbot : P = ⊥ := eq_bot_iff.mpr fun x hx => by
        have htwo : x ^ 2 = 1 := by
          calc
            x ^ 2 = α x * x := by rw [hall x,pow_two]
            _ = 1 := by rw [hinv x hx,inv_mul_cancel]
        have hthree : x ^ 3 = 1 := by
          have hh := pow_card_eq_one' (x := (⟨x,hx⟩ : P))
          rw [hP] at hh
          exact congrArg Subtype.val hh
        simpa [pow_succ,htwo] using hthree
      have hh := P.eq_bot_iff_card.mp hbot
      omega
    · exact he
  exact ⟨hex,(Nat.card_le_card_of_surjective _ (fst_displacement_surjective α hex)).trans
    ((Nat.card_le_card_of_injective _ (inclusion_injective hdis)).trans_eq hP)⟩
end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.CartanAction
