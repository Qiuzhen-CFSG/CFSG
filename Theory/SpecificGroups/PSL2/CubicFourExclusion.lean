module

public import GorensteinWalter.PGL2KleinFourCentralizer
/-!
# No cubic times four-group in odd PGL₂

The images of the two product factors would give a Klein four centralizing
a nontrivial odd cyclic subgroup, contrary to the proved PGL₂ involution
centralizer calculation. This rules out the exceptional mixed vertex in
the odd-prime component argument of Aschbacher--Smith F.6.17, printed p.309.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2
local notation "Three" => Multiplicative (ZMod 3)
local notation "Four" => Multiplicative (ZMod 2) × Multiplicative (ZMod 2)
theorem no_injective_cubic_four_product {F : Type*} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (f : Three × Four →* PGL2 F) :
    ¬ Function.Injective f := by
  intro hf
  let a : Three →* PGL2 F := f.comp (MonoidHom.inl Three Four)
  let v : Four →* PGL2 F := f.comp (MonoidHom.inr Three Four)
  have ha : Function.Injective a := hf.comp (fun x y h => congrArg Prod.fst h)
  have hv : Function.Injective v := hf.comp (fun x y h => congrArg Prod.snd h)
  let ea := MonoidHom.ofInjective ha
  let ev := MonoidHom.ofInjective hv
  have hA : Nat.card a.range = 3 := by rw [← Nat.card_congr ea.toEquiv]; simp
  have hV : IsKleinFour v.range := {
    card_four := by rw [← Nat.card_congr ev.toEquiv]; simp
    exponent_two := by rw [← Monoid.exponent_eq_of_mulEquiv ev]; simp [Monoid.exponent_prod] }
  apply pgl2_no_kleinFour_centralizes_odd_cyclic F hF a.range v.range
    (isCyclic_of_prime_card hA) (by intro hb; simp [hb] at hA)
    (by rw [hA]; decide) hV
  rintro x ⟨x,rfl⟩ y ⟨y,rfl⟩
  change f (y,1) * f (1,x) = f (1,x) * f (y,1)
  rw [← map_mul,← map_mul]
  simp
end Theory.PSL2
