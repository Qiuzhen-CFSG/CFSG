module
public import Theory.Representation.SmallBinaryOddResidual
public import Theory.GroupTheory.CyclicFifteen
/-!
# Cyclic residuals of faithful binary four-dimensional groups with normal five

The two-residual centralizes the normal subgroup of order five, since its
automorphism group has order four. Faithfulness on the sixteen-element module
bounds this centralizer's order by fifteen. All groups of order dividing
fifteen are cyclic, hence so is the two-residual.

Source application: the marked five case of Aschbacher--Smith15.2.3(2),
printed p.1105; this avoids the exceptional factorization subcase.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace Representation.SmallBinaryCyclicResidual
private theorem cyclic_card_dvd_fifteen {D : Type*} [Group D] [Finite D]
    (hc : Nat.card D ∣ 15) : IsCyclic D := by
  have hh : Nat.card D = 1 ∨ Nat.card D = 3 ∨ Nat.card D = 5 ∨ Nat.card D = 15 := by
    have := (Nat.mem_divisors (m := 15) (n := Nat.card D)).mpr ⟨hc,by decide⟩
    rw [show Nat.divisors 15 = {1,3,5,15} by decide] at this
    simpa using this
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  rcases hh with h | h | h | h
  · let : Subsingleton D := (Nat.card_eq_one_iff_unique.mp h).1
    infer_instance
  · exact isCyclic_of_prime_card h
  · exact isCyclic_of_prime_card h
  · exact isCyclic_of_card_eq_fifteen h

theorem cyclic_twoResidual_of_normal_five {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) V = 4)
    (P : Subgroup G) [P.Normal] (hP : Nat.card P = 5) :
    IsCyclic (pResidual 2 G) := by
  let := BinaryGroupAction.action ρ
  let := BinaryGroupAction.elementary (V := V)
  let := BinaryGroupAction.faithful ρ hf
  let : Finite V := Module.finite_of_finite (ZMod 2)
  have hV : Nat.card (Multiplicative V) = 16 := by
    change Nat.card V = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hdim]
    rfl
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : IsCyclic P := isCyclic_of_prime_card hP
  have hAut : IsPGroup 2 (MulAut P) := IsPGroup.of_card (n := 2) (by
    rw [IsCyclic.card_mulAut,hP]
    decide)
  have hle : pResidual 2 G ≤ centralizer (P : Set G) := by
    rw [← MulAut.conjNormal_ker_eq_centralizer P]
    exact pResidual_le_ker_of_isPGroup 2 (MulAut.conjNormal : G →* MulAut P) hAut
  exact cyclic_card_dvd_fifteen ((card_dvd_of_le hle).trans
    (card_centralizer_five_dvd_fifteen (V := Multiplicative V) P hP hV))

end Representation.SmallBinaryCyclicResidual
