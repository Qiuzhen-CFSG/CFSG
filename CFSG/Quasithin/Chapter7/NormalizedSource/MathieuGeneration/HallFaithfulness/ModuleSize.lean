module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSource
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M22.Properties.Order
public import Theory.Mathieu.M24.Properties.Order
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Prime.Factorial

/-!
# The size bound needed for the Mathieu odd-core argument

Each of the four actual Mathieu central quotients has order divisible by
11. A faithful action on the original orbit space embeds its component in
the permutation group on that space, so the space has at least 11 elements.
The original subgroup coordinates transfer this bound to V when V is its
T-orbit. This supplies precisely the greater-than-eight hypothesis of the
odd-core argument, without a module classification or a center-free cover.

Consumer: `MathieuGeneration.HallFaithfulness`, the Mathieu instance of
Aschbacher--Smith 4.4.8, printed p.620 (1 March 2004 manuscript).
-/

public noncomputable section
open scoped IsMulCommutative

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

private theorem eleven_dvd_mathieu {X : Type*} [Group X] [Finite X]
    (hm : HasMathieuCentralQuotient X) : 11 ∣ Nat.card X := by
  have hq : 11 ∣ Nat.card (X ⧸ center X) := by
    rcases hm with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · rw [Nat.card_congr e.toEquiv, Sporadic.Mathieu.m12_order]; norm_num
    · rw [Nat.card_congr e.toEquiv, Sporadic.Mathieu.m22_order]; norm_num
    · rw [Nat.card_congr e.toEquiv, Sporadic.Mathieu.m23_order]; norm_num
    · rw [Nat.card_congr e.toEquiv, Sporadic.Mathieu.m24_order]; norm_num
  exact hq.trans (card_quotient_dvd_card (center X))

private theorem prime_le_card_of_faithful_representation
    {X E : Type*} [Group X] [Finite X] [AddCommGroup E] [Module (ZMod 2) E]
    [Finite E] (ρ : Representation (ZMod 2) X E) (hf : Function.Injective ρ)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ Nat.card X) : p ≤ Nat.card E := by
  let τ : X →* Equiv.Perm E :=
    { toFun := fun g =>
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) E
          (ρ.asGroupHom g)).toEquiv
      map_one' := by ext v; simp
      map_mul' := by intro g h; ext v; simp }
  have hi : Function.Injective τ := by
    intro a b hab
    apply hf
    ext v
    exact congrArg (fun e : Equiv.Perm E => e v) hab
  have hdiv := hd.trans (card_dvd_of_injective τ hi)
  rw [Nat.card_perm] at hdiv
  exact hp.dvd_factorial.mp hdiv

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual faithful orbit action and its Mathieu central quotient force
the chosen invariant module to have more than eight elements. -/
theorem sourceOrbit_mathieu_card_gt_eight
    (hVW : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent) : 8 < Nat.card V := by
  have hf : Function.Injective (D.orbitRepresentation.comp D.orbitComponent.subtype) :=
    (subspaceImageRepresentation_injective _ _).comp D.orbitComponent.subtype_injective
  have he := prime_le_card_of_faithful_representation
    (D.orbitRepresentation.comp D.orbitComponent.subtype) hf Nat.prime_eleven
    (eleven_dvd_mathieu hm)
  have hc : Nat.card D.orbitSpace = Nat.card V := by
    exact (Nat.card_congr D.sourceOrbitCoordinates.toEquiv).trans
      (congrArg (fun W : Subgroup G => Nat.card W) hVW.symm)
  rw [hc] at he
  omega

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
