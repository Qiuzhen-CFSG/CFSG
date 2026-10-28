module

public import Theory.Representation.HexacodeAction.Field
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# The marked central character of the triple cover of A₆

The central generator of the hexacode cover identifies its center with F₄ˣ,
with that same generator sent to omega. A representation on which the generator
acts as omega therefore has the specified scalar action on the entire center.
Every nontrivial normal subgroup of this quasisimple group contains its
prime-order center, so a homomorphism moving the center is faithful.

These are the central-character and faithfulness steps for the actual maximal
quotient in Aschbacher–Smith 13.8.30, printed p.964. The imported concrete
hexacode model retains its ATLAS source attribution and license.
-/

public section

open Subgroup Atlas.Codes
namespace Representation.Hexacode
noncomputable section

private def omegaUnit : Fˣ := Units.mk0 omega (by decide)

private theorem omegaUnit_order : orderOf omegaUnit = 3 := by
  apply orderOf_eq_prime
  · apply Units.ext
    change omega ^ 3 = 1
    decide
  · intro h
    have hh := congrArg Units.val h
    exact (by decide : omega ≠ 1) hh

private theorem omegaUnit_generates : zpowers omegaUnit = ⊤ := by
  apply zpowers_eq_top_of_prime_card (p := 3)
  · rw [Nat.card_units, Nat.card_eq_fintype_card, field_card]
  · intro h
    have hh := omegaUnit_order
    rw [h, orderOf_one] at hh
    contradiction

private def centerGenerator : center HexEvenAutomorphisms :=
  ⟨hexEvenZ, by rw [← even_kernel_eq_center, hexEvenCoordinate_kernel]; exact mem_zpowers _⟩

private theorem centerGenerator_order : orderOf centerGenerator = 3 := by
  rw [centerGenerator, Subgroup.orderOf_mk, hexEvenZ_order]

private theorem centerGenerator_generates : ∀ z, z ∈ zpowers centerGenerator := by
  have he : zpowers centerGenerator = ⊤ := zpowers_eq_top_of_prime_card even_center_card
    (by intro h; have hh := centerGenerator_order; rw [h, orderOf_one] at hh; contradiction)
  intro z
  rw [he]
  trivial

/-- The marked central cubic identifies the center with the scalar group of F₄. -/
def centerCharacter : center HexEvenAutomorphisms ≃* Fˣ :=
  mulEquivOfOrderOfEq centerGenerator_generates
    (fun a => omegaUnit_generates ▸ mem_top a)
    (centerGenerator_order.trans omegaUnit_order.symm)

private theorem centerCharacter_pow (n : ℕ) :
    (centerCharacter (centerGenerator ^ n) : F) = omega ^ n := by
  rw [map_pow]
  have hg : centerCharacter centerGenerator = omegaUnit :=
    mulEquivOfOrderOfEq_apply_gen _ _ _
  rw [hg]
  rfl

/-- Every central element acts by its marked field scalar. -/
theorem centerCharacter_action
    {W : Type*} [AddCommGroup W] [Module F W]
    (σ : Representation F HexEvenAutomorphisms W)
    (hs : ∀ w, σ hexEvenZ w = omega • w)
    (z : center HexEvenAutomorphisms) (w : W) :
    σ z.val w = (centerCharacter z : F) • w := by
  have hp (n : ℕ) (v : W) : σ (hexEvenZ ^ n) v = omega ^ n • v := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, map_mul, Module.End.mul_apply, hs, map_smul, ih,
        smul_smul, mul_comm, ← pow_succ]
  have hz : z.val ∈ zpowers hexEvenZ := by
    rw [← hexEvenCoordinate_kernel, even_kernel_eq_center]
    exact z.property
  obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers.mpr hz)
  have he : z = centerGenerator ^ n := Subtype.ext hn.symm
  rw [he, centerCharacter_pow]
  exact hp n w

end
end Representation.Hexacode

open Theory.GroupTheory

namespace Representation.Hexacode

/-- Nontrivial action on the center forces faithfulness of the actual map. -/
theorem faithful_of_center_not_le_ker
    {M : Type*} [Monoid M] (f : HexEvenAutomorphisms →* M)
    (hn : ¬ center HexEvenAutomorphisms ≤ f.ker) : Function.Injective f := by
  let _ := even_isQuasisimple
  apply (MonoidHom.ker_eq_bot_iff f).mp
  rcases IsQuasisimple.normal_le_center_or_eq_top f.ker with hk | hk
  · let : Fact (Nat.card (center HexEvenAutomorphisms)).Prime :=
      ⟨by rw [even_center_card]; decide⟩
    rcases (f.ker.subgroupOf (center HexEvenAutomorphisms)).eq_bot_or_eq_top_of_prime_card
      with hb | ht
    · have he := congrArg (fun D => D.map (center HexEvenAutomorphisms).subtype) hb
      simpa only [map_subgroupOf_eq_of_le hk, Subgroup.map_bot] using he
    · exact (hn (subgroupOf_eq_top.mp ht)).elim
  · exact (hn (hk ▸ le_top)).elim

end Representation.Hexacode
