module

public import Theory.Representation.SL2.EightRegularKernelSplitting

/-!
# Regular coordinates on each actual eight-element root image

The actual irreducible binary degree-eight action has a one-dimensional
fixed space on every two-subgroup of order eight. The p-group coordinate
theorem gives regular coordinates on that very subgroup, without changing
its embedding or choosing standard upper-root coordinates.
-/

public noncomputable section
open Module Subgroup
open scoped MatrixGroups
namespace Representation.SL2.BinarySmall
open Representation.BinaryOffender

/-- Each specified eight-element two-subgroup has regular coordinates for
the original representation and its literal subgroup inclusion. -/
theorem eight_irreducible_root_regular
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2,GaloisField 2 3) V) [ρ.IsIrreducible]
    (hd : finrank (ZMod 2) V=8)
    (R : Subgroup SL(2,GaloisField 2 3)) (hR : IsPGroup 2 R) (hc : Nat.card R=8) :
    ∃ e : V ≃ₗ[ZMod 2] (R → ZMod 2),
      ∀ (g : R) v x, e (ρ g v) x=e v (g⁻¹*x) := by
  classical
  let : Fintype R := Fintype.ofFinite _
  have hfix := TripleFixedSpaces.binary_fixed_mul_card
    (GaloisField.card 2 3 (by decide)) ρ (eight_irreducible_isTriple ρ hd) R hR
  rw [hc] at hfix
  have hf : finrank (ZMod 2) (fixedSpace ρ R)=1 := by omega
  obtain ⟨z,hz,hspan⟩ := finrank_eq_one_iff'.mp hf
  apply Representation.TwistedRegular.exists_regular_coordinates (ρ.comp R.subtype)
    (by rw [ringChar.eq (ZMod 2) 2]; decide)
    (by rwa [ringChar.eq (ZMod 2) 2]) (z:V)
    (fun h => hz (Subtype.ext h))
  · intro v hv
    obtain ⟨c,hc⟩ := hspan (⟨v,hv⟩ : fixedSpace ρ R)
    exact ⟨c,(congrArg Subtype.val hc).symm⟩
  · rw [hd,←Nat.card_eq_fintype_card,hc]

end Representation.SL2.BinarySmall
