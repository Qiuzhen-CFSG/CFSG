module
public import Theory.Representation.InvolutiveRank
public import Theory.AtlasPort.LinearGroups.G2.Basic

/-!
# A two-rank bound for odd-characteristic G₂

The actual split-octonion automorphism group acts faithfully on its
eight-dimensional algebra and fixes its nonzero unit. Simultaneous sign
characters therefore give two-rank at most seven. This deliberately weak bound
suffices for the rank-eight exclusion in Aschbacher–Smith 4.4.3, printed p.622.
-/

public section
namespace Atlas.G2
variable {F : Type*} [Field F] [Finite F]

/-- The fixed octonion unit removes one of the eight possible sign coordinates. -/
theorem odd_twoRank_le_seven (h2 : (2 : F) ≠ 0) : primeRank 2 (Model F) ≤ 7 := by
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro A hA
  let : IsElementaryAbelian 2 A := hA
  let ρ : Representation F A (Atlas.SplitOctonion.Carrier F) :=
    { toFun := fun a => (representation F a.val).toLinearMap
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hρ : Function.Injective ρ := by
    intro a b hab
    apply Subtype.ext
    apply representation_injective F
    exact LinearEquiv.toLinearMap_injective hab
  have hbound := Representation.elementary_card_le_pow_finrank_sub_one_of_fixed
    ρ hρ h2 Atlas.SplitOctonion.unit Atlas.SplitOctonion.unit_ne_zero
    (fun a => Atlas.SplitOctonion.automorphism_unit a.val)
  simpa only [carrier_finrank, Nat.reduceSub] using hbound
end Atlas.G2
