module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.Alternating
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# The PSL₄(2) branch of the seven-component inspection

Transport the supplied finite field of order two to `ZMod 2`, then use the
actual exterior-square/deleted-module isomorphism PSL₄(2) ≃ A₈. The proved
alternating inspection handles the full two-subgroup of automorphisms and
both seven-component models. No identification from equal orders is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.18,
printed p.252, and Theorem C(4), printed p.33.
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie

/-- The dimension-four binary constructor is the actual alternating-eight case. -/
theorem binary_four {S : Type*} [Group S] [Finite S]
    (h : ClassicalGroup.IsPSL S 4 2) : SevenActionInspection S := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let _ : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  let a := (e.trans (Atlas.fieldEquivPSL 4 eF)).trans
    Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
  exact sevenActionInspection_of_isAlternating ⟨a⟩ (by decide : 8 ≤ 8)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie
