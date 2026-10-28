module

public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder

/-!
# The three-free outer quotient of binary SL₃

For every two-element field F, entrywise field transport identifies the actual
matrix group SL₃(F) with SL₃(ZMod 2). Transport of Aut/Inn then gives outer
order two from `Automorphisms.card_outer_sl`, hence an order prime to three.
The latter order calculation uses the proved exceptional isomorphism with
PSL₂(7), full automorphism coverage there, and the actual inner subgroup.

This is the binary endpoint of the SL₃(2ⁿ) alternative in Aschbacher–Smith,
*The Classification of Quasithin Groups*, combined manuscript (1 March 2004),
B.4.2(2), printed p.86, used in the componentwise inner-action argument in
15.3.49(k), printed p.1144. The surrounding component-product assembly is
separate from this intrinsic group fact.

The reused entrywise transport and exceptional isomorphism are attributed
ATLAS ports in `Theory.AtlasPort.ExceptionalIsomorphisms.Support` and
`Order168`; their attribution and ATLAS Research and Attribution License 1.0
notices remain in those modules.
-/

public section

namespace Matrix.PSL3Two

/-- Over every two-element field, the actual outer quotient of SL₃ has order two. -/
theorem card_outer_of_card_two {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2) :
    Nat.card (MulAut.Outer (SpecialLinearGroup (Fin 3) F)) = 2 := by
  let _ := Fintype.ofFinite F
  let e : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  rw [Nat.card_congr (MulAut.outerCongr (Atlas.fieldEquivSL 3 e)).toEquiv]
  exact Automorphisms.card_outer_sl

/-- The SL₃(2) component has outer order prime to three, with any field marking. -/
theorem outer_three_free_of_card_two {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2) :
    ¬ 3 ∣ Nat.card (MulAut.Outer (SpecialLinearGroup (Fin 3) F)) := by
  rw [card_outer_of_card_two hF]
  decide

end Matrix.PSL3Two
