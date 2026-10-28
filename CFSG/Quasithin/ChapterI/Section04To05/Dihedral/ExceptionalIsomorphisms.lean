module

public import GorensteinWalter.Classification
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360

/-!
# The exceptional linear models in I.4.1(2)

The two small odd-field cases in Aschbacher–Smith, *The Classification of
Quasithin Groups*, I.4.1(2), printed p. 415, are the actual matrix group PSL₃(2)
and the alternating group A₆. The imported ATLAS comparisons construct
multiplicative equivalences by identifying faithful actions: eight projective
points with eight Singer subgroups for PSL₂(7), and ten projective points
with complementary triples of six letters for PSL₂(9). Finite-field transport
makes these identifications independent of the chosen coefficient field.

The constructions are ported from Gerald Höhn and the ATLAS contributors,
revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`; the individual lower-layer
modules retain source attribution and the ATLAS Research and Attribution
License 1.0 notice. No order-based recognition assumption is used.
-/

namespace CFSG.Quasithin

/-- The seven-element-field case uses the concrete binary PSL₃ model. -/
public theorem psl2_equiv_psl3Two_of_card_seven
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 7) :
    Nonempty (GorensteinWalter.PSL2 F ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : Fintype F := Fintype.ofFinite F
  let e : F ≃+* ZMod 7 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  exact ⟨(Atlas.fieldEquivPSL 2 e).trans
    Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two⟩

/-- The nine-element-field case uses the concrete alternating group of degree six. -/
public theorem psl2_equiv_alternatingSix_of_card_nine
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 9) :
    Nonempty (GorensteinWalter.PSL2 F ≃* alternatingGroup (Fin 6)) :=
  ⟨Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 hF⟩

end CFSG.Quasithin
