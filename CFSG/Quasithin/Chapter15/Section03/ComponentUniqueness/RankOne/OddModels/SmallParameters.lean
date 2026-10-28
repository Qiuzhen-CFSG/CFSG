module

public import Theory.SpecificGroups.SL2.PrimeFiveEquiv
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168

/-!
# Transport of the two small odd parameters

The existing actual comparisons PSL₂(5) ≃ PSL₂(4) and PSL₂(7) ≃ PSL₃(2)
are transported from any field of the given order and then composed with
the supplied component equivalence. This is the overlap used at the end
of Aschbacher--Smith 15.3.43, printed p.1140. The characteristic-two
exclusions must still be applied by the parent assembly.

The order-seven comparison is the checked ATLAS eight-point action
construction. Its source attribution and ATLAS Research and Attribution
License 1.0 notice are retained in the imported `Order168` development.
-/

@[expose] public section

open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.OddModels
variable {G : Type*} [Group G]

theorem linear_two_five_transport {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 5) (e : G ≃* PSL(2, F)) :
    Nonempty (G ≃* PSL(2, GaloisField 2 2)) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fintype F := Fintype.ofFinite F
  let f : F ≃+* ZMod 5 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  obtain ⟨e5⟩ := Matrix.ProjectiveSpecialLinearGroup.five_equiv_four
  exact ⟨e.trans ((Atlas.fieldEquivPSL 2 f).trans e5)⟩

theorem linear_two_seven_transport {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 7) (e : G ≃* PSL(2, F)) :
    Nonempty (G ≃* PSL(3, ZMod 2)) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : Fintype F := Fintype.ofFinite F
  let f : F ≃+* ZMod 7 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  exact ⟨e.trans ((Atlas.fieldEquivPSL 2 f).trans
    Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two)⟩
end CFSG.Quasithin.Chapter15.Section03.RankOne.OddModels
