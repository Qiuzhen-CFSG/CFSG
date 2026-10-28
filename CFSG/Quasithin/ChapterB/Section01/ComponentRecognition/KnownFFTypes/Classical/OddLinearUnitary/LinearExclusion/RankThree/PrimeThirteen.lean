module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.SourceBounds
public import Theory.Representation.BinaryPrimeDegree
public import Theory.SpecificGroups.PSL3Three.Cardinality
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The order-thirteen lower bound for the actual PSL₃(3) quotient

Transport the three-element coefficient field to ZMod 3 and use the actual
matrix group order 5616. Its prime divisor thirteen divides the orders of the
central cover and the ambient group. Since the order of two modulo thirteen
is twelve, a faithful binary representation has degree at least twelve.
No assertion about the Schur multiplier or the module catalogue is needed.

The lower bound is consumed in the rank-three source assembly, and with
`degree_twelve_of_rank_two_actor` already determines the degree
for rank-two actors once three-conjugate generation is established.

Source: Aschbacher--Smith G.7.1(1), printed p.347, and K.2, printed p.453;
Guralnick--Malle, Classification of 2F-modules I, Proposition 4.2, pp.9--10.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)
include h

/-- Central covers of an actual PSL₃(3) quotient retain the degree-twelve lower bound. -/
theorem source_degree_at_least_twelve
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 3 3) :
    12 ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨F, hF, hfin, hc, ⟨f⟩⟩ := hm
  let := Fintype.ofFinite F
  let e : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hc)
  have hcard : Nat.card ((generalizedFitting G) ⧸ center (generalizedFitting G)) = 5616 :=
    (Nat.card_congr (f.trans (Atlas.fieldEquivPSL 3 e)).toEquiv).trans
      Matrix.PSL3Three.card_PSL
  have hdiv : 13 ∣ Nat.card G := by
    apply dvd_trans (show 13 ∣ Nat.card
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) by rw [hcard]; decide)
    exact (center (generalizedFitting G)).card_quotient_dvd_card.trans
      (generalizedFitting G).card_subgroup_dvd_card
  simpa only [BinaryPrimeDegree.orderOf_two_mod_thirteen] using
    BinaryPrimeDegree.orderOf_le_finrank ρ h.faithful (by decide : Nat.Prime 13)
      (by decide : 13 ≠ 2) hdiv
end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree
