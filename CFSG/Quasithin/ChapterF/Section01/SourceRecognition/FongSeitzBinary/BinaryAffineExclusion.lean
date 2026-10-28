module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.AffineExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.BinaryAffineCentralizer

/-!
# Excluding the binary affine endpoint on the marked source hexagon

The original nonbinary linear factor supplies the faithful local PSL2
marking and its canonical remainder containment. The global fixed-section
argument then excludes the order-144 affine alternative at the other
endpoint. The literal Chapter 12 application consequently proves (2B) at
both endpoints and identifies both original remainder preimages with the
original two-cores. The full amalgam marking, its full Borel and both
endpoint inclusion squares are retained in the input isomorphism.

Source: Fong--Seitz I (5I), pp.31--34, specialized to the split binary
hexagon with a nonbinary linear endpoint; DGS Theorem D, p.224;
Aschbacher--Smith F.1.1--3 and 12.2.2. Rotation order six and the earlier
marked split quotient still come from the independent apartment/exchange
and source-profile producers. The other even branches, minimality and
exhaustive seven-row recognition remain with source assembly.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include e h in
/-- The original linear factor excludes the affine hexagon alternative,
without perfectness or (2B) at the opposite endpoint. -/
theorem binary_affine_hexagon_false_of_linear
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hperfect : Group.IsPerfect (L i))
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
    (hx : BinaryUnitaryException Q split j) : False := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  exact no_affine_hexagon_of_linear Q split hF hm i j hij
    (linear_remainder_le_kernel Q e h split i T hT μ)
    (linearLocalEquiv Q e h split i hperfect T hT μ)
    (UnitarySource.actorReflection Q split i) hx.1 hx.2.1 hx.2.2.1

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- Both canonical remainders of the literal Chapter 12 hexagon are the
actual original two-cores. The affine alternative has been discharged. -/
theorem rankOne_global_hexagon_regularity
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : rotationOrder Q = 6) :
    ∀ i : Fin 2, simpleRemainder Q split i ≤ localKernel Q i ∧
      (simpleRemainder Q split i).comap (MarkedLocal.endpointMap Q e i) =
        pCore 2 (parabolic ![L,R] (Global.sourceS L H) i) := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  let hf := d.hypothesisF11 hi hTH
  rcases D.rankOne_global_regularity_or_even_affine_cartan h hmany hn hpsl d hTH Q e split with hr | hx
  · exact hr
  · obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hpsl
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    have hF2 : 2 < Nat.card F := by
      rw [hcard]
      exact (by decide : 2 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) hn)
    exact (MarkedLocal.binary_affine_hexagon_false_of_linear Q e hf split hF2 hm 0 1
      (by decide) (Chapter1.mem_L_isPerfect hi.local_mem.1.1) μ hx.1).elim

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
