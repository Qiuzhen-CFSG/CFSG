module

public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.ClassificationModels.RankTwo

/-!
# The complete even-characteristic input for A.2.18

Every alternative contains the actual model and the same parameter restrictions
as the full known-simple catalogue. There is no upper rank restriction. The
unitary and twisted parameters are fixed-field orders. The small derived
carriers are retained literally, including the Ree endpoint whose comparison
with a binary linear group must be proved when it is used.

This is an input predicate, not a family elimination theorem.
Source: Aschbacher--Smith A.2.18, printed p.40; GLS3, Theorem 2.2.7.
-/

@[expose] public section
universe u v
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie
open KnownSimple ClassificationModels

inductive IsEvenLieCarrier (G : Type u) [Group G] : Prop
  | linear (d a : ℕ) (ha : 0 < a) (parameters : LinearParameters d (2 ^ a))
      (iso : ClassicalGroup.IsPSL G d (2 ^ a))
  | unitary (d a : ℕ) (ha : 0 < a) (parameters : UnitaryParameters d (2 ^ a))
      (iso : ClassicalGroup.IsPSU G d (2 ^ a))
  | symplectic (r a : ℕ) (ha : 0 < a) (parameters : SymplecticParameters r (2 ^ a))
      (iso : ClassicalGroup.IsPSp G r (2 ^ a))
  | orthogonalPlus (r a : ℕ) (ha : 0 < a)
      (parameters : OrthogonalPlusParameters r (2 ^ a))
      (iso : ClassicalGroup.IsPOmegaPlus G r (2 ^ a))
  | orthogonalOdd (r a : ℕ) (ha : 0 < a)
      (parameters : OrthogonalOddParameters r (2 ^ a))
      (iso : ClassicalGroup.IsPOmegaOdd G r (2 ^ a))
  | orthogonalMinus (r a : ℕ) (ha : 0 < a)
      (parameters : OrthogonalMinusParameters r (2 ^ a))
      (iso : ClassicalGroup.IsPOmegaMinus G r (2 ^ a))
  | g2 (a : ℕ) (ha : 2 ≤ a) (iso : IsG2At G (2 ^ a))
  | suzuki (m : ℕ) (hm : 1 ≤ m)
      (iso : Nonempty (G ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
  | triality (a : ℕ) (ha : 0 < a)
      (iso : Triality.Standard.IsTrialityGroupAt (2 ^ a) G)
  | reeF4 (m : ℕ) (hm : 1 ≤ m) (iso : Nonempty (G ≃* ReeF4.Model m))
  | f4 (a : ℕ) (ha : 0 < a) (iso : ExceptionalGroup.IsF4 G (2 ^ a))
  | e6 (a : ℕ) (ha : 0 < a) (iso : ExceptionalGroup.IsE6 G (2 ^ a))
  | e7 (a : ℕ) (ha : 0 < a) (iso : ExceptionalGroup.IsE7 G (2 ^ a))
  | e8 (a : ℕ) (ha : 0 < a) (iso : ExceptionalGroup.IsE8 G (2 ^ a))
  | twistedE6 (a : ℕ) (ha : 0 < a) (iso : ExceptionalGroup.IsTwistedE6 G (2 ^ a))
  | smallDerived (model : IsSmallDerivedCarrier G)

/-- Every source carrier is transported through its literal model equivalence. -/
theorem IsEvenLieCarrier.of_mulEquiv {G : Type u} {H : Type v} [Group G] [Group H]
    (h : IsEvenLieCarrier G) (e : H ≃* G) : IsEvenLieCarrier H := by
  cases h with
  | linear d a ha hp iso => exact .linear d a ha hp (iso.of_mulEquiv e)
  | unitary d a ha hp iso => exact .unitary d a ha hp (iso.of_mulEquiv e)
  | symplectic r a ha hp iso => exact .symplectic r a ha hp (iso.of_mulEquiv e)
  | orthogonalPlus r a ha hp iso => exact .orthogonalPlus r a ha hp (iso.of_mulEquiv e)
  | orthogonalOdd r a ha hp iso => exact .orthogonalOdd r a ha hp (iso.of_mulEquiv e)
  | orthogonalMinus r a ha hp iso => exact .orthogonalMinus r a ha hp (iso.of_mulEquiv e)
  | g2 a ha iso => exact .g2 a ha (iso.of_mulEquiv e)
  | suzuki m hm iso => exact .suzuki m hm (iso.map fun f => e.trans f)
  | triality a ha iso => exact .triality a ha (iso.of_mulEquiv e)
  | reeF4 m hm iso => exact .reeF4 m hm (iso.map fun f => e.trans f)
  | f4 a ha iso => exact .f4 a ha (iso.of_mulEquiv e)
  | e6 a ha iso => exact .e6 a ha (iso.of_mulEquiv e)
  | e7 a ha iso => exact .e7 a ha (iso.of_mulEquiv e)
  | e8 a ha iso => exact .e8 a ha (iso.of_mulEquiv e)
  | twistedE6 a ha iso => exact .twistedE6 a ha (iso.of_mulEquiv e)
  | smallDerived model => exact .smallDerived (model.of_mulEquiv e)

end CFSG.Quasithin.ChapterA.Section02.EvenLie
