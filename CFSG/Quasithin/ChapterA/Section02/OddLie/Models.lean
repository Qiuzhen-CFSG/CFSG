module
public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.ClassificationModels.RankTwo
/-!
# Literal odd-characteristic carriers for source A.2.17

Every branch records an actual model with its full catalogue parameters.
There is no upper-rank or classification conclusion in this predicate.
The positive odd prime-power parameters retain the field and cover data
needed by the original simple and quasisimple source cases.
Source: Aschbacher–Smith A.2.17, printed pp.38–39; GLS3, Theorem 2.2.7.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterA.Section02.OddLie
open KnownSimple ClassificationModels
universe u
inductive IsOddLieCarrier (G : Type u) [Group G] : Prop
  | linear (d r e : ℕ) (hr : r.Prime) (ho : Odd r) (he : 0 < e)
      (parameters : LinearParameters d (r^e)) (model : ClassicalGroup.IsPSL G d (r^e))
  | unitary (d r e : ℕ) (hr : r.Prime) (ho : Odd r) (he : 0 < e)
      (parameters : UnitaryParameters d (r^e)) (model : ClassicalGroup.IsPSU G d (r^e))
  | symplectic (d r e : ℕ) (hr : r.Prime) (ho : Odd r) (he : 0 < e)
      (parameters : SymplecticParameters d (r^e)) (model : ClassicalGroup.IsPSp G d (r^e))
  | orthogonalPlus (d r e : ℕ) (hr : r.Prime) (ho : Odd r) (he : 0 < e)
      (parameters : OrthogonalPlusParameters d (r^e)) (model : ClassicalGroup.IsPOmegaPlus G d (r^e))
  | orthogonalOdd (d r e : ℕ) (hr : r.Prime) (ho : Odd r) (he : 0 < e)
      (parameters : OrthogonalOddParameters d (r^e)) (model : ClassicalGroup.IsPOmegaOdd G d (r^e))
  | orthogonalMinus (d r e : ℕ) (hr : r.Prime) (ho : Odd r) (he : 0 < e)
      (parameters : OrthogonalMinusParameters d (r^e)) (model : ClassicalGroup.IsPOmegaMinus G d (r^e))
  | g2 (r e : ℕ) (hr : r.Prime) (ho : Odd r) (he : 0 < e)
      (model : IsG2At G (r^e))
  | ree (q : ℕ) (model : ExceptionalGroup.IsReeG2 G q)
  | triality (P : Triality.Standard.Parameters) (ho : Odd P.prime)
      (model : Nonempty (G ≃* Triality.Standard.Carrier P))
  | f4 (r e : ℕ) (hr : r.Prime) (ho : Odd r) (he : 0 < e)
      (model : ExceptionalGroup.IsF4 G (r^e))
  | e6 (r e : ℕ) (hr : r.Prime) (ho : Odd r) (he : 0 < e)
      (model : ExceptionalGroup.IsE6 G (r^e))
  | e7 (r e : ℕ) (hr : r.Prime) (ho : Odd r) (he : 0 < e)
      (model : ExceptionalGroup.IsE7 G (r^e))
  | e8 (r e : ℕ) (hr : r.Prime) (ho : Odd r) (he : 0 < e)
      (model : ExceptionalGroup.IsE8 G (r^e))
  | twistedE6 (r e : ℕ) (hr : r.Prime) (ho : Odd r) (he : 0 < e)
      (model : ExceptionalGroup.IsTwistedE6 G (r^e))
end CFSG.Quasithin.ChapterA.Section02.OddLie
