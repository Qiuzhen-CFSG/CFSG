module
public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.OddSource.Defining
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.OddSource.UnitaryDefining
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.OddSource.LinearNondefining
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.OddSource.UnitaryNondefining
/-!
# The complete odd degree-three intrinsic source alternative

The defining linear case gives the elementary plane. The defining unitary
case is impossible because the permuting pair would fix an isotropic point
while containing a full Sylow two-subgroup. In both nondefining cases, the
actual three-weight action kills the normalizer Frattini commutator.
Thus the original AmbientInput and PairAction force B ≅ Eₚ² and D ≅ PSL₃(p).
No characteristic, parameter, action, or model-comparison premise is omitted;
in particular the odd field prime q may be three.

Source: Aschbacher–Smith, A.3.15(2),(3),(5) and Proposition 1.3.4,
printed pp.50–51 and 510–511. This is the remaining odd-three callback in
InvariantLarge.SylowInput.alternatives_or_odd_three.
-/
public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.OddSource
variable {J : Type*} [Group J] [Finite J]
variable {D B : Subgroup J} {S : Sylow 2 J} {p q : ℕ}

theorem alternative_of_odd_three
    (h : OddCartan.AmbientInput KnownSimple.IsKnownSimple D B S p)
    (ha : SourceTransport.PairAction p (S : Subgroup J) B)
    (hq : q.Prime) (ho : Odd q) (unitary : Bool)
    (hm : Chapter1.Section02.LocalModels.IsPSLSign D unitary 3 q) :
    Nonempty (B≃*Plane p) ∧ ClassicalGroup.IsPSL D 3 p := by
  cases unitary with
  | false =>
    change ClassicalGroup.IsPSL D 3 q at hm
    by_cases hpq : p=q
    · subst q
      exact ⟨linear_plane_of_defining h ha hm,hm⟩
    · exact (not_linear_nondefining h ha hq ho hpq hm).elim
  | true =>
    change ClassicalGroup.IsPSU D 3 q at hm
    by_cases hpq : p=q
    · subst q
      exact (not_unitary_defining h ha hm).elim
    · exact (not_unitary_nondefining h ha hq ho hpq hm).elim
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.OddSource
