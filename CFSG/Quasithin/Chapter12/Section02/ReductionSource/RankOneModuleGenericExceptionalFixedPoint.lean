module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptional
public import CFSG.Quasithin.Chapter5.A5Source.ExceptionalFixedPoint

/-!
# The source fixed-point application after outside centralization

Centralization of Ω₁(Z(T)) by the actual outside H supplies the disjointness
input to the earlier A₅ fixed-point recognition. The Cartan then fixes a
noncentral central involution in the original chosen module, giving its
actual conjugation coordinates through L/O₂(L).

The field-four marking, Cartan centralization and chosen T-invariance remain
explicit earlier inputs. In particular this does not promote a model on the
chosen subgroup to one on the whole reduced commutator layer. That separate
assertion of 5.1.14(4) remains with the exceptional source producer.
Source: Aschbacher--Smith, 5.1.14(3), 5.1.18--19, pp.639,642--644.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original outside subgroup discharges centralizer disjointness in
the Cartan fixed-point application on the actual chosen module. -/
theorem a5_model_of_outside_cartan_centralization
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHC : H ≤ Chapter6.Source.RankOneGeneric.omegaCentralizer T)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (P : Sylow 2 L) (hPT : (P : Subgroup L).map L.subtype ≤ (T : Subgroup G))
    (C : Subgroup L) (hgen : normalizer (P : Set L) ≤ (P : Subgroup L) ⊔ C)
    (hC : C.map L.subtype ≤ Chapter6.Source.RankOneGeneric.omegaCentralizer T) :
    Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  exact Chapter5.A5Source.chosen_model_of_source_cartan_centralization D
    e hTV P hPT C hgen hC (D.centralOmega_disjoint_of_outside_centralizes h hH hHC)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
