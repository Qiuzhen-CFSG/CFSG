module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.SourceSwapped.Containment
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.Source

/-!
# The exchanged-component containment step of Proposition 1.3.4

The genuine nonnormal-component catalogue proves that the actual quotient
component has abelian outer group or outer group of two-power order. The
original Frattini commutator identity then makes the odd complement act by
inner automorphisms on both commuting factors. The perfect normal orbit,
ambient odd rank two and irreducibility force the complement into that orbit;
coprime lifting and the original conjugate-generation identity give the same
containment for X. Every model and action premise is discharged internally.

The earlier universal Theorems A and C retain their actual source statements.
This is the exchanged-component P ≤ K, X ≤ K claim in Aschbacher--Smith,
proof of Proposition 1.3.4, printed p.510; the subsequent model alternatives
remain a separate part of that proposition.
-/

public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G]

theorem ComponentDetection.quotient_not_normal_of_not_normal
    {P H L : Subgroup G} (hL : ComponentDetection P H L)
    (hn : ¬ (L.subgroupOf H).Normal) : ¬ (quotientImage H L).Normal := by
  let := pCore_isNilpotent (p := 2) (G := H)
  exact fun h => hn (cComponent_normal_of_quotient_normal hL.mem.2 (pCore 2 H) h)

theorem LocalInput.quotient_orbit_outer_alternative
    (hA : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple Y)
    (hC : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple Y)
    {p : ℕ} {T X P H L : Subgroup G} (_h : LocalInput p T X P H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hL : ComponentDetection P H L) (hn : ¬ (quotientImage H L).Normal) :
    IsMulCommutative (MulAut.Outer (quotientImage H L)) ∨
      IsPGroup 2 (MulAut.Outer (quotientImage H L)) := by
  have hsq : IsSQTK KnownSimple.IsKnownSimple (XiQuotient H) :=
    ⟨quotient_stronglyQuasithin hH.stronglyQuasithin, hH.isKGroup.quotient _⟩
  exact ChapterA.SQTKStructure.NonnormalOuterSource.nonnormal_component_outer
    hA hC hsq (pCore_quotient_pCore_eq_bot 2) (quotientImage H L) hL.component hn

theorem LocalInput.quotient_complement_le_swapped_orbit
    (hA : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple Y)
    (hC : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple Y)
    {p : ℕ} {T X P H L : Subgroup G} (h : LocalInput p T X P H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (hT : IsSylowIn 2 T H)
    (hL : ComponentDetection P H L) (hn : ¬ (quotientImage H L).Normal) :
    quotientImage H P ≤ quotientImage H (componentOrbit L T) :=
  h.quotient_complement_le_orbit_of_outer_alternative hH hT hL hn
    (h.quotient_orbit_outer_alternative hA hC hH hL hn)

theorem LocalInput.complement_and_X_le_swapped_orbit
    (hA : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple Y)
    (hC : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple Y)
    {p : ℕ} {T X P H L : Subgroup G} (h : LocalInput p T X P H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (hT : IsSylowIn 2 T H)
    (hL : ComponentDetection P H L) (hn : ¬ (L.subgroupOf H).Normal) :
    P ≤ componentOrbit L T ∧ X ≤ componentOrbit L T := by
  have hnbar := hL.quotient_not_normal_of_not_normal hn
  exact h.complement_and_X_le_orbit_of_outer_alternative hH hT hL hnbar
    (h.quotient_orbit_outer_alternative hA hC hH hL hnbar)

end CFSG.Quasithin.Chapter1.XiEmbedding
