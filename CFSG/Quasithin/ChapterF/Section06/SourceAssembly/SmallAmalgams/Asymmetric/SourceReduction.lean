module

public import CFSG.Quasithin.ChapterF.Section06.Amalgams.WeakBN
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Asymmetric.ThompsonEscape

/-!
# Faithful source reductions before the F.1.12 enumeration

The actual Goldschmidt pair supplies the weak-BN input and two independent
escape records. The elementary Thompson subgroup escapes at least one local
2-core, while the Ω₁ of the common Sylow center has a moved orientation and
therefore yields a literal F.7 track. These records are kept separate: no
unproved identification of the two escape witnesses is made.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Asymmetric
open CFSG.Quasithin.ChapterF
variable {G : Type*} [Group G] [Finite G] {A B : Subgroup G}

theorem source_reduction
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A)
    (hB : generalizedFitting B=pCore 2 B)
    (S : Sylow 2 G) (hS : A⊓B=(S : Subgroup G)) :
    Source.HypothesisF11 (goldschmidtVertices A B) (A⊓B) ∧
      ((¬ elementaryAbelianMaxJ (S : Subgroup G) ≤ (pCore 2 A).map A.subtype) ∨
       (¬ elementaryAbelianMaxJ (S : Subgroup G) ≤ (pCore 2 B).map B.subtype)) ∧
      (∃ C D : Subgroup G, ((C=A ∧ D=B) ∨ (C=B ∧ D=A)) ∧
        ∃ (hSC : (S : Subgroup G)≤C)
          (E : Section07.Track.SourceSetup (pairFamily C D)),
          E.V=SylowOmegaSpan.span (S.subtype hSC) ∧ E.V≠⊥) := by
  refine ⟨h.source_hypothesis_of_characteristic_two hcore hA hB,
    thompson_escapes_one_core h hcore hA S hS, ?_⟩
  obtain ⟨C,D,ho,hSC,E,hV,hne,_⟩ := exists_oriented_source_track h hcore hA hB S hS
  exact ⟨C,D,ho,hSC,E,hV,hne⟩
end CFSG.Quasithin.ChapterF.SourceAssembly.Asymmetric
