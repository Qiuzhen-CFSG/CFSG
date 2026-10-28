module
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.RootChoice
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceC2Witness

/-!
# The original rooted pair and its two simple-socle carriers

The exceptional graph automorphism changes a short-root involution into a
transvection while preserving the original component, Sylow marking and
opposition construction. The three-center argument then constructs a c₂
involution in the same simple socle. The native catalogue leaves precisely
A₆ and binary PSp₄, with no independent involution-witness premise.

This is the rooted branch of Aschbacher--Smith E.2.7, printed pp.219--220,
using G.4.9 on p.341. Identification of either surviving action with its
coefficient model remains a separate representation-theoretic step.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate TransvectionRecognition
open ChapterB InvolutionTypes Theory.GroupTheory
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- The original root-containing pair admits a transvection marking and the
actual socle has one of the two surviving carriers. -/
theorem source_root_pair_socle_carriers {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1<n)
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hJ : minimalParabolicCore T hP = ⊥)
    (L : Subgroup G) [L.Normal] [IsSimpleGroup L] (e : Sp F ≃* L)
    (hmark : (T : Subgroup G).comap (L.subtype.comp e.toMonoidHom) = unipotent)
    (hgen : L ⊔ (T : Subgroup G) = ⊤)
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hVM : V ≤ (minimalParabolicMax T hP).pCoreIn 2)
    (hVN : (T : Subgroup G) ≤ normalizer (V : Set G)) (hr : 2 < Nat.card V)
    (hroot : ∃ x ∈ oppositePair (V.comap (L.subtype.comp e.toMonoidHom)), IsRootElement x) :
    ∃ e' : Sp F ≃* L,
      (T : Subgroup G).comap (L.subtype.comp e'.toMonoidHom) = unipotent ∧
      (∃ x ∈ oppositePair (V.comap (L.subtype.comp e'.toMonoidHom)), IsB1 x) ∧
      let P := oppositePair (V.comap (L.subtype.comp e'.toMonoidHom))
      let C := transvectionClosure P
      let N := (generalizedFitting C).map (P.subtype.comp C.subtype)
      (∃ i : N, IsC2 (i : Sp F)) ∧
        (Nonempty (N ≃* alternatingGroup (Fin 6)) ∨
          ∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSp N 2 (2^f)) := by
  obtain ⟨e',hm,hex⟩ := exists_marked_transvection_of_root (T : Subgroup G) V L e hmark hroot
  refine ⟨e',hm,hex,?_,?_⟩
  · exact source_transvection_simple_socle_isC2 hF hn T hP hJ L e' hm hgen
      V hVT hVM hVN hr hex
  · exact source_transvection_socle_carriers hF hn hG T hP hJ L e' hm hgen
      V hVT hVM hVN hr hex

end CFSG.Quasithin.ChapterE.Structure.SymplecticFour
