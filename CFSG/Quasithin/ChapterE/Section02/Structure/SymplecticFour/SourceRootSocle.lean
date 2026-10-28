module
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.RootChoice
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceC2Witness

/-!
# The original rooted pair and its simple transvection socle

The characteristic-two graph automorphism changes an a₂ root into a b₁
transvection while preserving the original Sylow marking and literal opposite
pair. The source c₂ extraction then identifies the surviving simple socle
carriers inside that same pair. Thus the original root-containing branch has
no additional transvection or c₂ witness premise.

Source: Aschbacher--Smith E.2.7, printed pp.219--220, and G.4.8--9,
printed pp.340--342. Coefficient-copy recognition of the surviving A₆ and
binary PSp₄ actions remains the final step of the rooted source branch.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate TransvectionRecognition
open ChapterB InvolutionTypes Theory.GroupTheory
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- The original root-containing pair admits the same marked coordinates with
a transvection, and its actual simple socle contains a c₂ involution and has
one of the two surviving carrier types. -/
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
