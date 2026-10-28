module
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceNonrootRecognized
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceRootedSocle
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceAlternatingSixRecognized
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceSymplecticRecognized

/-!
# Recognition of the original symplectic opposite pair

The root-free branch gives the marked Suzuki witness. In the root-containing
branch, the graph automorphism preserves the Sylow marking and supplies a
transvection. The actual simple socle is A₆ or a nonbinary PSp₄; the two
coefficient-recognition theorems identify the whole original pair and supply
every Sylow, Borel, center and core mark. No root, carrier or action premise
remains beyond the original source hypotheses.

Source: Aschbacher--Smith E.2.7, printed pp.219--221. The literal quotient
application to the cubic bound is in Chapter3/Section01/SourceNumericalComplete.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate InvolutionTypes
open ChapterB
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- The original E.2.7 pair has all the recognized source markings. -/
theorem source_hasRecognizedPair {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1<n)
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hJ : minimalParabolicCore T hP = ⊥)
    (L : Subgroup G) [L.Normal] [IsSimpleGroup L] (e : Sp F ≃* L)
    (hmark : (T : Subgroup G).comap (L.subtype.comp e.toMonoidHom) = unipotent)
    (hgen : L ⊔ (T : Subgroup G) = ⊤)
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hVM : V ≤ (minimalParabolicMax T hP).pCoreIn 2)
    (hVN : (T : Subgroup G) ≤ normalizer (V : Set G)) (hr : 2 < Nat.card V) :
    Witnesses.SymplecticFour.HasRecognizedPair T (minimalParabolicMax T hP) V := by
  by_cases hroot : ∃ x ∈ oppositePair (V.comap (L.subtype.comp e.toMonoidHom)),
      IsRootElement x
  · obtain ⟨e',hm,hex,_,h6 | hsp⟩ := source_root_pair_socle_carriers hF hn hG
      T hP hJ L e hmark hgen V hVT hVM hVN hr hroot
    · exact source_alternatingSix_hasRecognizedPair hF hn T hP hJ L e' hm hgen
        V hVT hVM hVN hr hex h6
    · exact source_symplectic_hasRecognizedPair hF hn T hP hJ L e' hm hgen
        V hVT hVM hVN hr hex hsp
  · exact source_nonroot_hasRecognizedPair hF hn hG T hP hJ L e hmark hgen
      V hVT hVM hVN hr (by simpa only [not_exists, not_and] using hroot)

end CFSG.Quasithin.ChapterE.Structure.SymplecticFour
