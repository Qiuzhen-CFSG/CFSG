module
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceThreeCenters
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.ThreeCentersDihedralLift

/-!
# The SL₂ quotient on the original E.2.7 transvection closure

The original irreducible closure supplies the three-center configuration.
If the required commuting-coset witness is absent, the literal quotient image
of its local generated subgroup is SL₂ over a binary subfield of degree
strictly greater than one. The dihedral alternative is now discharged by
central-kernel lifting and the actual three-center geometry.

Source: Aschbacher--Smith G.4.9, printed p.341, applied to E.2.7, printed
pp.219--220. The SL₂ Sylow lifting step remains separate; this is not yet an
unconditional coset-witness theorem.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate TransvectionRecognition
open ChapterB InvolutionTypes
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- The original marked closure has a genuine SL₂ quotient if its source
commuting-coset witness is absent. -/
theorem source_transvection_quotient_sl2_of_no_coset_witness {n:ℕ}
    (hF:Nat.card F=2^n) (hn:1<n)
    (T:Sylow 2 G) (hP:IsMinimalParabolicOver T ⊤)
    (hJ:minimalParabolicCore T hP=⊥)
    (L:Subgroup G) [L.Normal] [IsSimpleGroup L] (e:Sp F≃*L)
    (hmark:(T:Subgroup G).comap (L.subtype.comp e.toMonoidHom)=unipotent)
    (hgen:L⊔(T:Subgroup G)=⊤)
    (V:Subgroup G) [IsElementaryAbelian 2 V] (hVT:V≤T)
    (hVM:V≤(minimalParabolicMax T hP).pCoreIn 2)
    (hVN:(T:Subgroup G)≤normalizer (V:Set G)) (hr:2<Nat.card V)
    (hex:∃ h∈oppositePair (V.comap (L.subtype.comp e.toMonoidHom)),IsB1 h) :
    let H := oppositePair (V.comap (L.subtype.comp e.toMonoidHom))
    let X := (transvectionClosure H).map H.subtype
    ∀ a : transvectionClosure H, IsB1 ((a : H) : Sp F) →
      (¬∃ b : Sp F, IsB1 b ∧ ((a : H) : Sp F)⁻¹*b∈X ∧
        Commute ((a : H) : Sp F) b ∧ ((a : H) : Sp F)*b∈X ∧
        IsC2 (((a : H) : Sp F)*b)) →
      ∃ D : ThreeCenterConfiguration X ((a : H) : Sp F),
        ∃ k : ℕ, 1<k ∧ k∣n ∧
          Nonempty (D.quotientImage ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k)) := by
  dsimp only
  intro a ha hno
  obtain ⟨D⟩ := source_transvection_threeCenterConfiguration hF hn T hP hJ L e
    hmark hgen V hVT hVM hVN hr hex a ha
  refine ⟨D,D.quotientImage_sl2_of_no_coset_witness hF ha ?_ hno⟩
  exact le_normalizer (mem_map_of_mem _ a.property)

end CFSG.Quasithin.ChapterE.Structure.SymplecticFour
