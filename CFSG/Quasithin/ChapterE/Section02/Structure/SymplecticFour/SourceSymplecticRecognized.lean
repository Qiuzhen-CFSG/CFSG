module
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.SymplecticRecognition
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceTransvectionSocle
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.SymplecticFour.CoefficientSource

/-!
# Recognizing the nonbinary symplectic source pair

The original transvection socle is irreducible and normalized by the original
opposite pair. In its nonbinary PSp₄ carrier branch, the trivial matrix center
supplies a faithful Sp₄ carrier. Trace descent over a subfield of that carrier's
order and equality of group orders recognize the literal embedded socle.
Its coefficient copy is self-normalizing, so the entire original pair is that
copy. The existing coefficient-source construction supplies every required
Sylow, Borel, center and core mark for the original subgroup V.

The only carrier premise is the second alternative of
`source_root_pair_socle_carriers`; no action or coefficient-model premise
remains. Source: Aschbacher--Smith E.2.7, printed pp.219--220, using G.4.1 and
G.4.8, printed pp.340--342.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate TransvectionRecognition
open DiagramAutomorphisms.FieldFixedResidual ChapterB InvolutionTypes Theory.GroupTheory
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- The nonbinary PSp₄ source-socle branch identifies the whole original pair
with a conjugate of its actual coefficient symplectic group. -/
theorem source_symplectic_coefficient_copy {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1<n)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hJ : minimalParabolicCore T hP = ⊥)
    (L : Subgroup G) [L.Normal] [IsSimpleGroup L] (e : Sp F ≃* L)
    (hmark : (T : Subgroup G).comap (L.subtype.comp e.toMonoidHom) = unipotent)
    (hgen : L ⊔ (T : Subgroup G) = ⊤)
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hVM : V ≤ (minimalParabolicMax T hP).pCoreIn 2)
    (hVN : (T : Subgroup G) ≤ normalizer (V : Set G)) (hr : 2 < Nat.card V)
    (hex : ∃ h ∈ oppositePair (V.comap (L.subtype.comp e.toMonoidHom)), IsB1 h) :
    let H := oppositePair (V.comap (L.subtype.comp e.toMonoidHom))
    let C := transvectionClosure H
    let N := (generalizedFitting C).map (H.subtype.comp C.subtype)
    (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSp N 2 (2^f)) →
      ∃ K : Subfield F, ∃ c : Sp F,
        H = (coefficientInclusion K).range.map (MulAut.conj c).toMonoidHom := by
  dsimp only
  rintro ⟨f,hf,K,_,_,hK,⟨eK⟩⟩
  let : CharP K 2 := EvenProjective.charTwo_of_card hK
  let H := oppositePair (V.comap (L.subtype.comp e.toMonoidHom))
  let C := transvectionClosure H
  let N := (generalizedFitting C).map (H.subtype.comp C.subtype)
  let eN : N ≃* Sp K := eK.trans EvenProjective.equiv.symm
  obtain ⟨_,hNi,hNn⟩ := source_transvection_simple_socle_image hF hn T hP hJ L e hmark
    hgen V hVT hVM hVN hr hex
  have hNH : N ≤ H := by
    rintro x ⟨c,_,rfl⟩
    exact c.val.property
  obtain ⟨K₀,_,c,hcopy⟩ := coefficient_copy_of_normalized_symplectic_carrier
    hF (show 0<f by omega) hK H N hNH hNn hNi eN hex
  exact ⟨K₀,c,hcopy⟩

/-- The nonbinary PSp₄ branch supplies all marks for the original E.2.7
witness, with no additional action, Sylow or core premise. -/
theorem source_symplectic_hasRecognizedPair {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1<n)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hJ : minimalParabolicCore T hP = ⊥)
    (L : Subgroup G) [L.Normal] [IsSimpleGroup L] (e : Sp F ≃* L)
    (hmark : (T : Subgroup G).comap (L.subtype.comp e.toMonoidHom) = unipotent)
    (hgen : L ⊔ (T : Subgroup G) = ⊤)
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hVM : V ≤ (minimalParabolicMax T hP).pCoreIn 2)
    (hVN : (T : Subgroup G) ≤ normalizer (V : Set G)) (hr : 2 < Nat.card V)
    (hex : ∃ h ∈ oppositePair (V.comap (L.subtype.comp e.toMonoidHom)), IsB1 h) :
    let H := oppositePair (V.comap (L.subtype.comp e.toMonoidHom))
    let C := transvectionClosure H
    let N := (generalizedFitting C).map (H.subtype.comp C.subtype)
    (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSp N 2 (2^f)) →
      Witnesses.SymplecticFour.HasRecognizedPair T (minimalParabolicMax T hP) V := by
  dsimp only
  intro hsp
  obtain ⟨K,c,hcopy⟩ := source_symplectic_coefficient_copy hF hn T hP hJ L e hmark hgen
    V hVT hVM hVN hr hex hsp
  exact Witnesses.SymplecticFour.source_hasRecognizedPair_of_coefficient_copy hF hn T hP hJ L e
    hmark hgen V hVT hVM hVN hr K c hcopy

end CFSG.Quasithin.ChapterE.Structure.SymplecticFour
