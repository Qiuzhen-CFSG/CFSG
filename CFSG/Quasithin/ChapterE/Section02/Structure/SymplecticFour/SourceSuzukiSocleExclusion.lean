module
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceTransvectionSocle
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.SuzukiNormalizer

/-!
# The original transvection socle is not a Suzuki group

The original source geometry supplies the same simple irreducible socle
normalized by the pair, and a rank-one involution in that pair. The actual
Suzuki normalizer exclusion applies with no new source premise. This is
the Suzuki row of Aschbacher--Smith G.4.1, printed p.342.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate TransvectionRecognition
open ChapterB InvolutionTypes Theory.GroupTheory
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- The literal original-source socle has no Suzuki carrier. -/
theorem source_transvection_socle_not_suzuki {n:ℕ}
    (hF:Nat.card F=2^n) (hn:1<n)
    (T:Sylow 2 G) (hP:IsMinimalParabolicOver T ⊤)
    (hJ:minimalParabolicCore T hP=⊥)
    (L:Subgroup G) [L.Normal] [IsSimpleGroup L] (e:Sp F≃*L)
    (hmark:(T:Subgroup G).comap (L.subtype.comp e.toMonoidHom)=unipotent)
    (hgen:L⊔(T:Subgroup G)=⊤)
    (V:Subgroup G) [IsElementaryAbelian 2 V] (hVT:V≤T)
    (hVM:V≤(minimalParabolicMax T hP).pCoreIn 2)
    (hVN:(T:Subgroup G)≤normalizer (V:Set G)) (hr:2<Nat.card V)
    (hex:∃ h∈oppositePair (V.comap (L.subtype.comp e.toMonoidHom)),IsB1 h) {m:ℕ} (hm:1≤m) :
    let H := oppositePair (V.comap (L.subtype.comp e.toMonoidHom))
    let C := transvectionClosure H
    let N := (generalizedFitting C).map (H.subtype.comp C.subtype)
    ¬Nonempty (N≃*BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  dsimp only
  obtain ⟨_,hi,hN⟩ := source_transvection_simple_socle_image hF hn T hP hJ
    L e hmark hgen V hVT hVM hVN hr hex
  obtain ⟨t,ht,htr⟩ := hex
  exact not_suzuki_of_isB1_normalizer _ hi t (hN ht) htr hm

end CFSG.Quasithin.ChapterE.Structure.SymplecticFour
