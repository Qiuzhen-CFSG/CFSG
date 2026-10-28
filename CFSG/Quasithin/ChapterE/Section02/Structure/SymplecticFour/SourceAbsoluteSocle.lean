module
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceTransvectionSocle
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.AbsoluteSocle

/-!
# Absolute irreducibility of the original source socle

The completed G.4.9 source theorem gives the literal simple F-irreducible
socle and its normalization by the original opposite pair. The original
transvection witness belongs to that pair and therefore normalizes the
socle. The rank-one normalizer theorem upgrades the same natural action
to absolute irreducibility, without a new source premise or a transvection
inside the socle. Source: Aschbacher--Smith G.4.1, printed p.342.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate TransvectionRecognition
open ChapterB InvolutionTypes Theory.GroupTheory
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- The original source socle is absolutely irreducible on the original
F-space; its carrier and normalization by the original pair are retained. -/
theorem source_transvection_simple_socle_image_absolutelyIrreducible {n:ℕ}
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
    let C := transvectionClosure H
    let N := (generalizedFitting C).map (H.subtype.comp C.subtype)
    IsSimpleGroup N ∧
      Representation.IsAbsolutelyIrreducible ((Representation.symplecticNatural 2).comp N.subtype) ∧
      H≤normalizer (N:Set (Sp F)) := by
  dsimp only
  obtain ⟨hs,hi,hN⟩ := source_transvection_simple_socle_image hF hn T hP hJ
    L e hmark hgen V hVT hVM hVN hr hex
  obtain ⟨t,ht,htr⟩ := hex
  exact ⟨hs,subgroup_absolutelyIrreducible_of_isB1_normalizer _ hi t (hN ht) htr,hN⟩

end CFSG.Quasithin.ChapterE.Structure.SymplecticFour
