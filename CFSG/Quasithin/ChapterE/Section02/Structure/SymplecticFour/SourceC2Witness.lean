module
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.ThreeCentersSylowLift
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceTransvectionSurvivors


/-!
# A c₂ involution in the original transvection socle

The original E.2.7 geometry gives an irreducible simple socle normalized by
an actual transvection in the opposite pair. The completed three-center
coset theorem constructs a c₂ involution inside that same socle. Applying
the existing native catalogue inspection now leaves exactly A₆ and binary
PSp₄, with every source and c₂-witness premise discharged.

This closes the preliminary witness step of Aschbacher--Smith G.4.9,
printed p.341, for the original E.2.7 branch on pp.219--220. Identifying the
surviving carrier action with a coefficient copy remains a separate step.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate TransvectionRecognition
open ChapterB InvolutionTypes Theory.GroupTheory
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- The original pair's actual simple socle contains a c₂ involution.
The witness is constructed from the irreducible socle and the original
normalizing transvection, with no coset or lifting premise. -/
theorem source_transvection_simple_socle_isC2 {n:ℕ}
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
    ∃ i:N, IsC2 (i:Sp F) := by
  dsimp only
  let H := oppositePair (V.comap (L.subtype.comp e.toMonoidHom))
  let C := transvectionClosure H
  let N := (generalizedFitting C).map (H.subtype.comp C.subtype)
  obtain ⟨_,hNi,hNn⟩ := source_transvection_simple_socle_image hF hn T hP hJ L e hmark
    hgen V hVT hVM hVN hr hex
  obtain ⟨a,ha,haB⟩ := hex
  obtain ⟨b,_,_,_,hab,hc2⟩ := irreducible_normalized_exists_isC2 hF N hNi a haB (hNn ha)
  exact ⟨⟨a*b,hab⟩,hc2⟩

/-- The complete original b₁ branch has just two possible simple-socle
carriers. The independent c₂-witness premise of the catalogue reduction is
now discharged on that same embedded socle. -/
theorem source_transvection_socle_carriers {n:ℕ}
    (hF:Nat.card F=2^n) (hn:1<n)
    (hG:IsSQTK KnownSimple.IsKnownSimple G)
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
    Nonempty (N≃*alternatingGroup (Fin 6)) ∨
      ∃ f:ℕ, 2≤f ∧ ClassicalGroup.IsPSp N 2 (2^f) :=
  source_transvection_socle_alternatingSix_or_symplectic hF hn hG T hP hJ L e hmark hgen
    V hVT hVM hVN hr hex
    (source_transvection_simple_socle_isC2 hF hn T hP hJ L e hmark hgen V hVT hVM hVN hr hex)

end CFSG.Quasithin.ChapterE.Structure.SymplecticFour
