module
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.NormalClosure
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceImprimitiveExclusion

/-!
# Irreducibility of the original transvection closure

The literal source pair acts irreducibly over F. Its nontrivial normal
F-transvection closure therefore acts irreducibly or yields actual orthogonal
planes permuted by the pair. The original moving-actor geometry excludes
those planes, completing the G.4.6--7 reduction on the same component and pair.
The root witness is only required to lie in the pair, as in E.2.7.

Source: Aschbacher--Smith E.2.7, printed pp.219--220, and G.4.6--7,
printed pp.339--340. Coefficient-field recognition remains separate.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate TransvectionRecognition
open ChapterB InvolutionTypes
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- The actual original E.2.7 pair's F-transvections generate an irreducible
normal subgroup of that same pair; the transvection need only lie in the pair. -/
theorem source_transvection_closure_irreducible {n:ℕ}
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
    Representation.IsIrreducible
      ((pairAction (V.comap (L.subtype.comp e.toMonoidHom))).comp
        (transvectionClosure (oppositePair (V.comap (L.subtype.comp e.toMonoidHom)))).subtype) := by
  obtain ⟨_,_,_,hi,_⟩ := source_geometry hF hn T hP hJ L e hmark hgen V hVT hVM hVN hr
  rcases transvectionClosure_irreducible_or_orthogonal_two
    (oppositePair (V.comap (L.subtype.comp e.toMonoidHom))) hi hex with hi | ⟨D,hD⟩
  · exact hi
  · exact (source_geometry_imprimitive_exclusion hF hn T hP hJ L e hmark hgen
      V hVT hVM hVN hr D hD).elim

end CFSG.Quasithin.ChapterE.Structure.SymplecticFour
