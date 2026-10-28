module
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.TransvectionFusion
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceTransvectionClosure

/-!
# Internal transvection fusion for the original E.2.7 closure

The original pair geometry makes its F-transvection closure irreducible.
The odd-product and orbit-span argument then conjugates any two of its
transvections by an element of that same closure. This supplies the standing
fusion input of G.4.9 on the literal original subgroup and coefficient field.

Source: Aschbacher--Smith G.4.5--6, printed pp.339--340, applied in E.2.7,
printed pp.219--220. Socle and group-image recognition remain separate.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate TransvectionRecognition
open ChapterB InvolutionTypes
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- Every two F-transvections in the original normal closure are fused inside it. -/
theorem source_transvection_closure_isConj {n:ℕ}
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
    ∀ a b : transvectionClosure (oppositePair (V.comap (L.subtype.comp e.toMonoidHom))),
      IsB1 ((a : oppositePair (V.comap (L.subtype.comp e.toMonoidHom))) : Sp F) →
      IsB1 ((b : oppositePair (V.comap (L.subtype.comp e.toMonoidHom))) : Sp F) → IsConj a b := by
  intro a b ha hb
  exact transvectionClosure_isConj _
    (source_transvection_closure_irreducible hF hn T hP hJ L e hmark hgen
      V hVT hVM hVN hr hex) a b ha hb

end CFSG.Quasithin.ChapterE.Structure.SymplecticFour
