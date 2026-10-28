module
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.Homogeneous
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceTransvectionClosure

/-!
# Original E.2.7 homogeneous normal restrictions

The original local inputs make the exact F-transvection closure irreducible.
Its literal involutory rank-one generators then imply that every normal
restriction is homogeneous, with any chosen irreducible constituent specifying
the unique simple type. No primitivity or binary-irreducibility premise remains.

Source: Aschbacher--Smith E.2.7, printed pp.219--221, and the standing reduction
after G.4.6 used in G.4.9, printed pp.340--342.
-/

public noncomputable section
open Subgroup
open scoped MonoidAlgebra
namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate TransvectionRecognition
open ChapterB InvolutionTypes
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

theorem source_transvection_closure_normal_restriction_isotypic {n:ℕ}
    (hF:Nat.card F=2^n) (hn:1<n)
    (T:Sylow 2 G) (hP:IsMinimalParabolicOver T ⊤)
    (hJ:minimalParabolicCore T hP=⊥)
    (L:Subgroup G) [L.Normal] [IsSimpleGroup L] (e:Sp F≃*L)
    (hmark:(T:Subgroup G).comap (L.subtype.comp e.toMonoidHom)=unipotent)
    (hgen:L⊔(T:Subgroup G)=⊤)
    (V:Subgroup G) [IsElementaryAbelian 2 V] (hVT:V≤T)
    (hVM:V≤(minimalParabolicMax T hP).pCoreIn 2)
    (hVN:(T:Subgroup G)≤normalizer (V:Set G)) (hr:2<Nat.card V)
    (hex:∃ h∈oppositePair (V.comap (L.subtype.comp e.toMonoidHom)),IsB1 h)
    (N : Subgroup (transvectionClosure (oppositePair (V.comap (L.subtype.comp e.toMonoidHom)))))
    [N.Normal]
    (A : Subrepresentation
      (((pairAction (V.comap (L.subtype.comp e.toMonoidHom))).comp
        (transvectionClosure (oppositePair (V.comap (L.subtype.comp e.toMonoidHom)))).subtype).comp
          N.subtype)) [hA : A.toRepresentation.IsIrreducible] :
    IsIsotypicOfType F[N]
      (Representation.asModule
        (((pairAction (V.comap (L.subtype.comp e.toMonoidHom))).comp
          (transvectionClosure (oppositePair (V.comap (L.subtype.comp e.toMonoidHom)))).subtype).comp
            N.subtype)) A.asSubmodule :=
  transvectionClosure_normal_restriction_isotypic
    (oppositePair (V.comap (L.subtype.comp e.toMonoidHom)))
    (source_transvection_closure_irreducible hF hn T hP hJ L e hmark hgen V hVT hVM hVN hr hex)
    N A (hA := hA)

end CFSG.Quasithin.ChapterE.Structure.SymplecticFour
