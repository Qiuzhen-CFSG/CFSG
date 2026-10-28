module
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.FieldExtraction.MovingPair
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceTransvectionClosure

/-!
# The original E.2.7 transvection closure over its minimal field

The original local hypotheses first give irreducibility of the literal
F-transvection normal closure. Its actual rank-one witness then constructs an
absolutely irreducible four-dimensional model over its trace subfield, an
explicit scalar-extension equivalence, and a compatible invariant
nondegenerate alternating form. The coefficient field is minimal by trace
invariance; it is neither assumed to be binary nor forced to equal F.

Source: Aschbacher--Smith E.2.7, printed pp.219--221, using the coefficient-model
portion of G.4.8, printed pp.340--341. Group-image recognition remains separate.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate TransvectionRecognition
open ChapterB InvolutionTypes
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- A compatible minimal-field model of the same original transvection closure. -/
theorem source_transvection_closure_traceField_model {n:ℕ}
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
    Nonempty (Representation.TraceFieldDescent.Model
      ((pairAction (V.comap (L.subtype.comp e.toMonoidHom))).comp
        (transvectionClosure (oppositePair (V.comap (L.subtype.comp e.toMonoidHom)))).subtype)
      (form F)
      (Representation.TraceFieldDescent.traceField
        ((pairAction (V.comap (L.subtype.comp e.toMonoidHom))).comp
          (transvectionClosure (oppositePair (V.comap (L.subtype.comp e.toMonoidHom)))).subtype))) :=
  transvectionClosure_traceField_model
    (oppositePair (V.comap (L.subtype.comp e.toMonoidHom)))
    (source_transvection_closure_irreducible hF hn T hP hJ L e hmark hgen V hVT hVM hVN hr hex)
    hex

end CFSG.Quasithin.ChapterE.Structure.SymplecticFour
