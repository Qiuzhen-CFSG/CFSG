module
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.ThreeCenters
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceTransvectionClosure

/-!
# The three-center point-local configuration on the original E.2.7 closure

The actual normal transvection closure is F-irreducible. For each of its
transvections, its center orbit supplies two more conjugates spanning a
three-space. Their common perpendicular point is fixed, and a literal
symplectic frame embeds the triple-generated group in pointLocal.

Source: the opening geometry in Aschbacher--Smith G.4.9, printed p.341,
applied to E.2.7, printed pp.219--220. The later C2 coset witness is not assumed
or concluded here; its point-parabolic lift remains a separate source step.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate TransvectionRecognition
open ChapterB InvolutionTypes
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- The original closure supplies the literal three-center configuration. -/
theorem source_transvection_threeCenterConfiguration {n:ℕ}
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
    ∀ a : transvectionClosure H, IsB1 ((a : H) : Sp F) →
      Nonempty (ThreeCenterConfiguration ((transvectionClosure H).map H.subtype) ((a : H) : Sp F)) := by
  dsimp only
  intro a ha
  exact transvectionClosure_threeCenterConfiguration _
    (source_transvection_closure_irreducible hF hn T hP hJ L e hmark hgen
      V hVT hVM hVN hr hex) a ha

end CFSG.Quasithin.ChapterE.Structure.SymplecticFour
