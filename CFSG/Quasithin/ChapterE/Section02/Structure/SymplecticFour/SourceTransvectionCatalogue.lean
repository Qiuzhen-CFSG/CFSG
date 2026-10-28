module
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceAbsoluteSocle
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.KnownSimpleSectionTransport

/-!
# The inherited catalogue of the original transvection socle

The source simple socle is an actual image of a component of the transvection
closure, hence is perfect and nonsolvable. The original SQTK hypothesis
restricts through the actual ambient symplectic equivalence and the same
embedded subgroup. The proved Theorem C classification therefore supplies
its full native carrier catalogue, without a new classification premise.
Source: Aschbacher--Smith G.4.1, printed p.342.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate TransvectionRecognition
open ChapterB InvolutionTypes Theory.GroupTheory
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- The same embedded simple socle inherits the genuine Theorem C catalogue
and nonsolvability from the original source hypotheses. -/
theorem source_transvection_simple_socle_image_catalogue {n:ℕ}
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
    ChapterA.Section02.IsTheoremCModel N ∧ ¬Group.IsSolvable N := by
  dsimp only
  let H := oppositePair (V.comap (L.subtype.comp e.toMonoidHom))
  let C := transvectionClosure H
  let E := generalizedFitting C
  let f : C→*Sp F := H.subtype.comp C.subtype
  let N := E.map f
  obtain ⟨hcomp,_,_⟩ := source_transvection_closure_simple_socle hF hn T hP hJ
    L e hmark hgen V hVT hVM hVN hr hex
  let : IsQuasisimple E := hcomp.2
  let : Group.IsPerfect N := Group.IsPerfect.map f
  obtain ⟨hs,_,_⟩ := source_transvection_simple_socle_image hF hn T hP hJ
    L e hmark hgen V hVT hVM hVN hr hex
  let : IsSimpleGroup N := hs
  have hsq := ((hG.subgroup L).knownSimple_of_equiv e.symm).subgroup N
  exact ⟨ChapterA.Section02.theoremC_knownSimple inferInstance
    (Group.IsPerfect.not_isMulCommutative N) hsq.stronglyQuasithin hsq.isKGroup,
    Group.IsPerfect.not_isSolvable N⟩

end CFSG.Quasithin.ChapterE.Structure.SymplecticFour
