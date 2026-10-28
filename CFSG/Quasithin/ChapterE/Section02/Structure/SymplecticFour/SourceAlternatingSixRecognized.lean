module
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.AlternatingSixRecognition
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceC2Witness
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceAbsoluteSocle
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.SymplecticFour.CoefficientSource

/-!
# The complete original A₆-socle symplectic witness

On the actual opposite pair from E.2.7, the source geometry supplies the
irreducible simple socle, its absolute irreducibility, and a c₂ involution.
For the A₆ carrier alternative, binary natural coordinates and Frobenius
normalizer rigidity identify the whole pair with a conjugate of Sp₄(2).
The existing coefficient-copy consumer then constructs every Sylow, Borel,
center and core mark for the original subgroup V.

No matrix-model, action, c₂, internal-conjugator or marking premise remains
in this carrier branch. Its A₆ premise is the first alternative of the proved
source_transvection_socle_carriers. The other, nonbinary PSp₄ row remains a
separate source obligation.

Source: Aschbacher--Smith E.2.7, printed pp.219--220, using G.4.1, p.342.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate TransvectionRecognition
open DiagramAutomorphisms.FieldFixedResidual ChapterB InvolutionTypes Theory.GroupTheory
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- The A₆ source-socle branch identifies the whole original opposite pair
with a conjugate of Sp₄ over the binary coefficient subfield. -/
theorem source_alternatingSix_coefficient_copy {n:ℕ}
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
    Nonempty (N≃*alternatingGroup (Fin 6)) →
      ∃ K:Subfield F, Nat.card K=2 ∧ ∃ c:Sp F,
        H=(coefficientInclusion K).range.map (MulAut.conj c).toMonoidHom := by
  dsimp only
  intro h6
  let H := oppositePair (V.comap (L.subtype.comp e.toMonoidHom))
  let C := transvectionClosure H
  let N := (generalizedFitting C).map (H.subtype.comp C.subtype)
  obtain ⟨_,hNi,hNn⟩ := source_transvection_simple_socle_image hF hn T hP hJ L e hmark
    hgen V hVT hVM hVN hr hex
  obtain ⟨_,hNa,_⟩ := source_transvection_simple_socle_image_absolutelyIrreducible hF hn
    T hP hJ L e hmark hgen V hVT hVM hVN hr hex
  obtain ⟨e6⟩ := h6
  apply BinaryA6.coefficient_copy_of_alternatingSix_socle H N _ hNn e6 hNi hNa
    (source_transvection_simple_socle_isC2 hF hn T hP hJ L e hmark hgen V hVT hVM hVN hr hex) hex
  rintro x ⟨c,_,rfl⟩
  exact c.val.property

/-- The A₆ branch supplies every mark for the original E.2.7 witness;
coefficient recognition, Sylow alignment and the core are discharged. -/
theorem source_alternatingSix_hasRecognizedPair {n:ℕ}
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
    Nonempty (N≃*alternatingGroup (Fin 6)) →
      Witnesses.SymplecticFour.HasRecognizedPair T (minimalParabolicMax T hP) V := by
  dsimp only
  intro h6
  obtain ⟨K,_,c,hcopy⟩ := source_alternatingSix_coefficient_copy hF hn T hP hJ L e hmark
    hgen V hVT hVM hVN hr hex h6
  exact Witnesses.SymplecticFour.source_hasRecognizedPair_of_coefficient_copy hF hn T hP hJ L e
    hmark hgen V hVT hVM hVN hr K c hcopy

end CFSG.Quasithin.ChapterE.Structure.SymplecticFour
