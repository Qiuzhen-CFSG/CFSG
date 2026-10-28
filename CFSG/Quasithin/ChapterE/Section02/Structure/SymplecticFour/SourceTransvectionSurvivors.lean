module
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceTransvectionCatalogue
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceSL2SocleExclusion
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceSuzukiSocleExclusion
public import CFSG.Quasithin.ChapterG.Section04.NativeTransvectionRecognition.NativeModels

/-!
# The two surviving original transvection-socle carriers

The original SQTK hypothesis supplies the full catalogue on the same embedded
simple socle. One actual c2 witness applies the degree-four native inspection.
The source geometry excludes the PSL2 and A5 rows by their invariant quadratic
forms, and the given transvection normalizer excludes Suzuki by the square
obstruction. Exactly A6 and binary PSp4 remain. The c2 witness is retained
explicitly for its independent source producer; this is a carrier reduction,
not yet a literal coefficient-model identification.
Source: Aschbacher--Smith G.4.1, printed p.342.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate TransvectionRecognition
open ChapterB InvolutionTypes Theory.GroupTheory
open ChapterG.Section04.NativeTransvectionRecognition
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- Under the independent literal c2 witness, the original socle is A6 or
binary PSp4. Every other native row is discharged by original hypotheses. -/
theorem source_transvection_socle_alternatingSix_or_symplectic {n:ℕ}
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
    (∃i:N,IsC2 (i:Sp F)) →
      Nonempty (N≃*alternatingGroup (Fin 6)) ∨
      ∃f:ℕ,2≤f ∧ ClassicalGroup.IsPSp N 2 (2^f) := by
  dsimp only
  intro hc2
  obtain ⟨hm,hns⟩ := source_transvection_simple_socle_image_catalogue hF hn hG T hP hJ
    L e hmark hgen V hVT hVM hVN hr hex
  obtain ⟨i,hi⟩ := hc2
  rcases subgroup_native_of_one_isC2 hF _ hns hm i hi with h5|h6|⟨f,_,hlin⟩|⟨m,hm,hsz⟩|hsp
  · exact (source_transvection_socle_not_alternatingFive hF hn T hP hJ L e hmark hgen
      V hVT hVM hVN hr hex h5).elim
  · exact .inl h6
  · exact (source_transvection_socle_not_isPSL hF hn T hP hJ L e hmark hgen
      V hVT hVM hVN hr hex f hlin).elim
  · exact (source_transvection_socle_not_suzuki hF hn T hP hJ L e hmark hgen
      V hVT hVM hVN hr hex hm hsz).elim
  · exact .inr hsp

end CFSG.Quasithin.ChapterE.Structure.SymplecticFour
