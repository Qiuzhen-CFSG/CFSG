module
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceNonrootReduction
public import CFSG.Quasithin.ChapterG.Section04.NativeTransvectionRecognition.NativeModels
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.SymplecticFour.AbsolutelyIrreducible
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.SL2Quadratic
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceQuadraticExclusion
/-!
# The complete root-free original symplectic witness

Apply the inherited genuine simple-socle catalogue to the same original pair.
The completed native inspection removes every exceptional row, the explicit
centralizer obstruction removes PSp4, and the A6 source geometry removes A6.
The original central directions make the entire pair absolutely irreducible;
therefore a binary PSL2 carrier would preserve a compatible quadratic form,
contrary to the proved source geometry. The surviving Suzuki pair has the
original Sylow/Borel markings and supplies the required recognized witness.

Every source, model, outer-extension and marking premise is discharged except
the displayed condition selecting this root-free branch. This is the all-c2
paragraph of Aschbacher--Smith E.2.7, printed pp.220--221. The separate root-
containing coefficient-copy branch remains with its independent source owner.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate InvolutionTypes
open Witnesses.SymplecticFour
open ChapterG.Section04.NativeTransvectionRecognition
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- Original E.2.7 marked witness in the branch with no root involutions.
No model, action, absolute-irreducibility or Borel premise is retained. -/
theorem source_nonroot_hasRecognizedPair {n : ℕ}
    (hF : Nat.card F=2^n) (hn : 1<n)
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hJ : ChapterB.minimalParabolicCore T hP=⊥)
    (L : Subgroup G) [L.Normal] [IsSimpleGroup L] (e : Sp F≃*L)
    (hmark : (T : Subgroup G).comap (L.subtype.comp e.toMonoidHom)=unipotent)
    (hgen : L⊔(T : Subgroup G)=⊤)
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hVT : V≤T)
    (hVM : V≤(ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hVN : (T : Subgroup G)≤normalizer (V : Set G)) (hr : 2<Nat.card V)
    (hnr : ∀ g ∈ oppositePair (V.comap (L.subtype.comp e.toMonoidHom)),
      ¬IsRootElement g) :
    HasRecognizedPair T (ChapterB.minimalParabolicMax T hP) V := by
  let W := V.comap (L.subtype.comp e.toMonoidHom)
  let P := oppositePair W
  let I := generalizedFitting P
  rcases source_nonroot_recognized_or_binary_or_exceptional hF hn hG T hP hJ L e hmark
      hgen V hVT hVM hVN hr hnr with h|⟨r,hrank,⟨a⟩⟩|hex
  · exact h
  · have ha := source_original_pair_absolutelyIrreducible hF hn T hP hJ L e hmark hgen
      V hVT hVM hVN hr
    obtain ⟨Q,hpolar,hQ⟩ := TransvectionRecognition.exists_quadratic_of_psl2_subgroup
      P ha a r (GaloisField.card 2 r (by omega))
    exact (source_geometry_quadratic_exclusion hF hn T hP hJ L e hmark hgen
      V hVT hVM hVN hr Q hpolar (fun g hg => hQ ⟨g,hg⟩)).elim
  · let j : I →* Sp F := P.subtype.comp I.subtype
    have hj : Function.Injective j := P.subtype_injective.comp I.subtype_injective
    rcases hex with ⟨r,hr,hm⟩|⟨m,_,hm⟩|hm
    · exact (not_binary_triality_model (by omega) j hj hm).elim
    · exact (not_ree_model m j hj hm).elim
    · exact (not_tits_model j hj hm).elim
end CFSG.Quasithin.ChapterE.Structure.SymplecticFour
