module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalKernels
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.LinearCoordinates
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.CartanKernels
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.SuzukiOmega
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.NativeSuzukiChart

/-!
# Original marked endpoint applications of the Ree source root charts

The core quotient of the original whole endpoint carries its whole Borel
onto the source faithful Borel. Consequently an original natural rank-one
marking induces precisely the source marking required by the root-coordinate
construction. The complete Suzuki chart lifts through the original endpoint
map, with its multiplication, its exact simple-root range, and the commuting
faithful-quotient square. The lifted root then has the proved corrected
isomorphism to the native signed fixed root. Specialization to the generated
carrier keeps the literal original map Q.q.

These applications permit an independent original or geometric marked
amalgam and keep HypothesisF11. They require neither finite original ambient
G nor perfectness of the rank-one factor; m = 0 is included. They discharge
the root placement and convention transport used in Fong–Seitz I (3B),
p.13, and II §10, pp.221–222 and230. The common Ree field, remaining (6H),
mixed equations and whole-amalgam/Chapter12 comparison are not established
by this root comparison and remain with this source-construction family.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits) (i : Fin 2)

def originalFaithfulBorel :
    Subgroup (parabolic L S i ⧸ originalPanelKernel (L := L) (S := S) i) :=
  ((commonBorel L S).subgroupOf (parabolic L S i)).map
    (QuotientGroup.mk' (originalPanelKernel (L := L) (S := S) i))

/-- The entire original Borel survives both literal quotient identifications. -/
theorem originalPanelQuotientEquiv_borel :
    (originalFaithfulBorel (L := L) (S := S) i).map
      (originalPanelQuotientEquiv Q e h i).toMonoidHom = quotientBorel Q i := by
  have hc : (originalPanelQuotientEquiv Q e h i).toMonoidHom.comp
      (QuotientGroup.mk' (originalPanelKernel (L := L) (S := S) i)) =
      (QuotientGroup.mk' (panelKernel Q i)).comp (endpoint Q e i).toMonoidHom := by
    ext x
    exact originalPanelQuotientEquiv_mk Q e h i x
  have hb : (endpointBorel Q i).comap (endpoint Q e i).toMonoidHom =
      (commonBorel L S).subgroupOf (parabolic L S i) := endpoint_borel_comap Q e h i
  rw [originalFaithfulBorel, map_map, hc, ← map_map,
    ← hb, map_comap_eq,
    (endpoint Q e i).toMonoidHom.range_eq_top_of_surjective (endpoint Q e i).surjective,
    top_inf_eq]
  rfl

include h in
/-- The actual original panel core is exactly the kernel of the source Cartan root action. -/
theorem originalCartan_centralizer_simpleRoot :
    (Q.tits.B ⊓ Q.tits.N) ⊓ centralizer (simpleRoot Q split i : Set (X ⧸ Q.D)) =
      (Q.tits.B ⊓ Q.tits.N) ⊓
        (originalPanelKernel (L := L) (S := S) i).map (endpointMap Q e i) := by
  rw [originalPanelKernel_image Q e h i]
  exact cartan_centralizer_simpleRoot Q split i

variable {M : Type*} [Group M]

def faithfulModelMarking
    (μ : (parabolic L S i ⧸ originalPanelKernel (L := L) (S := S) i) ≃* M) :
    (Endpoint Q i ⧸ panelKernel Q i) ≃* M :=
  (originalPanelQuotientEquiv Q e h i).symm.trans μ

/-- A naturally marked original rank-one quotient gives the same full source Borel marking. -/
theorem faithfulModelMarking_borel
    (μ : (parabolic L S i ⧸ originalPanelKernel (L := L) (S := S) i) ≃* M)
    (C : Subgroup M)
    (hB : (originalFaithfulBorel (L := L) (S := S) i).map μ.toMonoidHom = C) :
    (quotientBorel Q i).map (faithfulModelMarking Q e h i μ).toMonoidHom = C := by
  rw [← originalPanelQuotientEquiv_borel Q e h i, map_map]
  have he : (faithfulModelMarking Q e h i μ).toMonoidHom.comp
      (originalPanelQuotientEquiv Q e h i).toMonoidHom = μ.toMonoidHom := by
    ext x
    exact congrArg μ ((originalPanelQuotientEquiv Q e h i).symm_apply_apply x)
  rw [he]
  exact hB

variable (m : ℕ)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

/-- The coordinate is in the full original parabolic, without using a perfect local factor. -/
def originalSuzukiParameter (a b : BinaryGaloisField (2*m+1)) : parabolic L S i :=
  originalRootLift Q e split i (suzukiParameter Q split i m μ hB a b)

theorem originalSuzukiParameter_mul (a b c d : BinaryGaloisField (2*m+1)) :
    originalSuzukiParameter Q e split i m μ hB a b * originalSuzukiParameter Q e split i m μ hB c d =
      originalSuzukiParameter Q e split i m μ hB (a+c) (b+d+a*suzukiTits m c) := by
  rw [originalSuzukiParameter, originalSuzukiParameter, ← map_mul, suzukiParameter_mul]
  rfl

/-- The original faithful quotient square preserves the actual two-parameter matrix. -/
theorem originalSuzukiParameter_projection (a b : BinaryGaloisField (2*m+1)) :
    μ (originalPanelQuotientEquiv Q e h i
      (QuotientGroup.mk' (originalPanelKernel (L := L) (S := S) i)
        (originalSuzukiParameter Q e split i m μ hB a b))) =
      (matrixRootPoint m a b : SuzukiMatrixGroup m) := by
  change μ (originalPanelQuotientEquiv Q e h i
    (originalRootProjection Q e split i (suzukiParameter Q split i m μ hB a b))) = _
  rw [originalRootProjection_commutes, suzukiParameter_projection]

/-- Both original endpoint markings retain the same actual simple-root range. -/
theorem originalSuzukiParameter_range : Set.range
    (fun p : BinaryGaloisField (2*m+1) × BinaryGaloisField (2*m+1) =>
      endpointMap Q e i (originalSuzukiParameter Q e split i m μ hB p.1 p.2)) =
      (simpleRoot Q split i : Set (X ⧸ Q.D)) := by
  simp only [originalSuzukiParameter, originalRootLift_image]
  exact suzukiParameter_range Q split i m μ hB

/-- The original endpoint lift of the actual source root is injective. -/
theorem originalRootLift_injective : Function.Injective (originalRootLift Q e split i) :=
  (endpoint Q e i).symm.injective.comp (fun _ _ he =>
    Subtype.ext (congrArg (fun x : Endpoint Q i => (x : X ⧸ Q.D)) he))

/-- The full lifted source root, with its ambient original endpoint embedding. -/
def originalSuzukiRootEquiv (d : ReeF4.LocalBlockInput m) (positive : Bool) :
    (originalRootLift Q e split i).range ≃*
      ReeF4.LocalBlockInput.PairRigidity.simpleBlock d .suzuki positive :=
  (MonoidHom.ofInjective (originalRootLift_injective Q e split i)).symm.trans
    (NativeSuzukiChart.sourceRootEquiv Q split i μ hB d positive)

theorem originalSuzukiRootEquiv_parameter (d : ReeF4.LocalBlockInput m) (positive : Bool)
    (a b : BinaryGaloisField (2*m+1)) :
    originalSuzukiRootEquiv Q e split i m μ hB d positive
      ⟨originalSuzukiParameter Q e split i m μ hB a b,
        ⟨suzukiParameter Q split i m μ hB a b,rfl⟩⟩ =
      NativeSuzukiChart.nativeRootPoint d positive a b := by
  change NativeSuzukiChart.sourceRootEquiv Q split i μ hB d positive
    ((MonoidHom.ofInjective (originalRootLift_injective Q e split i)).symm
      ((MonoidHom.ofInjective (originalRootLift_injective Q e split i))
        (suzukiParameter Q split i m μ hB a b))) = _
  rw [MulEquiv.symm_apply_apply, NativeSuzukiChart.sourceRootEquiv_parameter]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

@[expose] public noncomputable section
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The original generated carrier uses the same quotient map Q.q on every coordinate. -/
theorem originalSuzukiParameter_quotient (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (i : Fin 2) (m : ℕ)
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
    (hB : (quotientBorel Q i).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
    (a b : BinaryGaloisField (2*m+1)) :
    Q.q ⟨originalSuzukiParameter Q (originalMarkedIso Q) split i m μ hB a b,
      parabolic_le_generated i (originalSuzukiParameter Q (originalMarkedIso Q) split i m μ hB a b).property⟩ =
      (suzukiParameter Q split i m μ hB a b : (generated L S) ⧸ Q.D) :=
  originalRootLift_quotient Q split i (suzukiParameter Q split i m μ hB a b)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
