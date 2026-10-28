module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.CubicMovement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalSmallCharacteristic
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalMixedBounds

/-!
# Original endpoint and quotient witnesses for positive cubic movement

The original endpoint equivalence carries O2(P_i), its derived subgroup,
and both Frattini denominators to the same source radical sections. Thus
the marked original Suzuki parameter u(1,0) has an actual triple commutator
outside each original denominator. Hypothesis F.1.1 supplies the required
self-centralization of the endpoint two-core.

The last two theorems retain the literal generated-carrier quotient Q.q
on the parameter, witness, and all commutators. Either endpoint orientation
is allowed and the original ambient group need not be finite. Natural panel
markings and the independent-field size comparison remain explicit; the
positive perpendicular-support argument and full (6H) assembly are not
asserted here. The existing binary near-commutator theorem is unchanged.

Source: Fong--Seitz I (1973), pp.52--53, the cubic movement used in the
positive-parameter proof of (6H)(b).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal
variable {G X F : Type*} [Group G] [Group X] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (split : SplitData Q.tits) (i j : Fin 2)
  (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL(2,F))
  (T : Sylow 2 PSL(2,F))
  (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set PSL(2,F)))
  (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

include ν hC μ hB in
/-- The original marked root moves the original two-core cubically modulo its Frattini subgroup. -/
theorem original_positive_radical_cubic_movement (hmpos : 0 < m)
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : Nat.card F ≤ 2^(2*m+1)) :
    let O := pCore 2 (parabolic L S i)
    let u := originalSuzukiParameter Q e split i m μ hB 1 0
    ∃ v : O, ⁅u,⁅u,⁅u,(v : parabolic L S i)⁆⁆⁆ ∉ (frattini O).map O.subtype := by
  dsimp only
  let hV := marked_suzuki_remainder_le_kernel Q split i m μ hB
  obtain ⟨v,hv⟩ := source_positive_radical_cubic_movement Q split i j ν T hC m μ hB
    hmpos (parabolic_core_selfCentralizing Q e h i) hm hij hsize
  obtain ⟨w,rfl⟩ := (originalRadicalEquiv Q e split i hV).surjective v
  refine ⟨w,?_⟩
  rintro ⟨a,ha,hea⟩
  apply hv
  have hp := (originalPhiRadicalEquiv Q e split i hV ⟨a,ha⟩).property
  change endpointMap Q e i a.val ∈ (frattini (simpleRemainder Q split i)).map
    (simpleRemainder Q split i).subtype at hp
  change a.val = _ at hea
  rw [hea] at hp
  simpa only [map_commutatorElement,originalSuzukiParameter,originalRootLift_image,
    originalRadicalEquiv_apply] using hp

include ν hC μ hB in
/-- The same literal original root has cubic movement on the derived two-core section. -/
theorem original_positive_derived_cubic_movement (hmpos : 0 < m)
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : Nat.card F ≤ 2^(2*m+1)) :
    let O := pCore 2 (parabolic L S i)
    let D := commutator O
    let u := originalSuzukiParameter Q e split i m μ hB 1 0
    ∃ v : D, ⁅u,⁅u,⁅u,(v.val : parabolic L S i)⁆⁆⁆ ∉
      (frattini D).map (O.subtype.comp D.subtype) := by
  dsimp only
  let hV := marked_suzuki_remainder_le_kernel Q split i m μ hB
  obtain ⟨v,hv⟩ := source_positive_derived_cubic_movement Q split i j ν T hC m μ hB
    hmpos (parabolic_core_selfCentralizing Q e h i) hm hij hsize
  obtain ⟨w,rfl⟩ := (originalDerivedRadicalEquiv Q e split i hV).surjective v
  refine ⟨w,?_⟩
  rintro ⟨a,ha,hea⟩
  apply hv
  have hp := (originalDerivedPhiEquiv Q e split i hV ⟨a,ha⟩).property
  change endpointMap Q e i a.val.val ∈ _ at hp
  change a.val.val = _ at hea
  rw [hea] at hp
  simpa only [map_commutatorElement,originalSuzukiParameter,originalRootLift_image,
    originalDerivedRadicalEquiv_apply] using hp

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {G F : Type*} [Group G] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits) (i j : Fin 2)
  (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL(2,F))
  (T : Sylow 2 PSL(2,F))
  (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set PSL(2,F)))
  (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

include ν hC μ hB in
/-- The radical witness and all three commutators use the original generated quotient map. -/
theorem original_positive_radical_cubic_quotient (hmpos : 0 < m)
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : Nat.card F ≤ 2^(2*m+1)) :
    let u := originalSuzukiGeneratedParameter Q split i m μ hB 1 0
    ∃ v : pCore 2 (parabolic L S i),
      Q.q ⁅u,⁅u,⁅u,⟨v.val,parabolic_le_generated i v.val.property⟩⁆⁆⁆ ∉
        (frattini (simpleRemainder Q split i)).map (simpleRemainder Q split i).subtype := by
  dsimp only
  let hV := marked_suzuki_remainder_le_kernel Q split i m μ hB
  obtain ⟨v,hv⟩ := source_positive_radical_cubic_movement Q split i j ν T hC m μ hB
    hmpos (MarkedLocal.parabolic_core_selfCentralizing Q (originalMarkedIso Q) h i) hm hij hsize
  obtain ⟨w,rfl⟩ := (originalRadicalEquiv Q (originalMarkedIso Q) split i hV).surjective v
  refine ⟨w,?_⟩
  simpa only [map_commutatorElement,originalSuzukiGeneratedParameter_quotient,
    originalRadicalEquiv_quotient] using hv

include ν hC μ hB in
/-- The derived witness retains the same literal Q.q and the correct derived Frattini denominator. -/
theorem original_positive_derived_cubic_quotient (hmpos : 0 < m)
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : Nat.card F ≤ 2^(2*m+1)) :
    let D : Subgroup ((generated L S) ⧸ Q.D) := ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆
    let u := originalSuzukiGeneratedParameter Q split i m μ hB 1 0
    ∃ v : commutator (pCore 2 (parabolic L S i)),
      Q.q ⁅u,⁅u,⁅u,⟨v.val.val,parabolic_le_generated i v.val.val.property⟩⁆⁆⁆ ∉
        (frattini D).map D.subtype := by
  dsimp only
  let hV := marked_suzuki_remainder_le_kernel Q split i m μ hB
  obtain ⟨v,hv⟩ := source_positive_derived_cubic_movement Q split i j ν T hC m μ hB
    hmpos (MarkedLocal.parabolic_core_selfCentralizing Q (originalMarkedIso Q) h i) hm hij hsize
  obtain ⟨w,rfl⟩ := (originalDerivedRadicalEquiv Q (originalMarkedIso Q) split i hV).surjective v
  refine ⟨w,?_⟩
  simpa only [map_commutatorElement,originalSuzukiGeneratedParameter_quotient,
    originalDerivedRadicalEquiv_quotient] using hv

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
