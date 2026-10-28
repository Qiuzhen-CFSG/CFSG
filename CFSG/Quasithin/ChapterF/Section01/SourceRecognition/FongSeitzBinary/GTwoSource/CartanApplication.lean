module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.BinaryCartan
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.GTwoSource.ReflectionApplication

/-!
# Exact source Cartan factors and Borel--Weyl maps at both original endpoints

Pull the reflection-aligned diagonal maps back through the supplied
original/geometric amalgam isomorphism. Their ranges are exactly the
pullbacks of the SAME H ∩ R_i, and both coroot slices of the constructed
Borel--Weyl datum satisfy the literal endpoint squares. The source normal
generation hypothesis gives actual generation of the finite quotient.

The published G2Presentation.Positive consumer is applied to these six
root maps and retains the original S and both endpoint representative
equations. For SourceQuotient, the coroot and positive squares use Q.q
itself. No universal-to-original descent is assumed.

In the binary case the full Cartan's commutativity is now proved from the
root coordinates and core-free Borel. The new datum has the actual full
Borel and satisfies the braid and torus equations. For larger fields,
full Cartan commutativity remains explicit. In ALL cases the orthogonal
centralization and PartialPositiveData are still premises to discharge
from the source module argument; no complete 6E(a) -> 9A recognition is
claimed by this conditional application.

Source: Fong--Seitz II §7, (7D), (9A), printed pp.192,194--196,211--217.
The earlier local-section/kernel and normal-generation/core-freeness inputs
retain their source producers and final source-assembly discharge. The
natural/tensor reconstruction and remaining equations remain with this
source-family owner, including q=2 and q=4.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Theory.PSL2.SemilinearCoverage
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open Atlas.G2.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.GTwoSource.CartanPositive
variable {G X F : Type*} [Group G] [Group X] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)

/-- The actual source Cartan factor pulled back through the specified endpoint. -/
def originalCartan (i : Fin 2) : Subgroup (parabolic L S i) :=
  ((Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split i).comap (MarkedLocal.endpointMap Q e i)

/-- The diagonal matrices in the whole original endpoint pinning. -/
def originalTorusHom (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) (n : RootReflection Q split i) :
    Fˣ →* parabolic L S i :=
  (MarkedLocal.originalRankOne Q e split i).subtype.comp
    ((ReflectionPositive.originalPinning Q split e i hV μ n).toMonoidHom.comp
      (BenderSuzuki.Converse.torHom F))

theorem originalTorusHom_endpoint (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) (n : RootReflection Q split i) (a : Fˣ) :
    MarkedLocal.endpointMap Q e i (originalTorusHom Q split e i hV μ n a) =
      alignedTorus Q split i hV μ n a :=
  ReflectionPositive.originalPinning_endpoint Q split e i hV μ n (tor a)

/-- The parameterization covers exactly H ∩ R_i at this original endpoint. -/
theorem originalTorusHom_range (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) (n : RootReflection Q split i) :
    (originalTorusHom Q split e i hV μ n).range = originalCartan Q split e i := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    change MarkedLocal.endpointMap Q e i (originalTorusHom Q split e i hV μ n a) ∈
      (Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split i
    rw [originalTorusHom_endpoint, ← alignedTorusHom_range Q split i hV μ n]
    exact ⟨a,rfl⟩
  · intro hx
    change MarkedLocal.endpointMap Q e i x ∈ (Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split i at hx
    obtain ⟨a,ha⟩ := exists_alignedTorus_of_mem Q split i hV μ n hx.1 hx.2
    refine ⟨a, ?_⟩
    apply (Q.tits.standardParabolic {Q.simple i}).subtype_injective.comp
      (MarkedLocal.endpoint Q e i).injective
    exact (originalTorusHom_endpoint Q split e i hV μ n a).trans ha

variable (hm : rotationOrder Q = 6)
  (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))
  (n : ∀ i, RootReflection Q split i) (short : Fin 2)
  (hH : IsMulCommutative ↥(Q.tits.B ⊓ Q.tits.N))

include hm in
/-- The maps meet the literal source generator and placement clauses.
The full Cartan's abelianness and source normal generation remain explicit. -/
theorem quotient_maps (hgen : split.unipotentClosure = ⊤) :
    let d := sourceBorelWeyl Q split hK μ n short hH
    d.toPositiveRoots.generated = split.U ∧ d.x 0 1 ≠ 1 ∧ d.whole = ⊤ ∧
    d.torus.range ≤ Q.tits.B ⊓ Q.tits.N ∧
    d.s ∈ Q.tits.standardParabolic {Q.simple short} ∧
    d.r ∈ Q.tits.standardParabolic {Q.simple (1-short)} := by
  refine ⟨sourceBorelWeyl_positive Q split hK μ n short hH hm,
    sourceBorelWeyl_highest Q split hK μ n short hH,
    sourceBorelWeyl_whole Q split hK μ n short hH hm hgen, ?_,
    (sourceReflection_placements Q split n short).1,
    (sourceReflection_placements Q split n short).2⟩
  rintro x ⟨p,rfl⟩
  exact alignedPairTorus_mem Q split hK μ n short hH p

/-- Both coroot slices of the new datum use the original endpoint maps. -/
theorem torus_slices :
    (∀ a : Fˣ, MarkedLocal.endpointMap Q e short
      (originalTorusHom Q split e short (hK short) (μ short) (n short) a) =
        (sourceBorelWeyl Q split hK μ n short hH).torus (a,a⁻¹)) ∧
    (∀ a : Fˣ, MarkedLocal.endpointMap Q e (1-short)
      (originalTorusHom Q split e (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) a) =
        (sourceBorelWeyl Q split hK μ n short hH).torus (1,a)) := by
  constructor <;> intro a
  · rw [originalTorusHom_endpoint]
    exact (alignedPairTorus_short Q split hK μ n short hH a).symm
  · rw [originalTorusHom_endpoint]
    exact (alignedPairTorus_long Q split hK μ n short hH a).symm

variable
  (hc : rankOne Q split short ≤ centralizer (positiveCarrier Q split short 0 : Set (X ⧸ Q.D)))
  (d₀ : PartialPositiveData (sourceBorelWeyl Q split hK μ n short hH).toPositiveRoots)
  (h : HypothesisF11 L S)

/-- Apply the published positive presentation to these maps, on the original S.
The undisposed lower module equations are d₀, and orthogonal centralization is hc. -/
theorem positive_marked_application :
    Function.Surjective (ReflectionPositive.sourceSylowHom Q split e hm hK μ n short hc d₀ h) ∧
    ∀ (i : Fin 2) (a : Fin 6 → F),
      let s := ReflectionPositive.sourceSylowHom Q split e hm hK μ n short hc d₀ h
        (Atlas.G2.unipotentEquiv a)
      MarkedLocal.endpointMap Q e i
        ⟨s, (show S ≤ parabolic L S i from le_sup_right.trans le_sup_left) s.property⟩ =
          (sourceBorelWeyl Q split hK μ n short hH).product a :=
  ⟨ReflectionPositive.sourceSylowHom_surjective Q split e hm hK μ n short hc d₀ h,
    ReflectionPositive.sourceSylowHom_endpoint Q split e hm hK μ n short hc d₀ h⟩


section Binary
variable (hF : Nat.card F = 2) (hcore : Q.tits.B.normalCore = ⊥)

/-- At q=2 no Cartan commutativity premise is needed, and the full Borel and
braid are recovered in the same quotient. Positive equations remain separate. -/
theorem binary_quotient_maps (hgen : split.unipotentClosure = ⊤) :
    let d := binarySourceBorelWeyl Q split hK μ n short hm hF hcore
    d.toPositiveRoots.generated = split.U ∧ d.x 0 1 ≠ 1 ∧ d.whole = ⊤ ∧
    d.borel = Q.tits.B ∧ (d.r*d.s)^6 = 1 ∧
    d.s ∈ Q.tits.standardParabolic {Q.simple short} ∧
    d.r ∈ Q.tits.standardParabolic {Q.simple (1-short)} := by
  obtain ⟨hU,hA,hW,_,hs,hr⟩ := quotient_maps Q split hm hK μ n short
    (binaryCartanCommutative Q split hK μ n short hm hF hcore) hgen
  exact ⟨hU,hA,hW,binarySourceBorelWeyl_borel Q split hK μ n short hm hF hcore,
    binarySourceBorelWeyl_braid Q split hK μ n short hm hF hcore,hs,hr⟩

/-- The positive consumer at q=2 retains both original endpoints with the
constructed binary Cartan. The outstanding mixed-module input is explicit. -/
theorem binary_positive_marked_application
    (db : PartialPositiveData (binarySourceBorelWeyl Q split hK μ n short hm hF hcore).toPositiveRoots) :
    Function.Surjective (ReflectionPositive.sourceSylowHom Q split e hm hK μ n short hc db h) ∧
    ∀ (i : Fin 2) (a : Fin 6 → F),
      let s := ReflectionPositive.sourceSylowHom Q split e hm hK μ n short hc db h
        (Atlas.G2.unipotentEquiv a)
      MarkedLocal.endpointMap Q e i
        ⟨s, (show S ≤ parabolic L S i from le_sup_right.trans le_sup_left) s.property⟩ =
          (binarySourceBorelWeyl Q split hK μ n short hm hF hcore).product a :=
  positive_marked_application Q split e hm hK μ n short
    (binaryCartanCommutative Q split hK μ n short hm hF hcore) hc db h
end Binary

section Original
variable (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)

theorem originalTorusHom_quotient (i : Fin 2)
    (hV : simpleRemainder Q₀ split₀ i ≤ localKernel Q₀ i)
    (μ₀ : localGroup Q₀ split₀ i ≃* PSL(2,F)) (n₀ : RootReflection Q₀ split₀ i) (a : Fˣ) :
    let t := originalTorusHom Q₀ split₀ (originalMarkedIso Q₀) i hV μ₀ n₀ a
    Q₀.q ⟨t,parabolic_le_generated i t.property⟩ = alignedTorus Q₀ split₀ i hV μ₀ n₀ a := by
  dsimp only
  exact (original_endpointMap_apply Q₀ i
    (originalTorusHom Q₀ split₀ (originalMarkedIso Q₀) i hV μ₀ n₀ a)).symm.trans
      (originalTorusHom_endpoint Q₀ split₀ (originalMarkedIso Q₀) i hV μ₀ n₀ a)

variable (hm₀ : rotationOrder Q₀ = 6)
  (hK₀ : ∀ i, simpleRemainder Q₀ split₀ i ≤ localKernel Q₀ i)
  (μ₀ : ∀ i, localGroup Q₀ split₀ i ≃* PSL(2,F))
  (n₀ : ∀ i, RootReflection Q₀ split₀ i)
  (hH₀ : IsMulCommutative ↥(Q₀.tits.B ⊓ Q₀.tits.N))
  (hc₀ : rankOne Q₀ split₀ short ≤ centralizer (positiveCarrier Q₀ split₀ short 0 : Set _))
  (d₁ : PartialPositiveData (sourceBorelWeyl Q₀ split₀ hK₀ μ₀ n₀ short hH₀).toPositiveRoots)

/-- The positive map and the two coroot maps retain the SAME original quotient. -/
theorem positive_original_quotient (u : Atlas.G2.unipotent (K := F)) :
    let s := ReflectionPositive.sourceSylowHom Q₀ split₀ (originalMarkedIso Q₀)
      hm₀ hK₀ μ₀ n₀ short hc₀ d₁ h u
    Q₀.q ⟨s, (show S ≤ generated L S from le_sup_right) s.property⟩ =
      (sourceBorelWeyl Q₀ split₀ hK₀ μ₀ n₀ short hH₀).toPositiveRoots.unipotentHom
        (aligned_positive_relations Q₀ split₀ hK₀ μ₀ n₀ short hc₀ d₁).collection u :=
  ReflectionPositive.sourceSylowHom_original_quotient short h Q₀ split₀ hm₀ hK₀ μ₀ n₀ hc₀ d₁ u
end Original
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.GTwoSource.CartanPositive
