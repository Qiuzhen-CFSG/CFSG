module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.RootActors
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Source.NormalGeneration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.FourApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.FiveApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryPresentation.SourceBorelCells

/-!
# Whole-source generation and full endpoint placements

The original F.1.1 normal-generation argument, including nonperfect local
factors, makes the actual Weyl-root span the entire quotient. Hence U and
any two lifts of the marked reflections generate Y. This discharges global
generation for the unitary source maps once their positive ranges have been
constructed; no root-field compatibility or perfectness is substituted.

The same four maps and a map onto the entire Cartan give the entire Borel.
Adding the corresponding reflection gives either whole original endpoint,
with the literal quotient map Q.q. In particular, full endpoint placement
needs no independently supplied parabolic equality. Construction of the
source field, actors, equivariant modules and full Cartan parametrization
remains with this source-reconstruction family.

Source: Fong--Seitz I §1 and §3; II §§8B--C; AS F.1.1--3; DGS Theorem D.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootGeneration
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}

/-- The actual root span is the entire same quotient, also for nonperfect endpoints. -/
theorem marked_weylRootSpan_eq_top
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam)
    (h : HypothesisF11 L S) (split : SplitData Q.tits) : weylRootSpan Q split = ⊤ := by
  rw [weylRootSpan_eq_unipotentClosure, SplitData.unipotentClosure_eq_normalClosure]
  exact A2Source.unipotent_normalClosure_eq_top Q e h split

/-- The same conclusion holds with a geometric or original quotient marking. -/
theorem marked_generate_of_unipotent_and_lifts
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam)
    (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (n : Fin 2 → Q.tits.N)
    (hn : ∀ i, QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) (n i) = Q.simple i)
    (K : Subgroup (X ⧸ Q.D)) (hU : split.U ≤ K) (hK : ∀ i, (n i : X ⧸ Q.D) ∈ K) : K = ⊤ := by
  apply top_unique
  rw [← marked_weylRootSpan_eq_top Q e h split]
  exact weylRootSpan_le_of_unipotent_and_lifts Q split n hn K hU hK

variable (Q : SourceQuotient L S) (split : SplitData Q.tits)
variable (n : Fin 2 → Q.tits.N)
variable (hn : ∀ i, QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) (n i) = Q.simple i)

/-- The root actor is inside the literal Q.q-image of the corresponding original endpoint. -/
theorem original_rootActor_le_endpoint (i : Fin 2) :
    rootActor Q split i ≤ ((parabolic L S i).subgroupOf (generated L S)).map Q.q := by
  rw [Q.parabolic_image]
  exact rootActor_le_endpoint Q split i

include split hn

/-- The original Sylow image and any two marked Weyl lifts generate the whole Y. -/
theorem originalS_and_lifts_generate (h : HypothesisF11 L S) :
    (S.subgroupOf (generated L S)).map Q.q ⊔
      closure (Set.range (fun i => (n i : (generated L S) ⧸ Q.D))) = ⊤ := by
  apply marked_generate_of_unipotent_and_lifts Q (originalMarkedIso Q) h split n hn
  · rw [quotient_sourceS_image_eq_unipotent h Q split]
    exact le_sup_left
  · intro i
    exact mem_sup_right (subset_closure (Set.mem_range_self i))

variable {RA RD RC RB : Type*} [Group RA] [Group RD] [Group RC] [Group RB]
variable (r : PositiveMaps ((generated L S) ⧸ Q.D) RA RD RC RB)

/-- The four positive maps, together with two source Weyl lifts, generate Y. -/
theorem positive_and_lifts_generate (h : HypothesisF11 L S) (b : Bool)
    (hroots : orderedRoots Q split b (rotationOrder Q) =
      [r.A.range,r.D.range,r.C.range,r.B.range]) :
    r.generated ⊔ closure (Set.range (fun i => (n i : (generated L S) ⧸ Q.D))) = ⊤ := by
  rw [positive_generated_eq_unipotent Q split r b hroots]
  rw [← quotient_sourceS_image_eq_unipotent h Q split]
  exact originalS_and_lifts_generate Q split n hn h

/-- Full Borel and both full endpoint equalities follow from positive
placement and surjectivity onto the actual full Cartan. -/
theorem original_full_placements {H : Type*} [Group H]
    (h : HypothesisF11 L S) (hU : r.generated = split.U)
    (cartan : H →* ((generated L S) ⧸ Q.D))
    (hcartan : cartan.range = Q.tits.B ⊓ Q.tits.N) :
    r.borel cartan = ((commonBorel L S).subgroupOf (generated L S)).map Q.q ∧
    ∀ i, r.borel cartan ⊔ closure ({(n i : (generated L S) ⧸ Q.D)} : Set _) =
      ((parabolic L S i).subgroupOf (generated L S)).map Q.q := by
  have hB : r.borel cartan = Q.tits.B := by
    change r.generated ⊔ cartan.range = Q.tits.B
    rw [hU, hcartan, split.factorization]
  constructor
  · rw [hB, ← Q.borel_image]
    change ((parabolic L S 0 ⊓ parabolic L S 1).subgroupOf (generated L S)).map Q.q = _
    rw [lemma_F_1_3_6 h]
  · intro i
    rw [hB, Q.parabolic_image, endpoint_eq_borel_sup_lift Q i (n i) (hn i)]

/-- Actual tensor-root ranges discharge U-generation and hence whole-Y
generation, with no perfectness or small-field exclusion. -/
theorem four_tensor_and_lifts_generate {E : Type*} [Field E]
    (σ : E ≃+* E) (hσ : Function.Involutive σ)
    (l : Matrix.SpecialLinearGroup (Fin 2) E →* ((generated L S) ⧸ Q.D))
    (v : Multiplicative (FourTensor.Core E σ hσ) →* ((generated L S) ⧸ Q.D))
    (h : HypothesisF11 L S) (i : Fin 2)
    (hA : (FourTensor.roots E σ hσ l v).A.range = simpleRoot Q split i)
    (hV : v.range = simpleRemainder Q split i) :
    (FourTensor.roots E σ hσ l v).generated ⊔
      closure (Set.range (fun j => (n j : (generated L S) ⧸ Q.D))) = ⊤ := by
  rw [four_generated_eq_unipotent Q split σ hσ l v i hA hV]
  rw [← quotient_sourceS_image_eq_unipotent h Q split]
  exact originalS_and_lifts_generate Q split n hn h

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
