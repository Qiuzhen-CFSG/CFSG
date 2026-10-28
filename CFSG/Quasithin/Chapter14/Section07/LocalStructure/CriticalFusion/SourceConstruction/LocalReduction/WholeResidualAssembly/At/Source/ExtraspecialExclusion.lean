module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourClassical
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.LocalAction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Alternating.NaturalRecognition
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Source.FourGroupStructure
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourOrdinary
public import Theory.SpecificGroups.PSL4Two.SchurMultiplier
public import Theory.SpecificGroups.SU3.BinaryCubicRankParity
public import Theory.SpecificGroups.SU3.EvenSemilinear.CyclicOuter
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourSpan
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourModelExclusions
public import Theory.Mathieu.M11.Properties.ThreeInvolutions
public import Theory.Mathieu.SmallModuleRanks.M12
public import Theory.Mathieu.M22.Properties.TwoRank
public import Theory.Mathieu.M23.Properties.TwoRank
public import Theory.Mathieu.SmallModuleRanks.M24
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.AutomorphismRankBound
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.TwoRank
public import Theory.SpecificGroups.Held.TwoRank.Intrinsic
public import Theory.SpecificGroups.Rudvalis.Model.TwoRankSix
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.Core
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Second
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.Reduction
public import Theory.GroupAction.SylowFixedCentralQuotient
public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Theory.SpecificGroups.PSL2.OddAutomorphismRank
public import Theory.SpecificGroups.OddThreeRank
public import Theory.SpecificGroups.SU3.EvenTwoRank
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourRee
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.SolvableSylowThreeFree
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourTriality
public import Theory.SpecificGroups.Triality.LocalHeisenbergExclusion
public import Theory.SpecificGroups.Triality.StandardTwoRank.RankTable
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourCentralizers
public import Theory.SpecificGroups.PSL3.LargeInvolutionPrime
public import Theory.SpecificGroups.SU3.LargeInvolutionPrime
public import Theory.SpecificGroups.Tits.SylowFixedPrime
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourTI
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialExclusion
public import CFSG.Quasithin.ChapterI.Section06To08.TIConjugates
public import Theory.GroupAction.FourthPowerFixed
public import Theory.Representation.BinaryConjugationSection.DualHyperplanes
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableThreeCore
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LocalOvergroups
public import Theory.GroupTheory.Fitting.CyclicThreeSylow
public import Theory.GroupTheory.PResidual.NormalThreeLift
public import CFSG.Quasithin.ChapterA.Section01.RankActions.Supercritical
public import Theory.GroupTheory.PGroup.SupercriticalExistence

/-!
# Guarded extraspecial exclusion

This unit collects the indicated original source arguments at the same G,T.
Each constituent overview records its proof and source; the universal exports
remain unchanged. The larger unit avoids repeated loading of the common source
imports. Public mathematical statements and literal subgroup maps are retained.
-/

/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Classical model exclusions for the original ordinary component

The literal quotient action of the escaping involution centralizer contains
an injective ternary Heisenberg group inside its solvable subgroup of odd
index. Rank-one automorphism bounds exclude binary PSL₂ and even-degree
PSU₃. Solvable Sylow control excludes Sp₄ and G₂ in every nonbinary field.
The small derived G₂ model is excluded using the exact residual marking;
the small alternating and binary linear models are excluded by their actual
automorphism orders. All comparisons use isomorphisms of B/O₂(B), including
central covers, and the final theorem applies the model calculations to the
original flag and component without additional action premises.

Source: Aschbacher–Smith 14.7.26, printed p.1053, refs/quasithin.pdf.
The remaining ordinary models, centralizer containment and TI are not
asserted here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open ClassificationModels Chapter1.Section02.LocalModels
open Chapter15.Section03.Candidates.ComponentStructure
private theorem ExtraspecialFourClassical_transport_rankTwo_exclusion
    {Q W : Type*} [Group Q] [Finite Q] [Group W] [Finite W] (e : Q ≃* W)
    (exclude : ∀ (A : Subgroup (MulAut W)), MulAut.innerSubgroup W ≤ A →
      primeRank 3 A ≤ 2 → ∀ J : Subgroup A, Group.IsSolvable J → Odd J.index →
      ∀ f : HeisenbergPrime 3 →* A, Function.Injective f → (∀ y, f y ∈ J) → False)
    (A : Subgroup (MulAut Q)) (hA : MulAut.innerSubgroup Q ≤ A)
    (hr : primeRank 3 A ≤ 2) (J : Subgroup A) (hs : Group.IsSolvable J) (ho : Odd J.index)
    (f : HeisenbergPrime 3 →* A) (hf : Function.Injective f) (hJ : ∀ y, f y ∈ J) : False := by
  let ea := MulAut.congr e
  let A' := A.map ea.toMonoidHom
  let eA : A ≃* A' := ea.subgroupMap A
  let J' := J.map eA.toMonoidHom
  have hA' : MulAut.innerSubgroup W ≤ A' := by
    rw [←MulAut.map_innerSubgroup_congr e]
    exact map_mono hA
  have hr' : primeRank 3 A' ≤ 2 := (primeRank_equiv 3 eA).symm ▸ hr
  let := hs
  have hs' : Group.IsSolvable J' := Group.isSolvable_of_surjective
    (eA.toMonoidHom.subgroupMap_surjective J)
  have ho' : Odd J'.index := (index_map_of_bijective (f := eA.toMonoidHom) eA.bijective J).symm ▸ ho
  exact exclude A' hA' hr' J' hs' ho' (eA.toMonoidHom.comp f) (eA.injective.comp hf)
    (fun y => mem_map_of_mem _ (hJ y))


private theorem ExtraspecialFourClassical_binary_linear_action_false {Q : Type*} [Group Q] [Finite Q]
    (f : HeisenbergPrime 3 →* MulAut Q) (hf : Function.Injective f)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL Q n 2) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  rcases hn with rfl | rfl
  · exact HeisenbergPrime.SmallAutomorphismExclusions.no_alternating_action
      (by omega : 8 = 5 ∨ 8 = 6 ∨ 8 = 7 ∨ 8 = 8)
      (e.trans (Matrix.PSL4Two.binaryEquivAlternatingEight F hF)) f hf
  · let : Fintype F := Fintype.ofFinite F
    let k : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
      simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
    let q := (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 5)).trans
      (BinaryLinear.OuterCyclic.slEquivLinear 5).symm
    exact HeisenbergPrime.SmallAutomorphismExclusions.no_binary_five_action
      (e.trans ((Atlas.fieldEquivPSL 5 k).trans q)) f hf

private theorem ExtraspecialFourClassical_binary_rankOne_action_false {Q : Type*} [Group Q] [Finite Q]
    (f : HeisenbergPrime 3 →* MulAut Q) (hf : Function.Injective f)
    {n : ℕ} (hm : ClassicalGroup.IsPSL Q 2 (2^n)) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let c := MulAut.congr (e.trans (BenderSuzuki.ZD.Linear.sl2QuotientEquiv F).symm)
  exact Matrix.SL2.no_heisenberg_automorphism_action
    (c.toMonoidHom.comp f) (c.injective.comp hf)

private theorem ExtraspecialFourClassical_binary_unitary_even_action_false {Q : Type*} [Group Q] [Finite Q]
    [IsSimpleGroup Q] [Group.IsPerfect Q]
    (f : HeisenbergPrime 3 →* MulAut Q) (hf : Function.Injective f)
    {n : ℕ} (hn : 2 ≤ n) (hne : Even n) (hm : ClassicalGroup.IsPSU Q 3 (2^n)) : False := by
  obtain ⟨F,_,_,J,hF,hJ,⟨e⟩⟩ := hm
  let : IsSimpleGroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    e.symm.isSimpleGroup
  let : Group.IsPerfect (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let : IsCyclic (MulAut.Outer (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)) :=
    BenderSuzuki.MatrixGroups.HermitianForm.EvenSemilinear.outer_isCyclic_of_even J (by omega) hne hF hJ
  apply HeisenbergPrime.no_faithful_action_of_rank_one
    Subgroup.center_eq_bot_of_simple_perfect
    (BenderSuzuki.MatrixGroups.HermitianForm.BinaryCubicRankParity.rank_le_one_of_even J (by omega) hF hJ hne)
    ((default : Sylow 3 (MulAut.Outer (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J))).primeRank_le_one_of_isCyclic inferInstance)
    ((MulAut.congr e).toMonoidHom.comp f) ((MulAut.congr e).injective.comp hf)

private theorem ExtraspecialFourClassical_rankTwo_action_false {Q : Type*} [Group Q] [Finite Q]
    (A : Subgroup (MulAut Q)) (hA : MulAut.innerSubgroup Q ≤ A)
    (hr : primeRank 3 A ≤ 2) (J : Subgroup A) (hs : Group.IsSolvable J) (ho : Odd J.index)
    (f : HeisenbergPrime 3 →* A) (hf : Function.Injective f) (hJ : ∀ y, f y ∈ J)
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSp Q 2 (2^n) ∨ IsG2At Q (2^n)) : False := by
  have hq : 2 < 2^n := by
    calc
      2 < 2^2 := by decide
      _ ≤ 2^n := Nat.pow_le_pow_right (by decide) hn
  rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩
  · let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    apply ExtraspecialFourClassical_transport_rankTwo_exclusion
      (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)
      ?_ A hA hr J hs ho f hf hJ
    intro A hA hr J hs ho f hf hJ
    let := hs
    exact HeisenbergPrime.BinaryRankTwoExclusions.symplectic hF (by omega)
      (hF.symm ▸ hq) A hA hr J ho f hf hJ
  · let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    apply ExtraspecialFourClassical_transport_rankTwo_exclusion e ?_ A hA hr J hs ho f hf hJ
    intro A hA hr J hs ho f hf hJ
    let := hs
    exact HeisenbergPrime.BinaryRankTwoExclusions.g2 (hF.symm ▸ hq) A hA hr J ho f hf hJ

open Representation Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterI.Section06To08
open scoped IsMulCommutative Pointwise commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Classical quotient rows excluded by the actual original Heisenberg action
and its solvable subgroup of odd index. No action-image hypothesis is added. -/
theorem extraspecial_four_ordinary_quotient_exclusions
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (B : Subgroup (centralizer ({x} : Set G)))
    (hB : IsComponent (centralizer ({x} : Set G)) B) :
    let Q := B ⧸ pCore 2 B
    (∀ n, ¬ ClassicalGroup.IsPSL Q 2 (2^n)) ∧
    (∀ n, 2 ≤ n → ¬ ClassicalGroup.IsPSp Q 2 (2^n)) ∧
    (∀ n, 2 ≤ n → ¬ IsG2At Q (2^n)) ∧
    ¬ Nonempty (Q ≃* commutator (Atlas.G2.Model (ZMod 2))) ∧
    (∀ n, n = 4 ∨ n = 5 → ¬ ClassicalGroup.IsPSL Q n 2) ∧
    (∀ n, 2 ≤ n → Even n → ¬ ClassicalGroup.IsPSU Q 3 (2^n)) ∧
    (∀ n, n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 → ¬ IsAlternating Q n) := by
  obtain ⟨hn,ha⟩ := extraspecial_four_ordinary_action
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  let := hn
  obtain ⟨_,hi,hr,hs,ho,hres,f,hf,hfJ⟩ := ha
  let a := normalQuotientAction B (pCore 2 B)
  let f' := a.range.subtype.comp f
  have hf' : Function.Injective f' := Subtype.val_injective.comp hf
  let : IsSimpleGroup (B ⧸ pCore 2 B) := (extraspecial_four_ordinary_structure
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB).2.2.2.2.1
  let : IsQuasisimple B := hB.2
  let : Group.IsPerfect (B ⧸ pCore 2 B) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (pCore 2 B)) (QuotientGroup.mk'_surjective _)
  refine ⟨fun _ hm => ExtraspecialFourClassical_binary_rankOne_action_false f' hf' hm,
    fun _ hn hm => ExtraspecialFourClassical_rankTwo_action_false _ hi hr _ hs ho f hf hfJ hn (Or.inl hm),
    fun _ hn hm => ExtraspecialFourClassical_rankTwo_action_false _ hi hr _ hs ho f hf hfJ hn (Or.inr hm),
    ?_, fun _ hn hm => ExtraspecialFourClassical_binary_linear_action_false f' hf' hn hm,
    fun _ hn he hm => ExtraspecialFourClassical_binary_unitary_even_action_false f' hf' hn he hm, ?_⟩
  · rintro ⟨e⟩
    exact Atlas.G2.BinaryLocalResidual.no_odd_index_heisenberg e _ hi _ ho hres
  · rintro n hn ⟨e⟩
    exact HeisenbergPrime.SmallAutomorphismExclusions.no_alternating_action hn e f' hf'

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The original span embeds in the ordinary-component quotient

The original normal point residual L₁ contains U and lies in every ordinary
component B of the escaping involution centralizer. If an element of U dies
in B/O₂(B), it is central in B and hence centralizes O₂(L₁). The original
core pairing places it in V₁. The nonidentity generator of V₁ cannot be
central in B: its ambient centralizer lies in H, whereas B escapes H.
Thus the literal map U → B → B/O₂(B) is injective. Since U is elementary
abelian of order 128, this gives two-rank at least seven in that same quotient.

Source: Aschbacher–Smith 14.7.16, 14.7.21 and 14.7.26, printed
pp.1048–1053, refs/quasithin.pdf. This uses the original ambient flag;
it is not an assertion about arbitrary intrinsic Heisenberg actions.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open ClassificationModels Chapter1.Section02.LocalModels
open Chapter15.Section03.Candidates.ComponentStructure

open Representation Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterI.Section06To08
open scoped IsMulCommutative Pointwise commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original order-128 span embeds through the literal ordinary-component
quotient: its intersection with the central two-core is trivial. -/
theorem extraspecial_four_ordinary_span_embedding
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (B : Subgroup (centralizer ({x} : Set G)))
    (hB : IsComponent (centralizer ({x} : Set G)) B) :
    ∃ i : F.U →* B, (∀ u, ((i u : centralizer ({x} : Set G)) : G) = u) ∧
      Function.Injective ((QuotientGroup.mk' (pCore 2 B)).comp i) := by
  classical
  let C := centralizer ({x} : Set G)
  have hst := extraspecial_four_ordinary_structure
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  have hLB := hst.2.1
  have hzB := hst.2.2.2.1
  obtain ⟨hn,_,_⟩ := extraspecial_source_reduction h hab structural previous he
  have hUB := (U_le_pointResidual_of_normal h hn).trans hLB
  have hUC : F.U ≤ C := hUB.trans (map_subtype_le B)
  let i : F.U →* B := (inclusion hUC).codRestrict B (by
    intro u
    obtain ⟨b,hb,heq⟩ := hUB u.property
    exact (show b = inclusion hUC u from Subtype.ext heq) ▸ hb)
  have hival (u : F.U) : ((i u : C) : G) = u := rfl
  obtain ⟨_,_,z,hzo,hzp,P,_,h115⟩ := extraspecial_four_centralizer_source_setup
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
  obtain ⟨_,houtB,_⟩ := Chapter1.lemma_1_1_5_three_knownSimple d.qtke C P F.H z h115 B hB
  obtain ⟨e⟩ := he
  have hfix := extraspecial_point_core_centralizer h hab structural previous
    ((HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm)
    ((Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3)))
    ((Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2)))
  refine ⟨i,hival,?_⟩
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro u hu
  have huZ : i u ∈ center B := by
    rw [hzB]
    exact (QuotientGroup.eq_one_iff _).mp hu
  have huC : (u : G) ∈ centralizer ((F.Li L 1).pCoreIn 2 : Set G) := by
    intro y hy
    obtain ⟨b,hb,rfl⟩ := hLB (pCoreIn_le 2 (F.Li L 1) hy)
    exact congrArg (fun b : B => ((b : C) : G)) (mem_center_iff.mp huZ ⟨b,hb⟩)
  have huV : (u : G) ∈ F.Vi 1 := hfix ▸ (show (u : G) ∈
    F.U ⊓ centralizer ((F.Li L 1).pCoreIn 2 : Set G) from ⟨u.property,huC⟩)
  rw [←hzp,mem_zpowers_iff_mem_range_orderOf,hzo] at huV
  obtain ⟨n,hn,heq⟩ := Finset.mem_image.mp huV
  have hn2 : n < 2 := Finset.mem_range.mp hn
  interval_cases n
  · exact mem_bot.mpr (Subtype.ext (by simpa using heq.symm))
  · have huz : (u : G) = z := by simpa using heq.symm
    apply (houtB ?_).elim
    rintro _ ⟨b,hb,rfl⟩
    apply h115.centralizer_le
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg (fun b : B => ((b : C) : G)) (mem_center_iff.mp huZ ⟨b,hb⟩)
    change (b : G) * (u : G) = (u : G) * (b : G) at hh
    change (b : G) * z = z * (b : G)
    simpa only [huz] using hh

/-- The actual ordinary-component quotient has two-rank at least seven. -/
theorem extraspecial_four_ordinary_twoRank
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (B : Subgroup (centralizer ({x} : Set G)))
    (hB : IsComponent (centralizer ({x} : Set G)) B) :
    7 ≤ primeRank 2 (B ⧸ pCore 2 B) := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨i,_,hi⟩ := extraspecial_four_ordinary_span_embedding
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  let j := (QuotientGroup.mk' (pCore 2 B)).comp i
  let : IsElementaryAbelian 2 j.range := IsElementaryAbelian.of_surjective
    j.rangeRestrict j.rangeRestrict_surjective
  have hc : Nat.card j.range = 2^7 :=
    (Nat.card_congr (MonoidHom.ofInjective hi).toEquiv).symm.trans
      (extraspecial_source_reduction h hab structural previous he).2.1
  exact IsElementaryAbelian.primeRank_ge_of_card j.range hc

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Model reduction for the actual extraspecial ordinary component

The embedded original elementary span of order 128 excludes every small
sporadic row, the odd-characteristic rows, and both central two-covers in
1.1.5. For J₄, the actual inner involution centralizers have order divisible
by seven. Fixed-point lifting through the original central cover forces
seven into its fixed subgroup, which embeds in the original {2,3}-group H.
The intrinsic J₄ calculation and fixed-cover argument are adapted from
`Source/ResidualFusion/FixedCentralizers/Quasisimple/Recognition/Sporadic/SevenPrimes.lean`;
no Data or recognition conclusion is assumed here.

The full 1.1.5 case split now leaves only binary PSL₃ with even exponent at
least four, binary PSU₃ with odd exponent at least seven, triality, Ree F₄
and Tits quotients. The original Heisenberg action supplies the linear
parity restriction. All alternatives describe the literal B/O₂(B), and
the final application retains the original normal component, point-residual
inclusion, movement and marked inner involution. These five remaining
families, centralizer containment and TI are not asserted to be excluded.

Source: Aschbacher–Smith, 14.7.26, printed p.1053, refs/quasithin.pdf;
1.1.5(3), printed pp.501–503; GLS3 Table 5.3i for the J₄ centralizers.
Imported concrete model proofs retain their source attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open ClassificationModels Chapter1.Section02.LocalModels
open Chapter15.Section03.Candidates.ComponentStructure
private theorem ExtraspecialFourModelExclusions_fixed_card_conj {A : Type*} [Group A] {x y : A} (h : IsConj x y) :
    Nat.card (MulAut.conj x).fixedSubgroup = Nat.card (MulAut.conj y).fixedSubgroup := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have he := Nat.card_congr (MulAut.fixedSubgroupCongr (MulAut.conj c) (MulAut.conj x)).toEquiv
  rw [MulAut.congr_conj] at he
  exact he.trans (congrArg (fun z : A => Nat.card (MulAut.conj z).fixedSubgroup) hc)

private theorem ExtraspecialFourModelExclusions_j4_seven [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model] (y : Janko4.Model) (hy : orderOf (MulAut.conj y) = 2) :
    7 ∣ Nat.card (MulAut.conj y).fixedSubgroup := by
  have ho : orderOf y = 2 := (MulAut.conj_orderOf_of_center_eq_bot Subgroup.center_eq_bot_of_simple_perfect y).symm.trans hy
  have hfirst : 7 ∣ Nat.card (MulAut.conj Janko4.a).fixedSubgroup := by
    rw [MulAut.fixedSubgroup_conj, Janko4.OuterReduction.OddIndex.modelCentralizer_card]
    norm_num
  have hseed : 7 ∣ Nat.card
      (MulAut.conj (Janko4.InvolutionCentralizers.Second.seed : Janko4.Model)).fixedSubgroup := by
    rw [MulAut.fixedSubgroup_conj]
    change 7 ∣ Nat.card Janko4.InvolutionCentralizers.Second.ambientCentralizer
    rw [Janko4.InvolutionCentralizers.Second.ambient_card]
    norm_num
  have hsecond : 7 ∣ Nat.card
      (MulAut.conj ((Janko4.a * Janko4.b * Janko4.a * Janko4.b * Janko4.b) ^ 5)).fixedSubgroup := by
    obtain ⟨c, hc⟩ := Janko4.Simplicity.Max1Fusion.seed_fuses_second
      Janko4.matrixA_mul_self Janko4.matrixB_pow_four
    have hw : Janko4.Simplicity.word
        (Janko4.Simplicity.a Janko4.matrixA_mul_self)
        (Janko4.Simplicity.b Janko4.matrixB_pow_four) "ababb" =
        Janko4.a * Janko4.b * Janko4.a * Janko4.b * Janko4.b := by
      change Janko4.Simplicity.word Janko4.a Janko4.b "ababb" = _
      simp [Janko4.Simplicity.word, mul_assoc]
    rw [hw] at hc
    have hf := ExtraspecialFourModelExclusions_fixed_card_conj (isConj_iff.mpr ⟨c, hc.symm⟩)
    exact hf ▸ hseed
  rcases Janko4.OuterReduction.involution_isConj_of_max1_odd_index
    Janko4.OuterReduction.max1_odd_index_unconditional ho with h | h
  · exact ExtraspecialFourModelExclusions_fixed_card_conj h ▸ hfirst
  · exact ExtraspecialFourModelExclusions_fixed_card_conj h ▸ hsecond

private theorem ExtraspecialFourModelExclusions_seven_of_cover {A B : Type*} [Group A] [Finite A] [Group B]
    (f : PerfectCentralCovering.Cover A B) (α : MulAut A) (hα : TwoCentralInner α)
    (hseven : ∀ y : B, orderOf (MulAut.conj y) = 2 →
      7 ∣ Nat.card (MulAut.conj y).fixedSubgroup) :
    7 ∣ Nat.card α.fixedSubgroup := by
  let := f.isPerfect
  obtain ⟨⟨x, hx⟩, ho, P, hP⟩ := hα
  let β := MulAut.conj (f.toMonoidHom x)
  have heq (a : A) : f.toMonoidHom (α a) = β (f.toMonoidHom a) := by
    rw [← hx]
    simp only [β, MulAut.conj_apply, map_mul, map_inv]
  have ha2 : α ^ 2 = 1 := ho ▸ pow_orderOf_eq_one α
  have hb2 : β ^ 2 = 1 := by
    ext b
    obtain ⟨a, rfl⟩ := f.surjective b
    change β (β (f.toMonoidHom a)) = f.toMonoidHom a
    rw [← heq, ← heq]
    exact congrArg f.toMonoidHom (show α (α a) = a from
      DFunLike.congr_fun ha2 a)
  have hbne : β ≠ 1 := by
    intro hb
    have ha : α = 1 := MulAut.eq_one_of_central_displacement α (fun a => by
      apply f.ker_le_center
      rw [MonoidHom.mem_ker, map_mul, map_inv, heq, hb, MulAut.one_apply, inv_mul_cancel])
    rw [ha, orderOf_one] at ho
    contradiction
  have hb : orderOf β = 2 := orderOf_eq_prime hb2 hbne
  have hsurj := MulAut.fixedSubgroupMap_surjective_of_sylow_fixed α β f.toMonoidHom
    f.surjective f.ker_le_center heq ha2 P (fun a ha => hP ⟨a, ha⟩)
  exact (hseven _ hb).trans (card_dvd_of_surjective _ hsurj)


private theorem ExtraspecialFourModelExclusions_small_sporadic_rank (name : SporadicName)
    [Finite name.Carrier] [IsSimpleGroup name.Carrier] [Group.IsPerfect name.Carrier]
    (h3 : name ≠ .j3) (h4 : name ≠ .j4) : primeRank 2 name.Carrier ≤ 6 := by
  have hi : primeRank 2 name.Carrier ≤ primeRank 2 (MulAut name.Carrier) :=
    _root_.primeRank_le_of_injective 2 MulAut.conj
      (MulAut.conj_injective_of_center_eq_bot Subgroup.center_eq_bot_of_simple_perfect)
  cases name with
  | m11 => exact hi.trans (Sporadic.Mathieu.m11_automorphism_twoRank_le_two.trans (by decide))
  | m12 => exact Sporadic.Mathieu.m12_twoRank_le_three.trans (by decide)
  | m22 => exact Sporadic.Mathieu.m22_twoRank_le_four.trans (by decide)
  | m23 => exact Sporadic.Mathieu.m23_twoRank_le_four.trans (by decide)
  | m24 => exact Sporadic.Mathieu.m24_twoRank_le_six
  | j2 => exact hi.trans Sporadic.LeechRelated.J2.automorphism_primeRank_le_six
  | j3 => exact (h3 rfl).elim
  | j4 => exact (h4 rfl).elim
  | hs => exact Sporadic.LeechRelated.HS.twoRank_le_four.trans (by decide)
  | he => exact Held.primeRank_two_le_six
  | ru => exact Rudvalis.primeRank_le_six

open Representation Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterI.Section06To08
open scoped IsMulCommutative Pointwise commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem ExtraspecialFourModelExclusions_original_fixed_not_seven
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {x : G} (B : Subgroup (centralizer ({x} : Set G)))
    (z : G) (hz : zpowers z = F.Vi 1) (α : MulAut B)
    (ha : ∀ b : B, ((α b : centralizer ({x} : Set G)) : G) = z * (b : G) * z⁻¹) :
    ¬ 7 ∣ Nat.card α.fixedSubgroup := by
  let C := centralizer ({x} : Set G)
  have hm (a : α.fixedSubgroup) : ((a.val : C) : G) ∈ F.H := by
    apply Subgroup.centralizer_le_normalizer (F.Vi 1 : Set G)
    have hα : α a.val = a.val := (MulAut.mem_fixedSubgroup _ _).mp a.property
    have hh : z * (a.val : G) * z⁻¹ = (a.val : G) := by
      rw [←ha,hα]
    have hc : Commute z (a.val : G) := mul_inv_eq_iff_eq_mul.mp hh
    rw [←hz]
    intro y hy
    obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp hy
    exact (hc.zpow_left n).eq
  let f : α.fixedSubgroup →* F.H :=
    (C.subtype.comp (B.subtype.comp α.fixedSubgroup.subtype)).codRestrict F.H hm
  have hf : Function.Injective f := by
    intro a b hh
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun y : F.H => (y : G)) hh
  intro h7
  have hH7 := h7.trans (card_dvd_of_injective f hf)
  have hd := odd_prime_dvd_twoCore_quotient_residual (by decide : Nat.Prime 7) (by decide) hH7
  obtain ⟨e⟩ := he
  rw [Nat.card_congr ((residualStarEquiv F).symm.trans e).toEquiv,HeisenbergPrime.card] at hd
  norm_num at hd

/-- Every sporadic row of the actual 1.1.5 marking is excluded. Small rows
contradict the embedded original U; the J₄ row forces seven in its actual
fixed subgroup, which lies in the original {2,3}-group H. -/
theorem extraspecial_four_ordinary_not_sporadic
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (B : Subgroup (centralizer ({x} : Set G)))
    (hB : IsComponent (centralizer ({x} : Set G)) B)
    (z : G) (hz : zpowers z = F.Vi 1) (α : MulAut B)
    (ha : ∀ b : B, ((α b : centralizer ({x} : Set G)) : G) = z * (b : G) * z⁻¹)
    (ht : TwoCentralInner α) (name : SporadicName) (h3 : name ≠ .j3)
    (e : (B ⧸ pCore 2 B) ≃* name.Carrier) : False := by
  let : IsQuasisimple B := hB.2
  let : IsSimpleGroup (B ⧸ pCore 2 B) := (extraspecial_four_ordinary_structure
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB).2.2.2.2.1
  let : Group.IsPerfect (B ⧸ pCore 2 B) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (pCore 2 B)) (QuotientGroup.mk'_surjective _)
  let : Finite name.Carrier := Finite.of_surjective e e.surjective
  let : IsSimpleGroup name.Carrier := e.symm.isSimpleGroup
  let : Group.IsPerfect name.Carrier := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  have hr := extraspecial_four_ordinary_twoRank
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  rw [primeRank_equiv 2 e] at hr
  by_cases hn : name = .j4
  · subst name
    let e' : (B ⧸ pCore 2 B) ≃* Janko4.Model := e
    let : IsSimpleGroup Janko4.Model := e'.symm.isSimpleGroup
    let : Group.IsPerfect Janko4.Model := Group.IsPerfect.ofSurjective
      (f := e'.toMonoidHom) e'.surjective
    let c : PerfectCentralCovering.Cover B Janko4.Model :=
      { toMonoidHom := e'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B))
        surjective := e'.surjective.comp (QuotientGroup.mk'_surjective _)
        isPerfect := inferInstance
        ker_le_center := by
          rw [MonoidHom.ker_comp_of_injective _ _ e'.injective,QuotientGroup.ker_mk']
          exact IsQuasisimple.pCore_le_center 2 }
    exact ExtraspecialFourModelExclusions_original_fixed_not_seven he B z hz α ha (ExtraspecialFourModelExclusions_seven_of_cover c α ht ExtraspecialFourModelExclusions_j4_seven)
  · have hb := ExtraspecialFourModelExclusions_small_sporadic_rank name h3 hn
    omega
private theorem ExtraspecialFourModelExclusions_binary_three_parameter {Q : Type*} [Group Q] [Finite Q]
    (hr : 7 ≤ primeRank 2 Q)
    (f : HeisenbergPrime 3 →* MulAut Q) (hf : Function.Injective f)
    {n : ℕ} (hn : 1 ≤ n) (hm : ClassicalGroup.IsPSL Q 3 (2^n)) :
    4 ≤ n ∧ Even n := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have hrF : 7 ≤ 2*n := by
    rw [primeRank_equiv 2 e,Matrix.PSL3Even.two_rank F (by omega) hF] at hr
    exact hr
  refine ⟨by omega,Nat.not_odd_iff_even.mp ?_⟩
  intro ho
  have hmod : Nat.card F % 3 = 2 := by
    rw [hF,Nat.BinaryTorusParity.two_pow_mod_three,
      if_neg (by have hh := Nat.odd_iff.mp ho; omega)]
  have hcop : Nat.Coprime 3 (Nat.card F - 1) := by
    apply Nat.prime_three.coprime_iff_not_dvd.mpr
    intro hd
    have hm := Nat.mod_eq_zero_of_dvd hd
    have hpos := Finite.one_lt_card (α := F)
    omega
  have hz : center SL(3,F) = ⊥ := (eq_bot_iff_card _).mpr (by
    rw [Atlas.ExceptionalSupport.card_sl_center]
    simpa only [Fintype.card_fin] using hcop.gcd_eq_one)
  let ep : SL(3,F) ≃* PSL(3,F) := QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hz.symm)
  let ea := MulAut.congr (e.trans ep.symm)
  exact Matrix.SL3.no_heisenberg_automorphism_action (by omega) hF hz
    (ea.toMonoidHom.comp f) (ea.injective.comp hf)

/-- The literal ordinary component cannot belong to either odd-characteristic
row of 1.1.5: its original elementary subgroup has order 128. -/
theorem extraspecial_four_ordinary_not_odd
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (B : Subgroup (centralizer ({x} : Set G)))
    (hB : IsComponent (centralizer ({x} : Set G)) B)
    (hm : ClassicalGroup.IsPSL B 3 3 ∨
      ∃ p, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL B 2 p) : False := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨i,_,hi⟩ := extraspecial_four_ordinary_span_embedding
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  have hii : Function.Injective i := fun a b hh => hi (congrArg (QuotientGroup.mk' _) hh)
  let : IsElementaryAbelian 2 (⊤ : Subgroup F.U) :=
    IsElementaryAbelian.of_injective _ (⊤ : Subgroup F.U).subtype_injective
  have hru : 7 ≤ primeRank 2 F.U :=
    IsElementaryAbelian.primeRank_ge_of_card (⊤ : Subgroup F.U) (by
      simpa only [card_top, Nat.reducePow] using (extraspecial_source_reduction h hab structural previous he).2.1)
  have hr : 7 ≤ primeRank 2 B := hru.trans (_root_.primeRank_le_of_injective 2 i hii)
  rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨p,hp,F,_,_,hF,⟨e⟩⟩
  · rw [primeRank_equiv 2 e] at hr
    have hb := Theory.SpecificGroups.OddThreeRank.psl3_primeRank_two_le
      (by decide : Nat.Prime 3) (by decide) hF
    omega
  · by_cases hp2 : p = 2
    · rcases hp2 with rfl
      let : Fintype F := Fintype.ofFinite F
      have hc : Nat.card (GL (Fin 2) F) = 6 := by
        rw [Matrix.card_GL_field]
        simp only [←Nat.card_eq_fintype_card,hF]
        norm_num
      have hdiv : 128 ∣ Nat.card B := by
        rw [←(extraspecial_source_reduction h hab structural previous he).2.1]
        exact card_dvd_of_injective i hii
      rw [Nat.card_congr e.toEquiv] at hdiv
      have hquot : Nat.card PSL(2,F) ∣ Nat.card SL(2,F) :=
        (center SL(2,F)).card_quotient_dvd_card
      have hSL : Nat.card SL(2,F) ∣ 6 := by
        rw [←hc]
        exact card_dvd_of_injective Matrix.SpecialLinearGroup.toGL
          Matrix.SpecialLinearGroup.toGL_injective
      exact (by decide : ¬128 ∣ 6) (hdiv.trans (hquot.trans hSL))
    · have ho := hp.1.odd_of_ne_two hp2
      let P : Sylow 2 PSL(2,F) := default
      obtain ⟨n,_,⟨en⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F
        ⟨p,1,hp.1,ho,by omega,by simpa using hF⟩ P
      rw [primeRank_equiv 2 e,P.primeRank_eq,primeRank_equiv 2 en] at hr
      have hb := Theory.GroupTheory.dihedral_rank_le_two n
      omega

/-- Neither central two-cover row of 1.1.5 can be the original component. -/
theorem extraspecial_four_ordinary_not_twoCover
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (B : Subgroup (centralizer ({x} : Set G)))
    (hB : IsComponent (centralizer ({x} : Set G)) B)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 3 4 ∨ IsG2At (B ⧸ pCore 2 B) 4) : False := by
  rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | hg
  · have hr := extraspecial_four_ordinary_twoRank
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
    have hb := Matrix.PSL3Even.two_rank F (n := 2) (by decide) hF
    rw [primeRank_equiv 2 e,hb] at hr
    omega
  · exact (extraspecial_four_ordinary_quotient_exclusions
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB).2.2.1
        2 (by decide) hg

/-- The full original 1.1.5 model list leaves only the indicated large linear,
large unitary, triality, Ree and Tits quotients. The bounds and parity refer
to the actual quotient and follow from the original U and Heisenberg actions. -/
theorem extraspecial_four_ordinary_model_reduction
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (B : Subgroup (centralizer ({x} : Set G)))
    (hB : IsComponent (centralizer ({x} : Set G)) B)
    (z : G) (hz : zpowers z = F.Vi 1) (α : MulAut B)
    (ha : ∀ b : B, ((α b : centralizer ({x} : Set G)) : G) = z * (b : G) * z⁻¹)
    (hm : ModelAction115 B α) :
    (∃ n, 4 ≤ n ∧ Even n ∧ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 3 (2^n)) ∨
    (∃ n, 7 ≤ n ∧ Odd n ∧ ClassicalGroup.IsPSU (B ⧸ pCore 2 B) 3 (2^n)) ∨
    (∃ n, 1 ≤ n ∧ Triality.Standard.IsTrialityGroupAt (2^n) (B ⧸ pCore 2 B)) ∨
    (∃ m, 1 ≤ m ∧ IsReeF4At (B ⧸ pCore 2 B) m) ∨
    Nonempty ((B ⧸ pCore 2 B) ≃* Tits.ParrottGroup) := by
  let : IsQuasisimple B := hB.2
  have hs := extraspecial_four_ordinary_structure
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  have hc := hs.2.2.2.1
  have hno := extraspecial_four_ordinary_quotient_exclusions
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  have hr := extraspecial_four_ordinary_twoRank
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  have halt {n : ℕ} (hn : n = 6 ∨ n = 7) (σ : Equiv.Perm (Fin n))
      (hm : AlternatingAction α n σ) : False := by
    rcases hm with ⟨e,_⟩ | ⟨_,⟨ez⟩,_,_⟩
    · have hcenter : center B = ⊥ := (eq_bot_iff_card _).mpr (by
        rw [Nat.card_congr (centerCongr e).toEquiv,
          alternatingGroup.center_eq_bot (by simpa only [Nat.card_fin] using (show 4 ≤ n by omega)),card_bot])
      let eq : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin n) :=
        (QuotientGroup.quotientMulEquivOfEq (hc.symm.trans hcenter)).trans
          (QuotientGroup.quotientBot.trans e)
      exact hno.2.2.2.2.2.2 n (by omega) ⟨eq⟩
    · have hz3 : Nat.card (pCore 2 B) = 3 := by
        rw [←hc,Nat.card_congr ez.toEquiv]
        simp only [Nat.card_eq_fintype_card,Fintype.card_multiplicative,ZMod.card]
      rcases (pCore_isPGroup (p := 2) (G := B)).card_eq_or_dvd with hh | hh
      · omega
      · rw [hz3] at hh
        norm_num at hh
  cases hm with
  | lie hsimple hmodel _ =>
    let : IsSimpleGroup B := hsimple
    have hpc : pCore 2 B = ⊥ := hc.symm.trans Subgroup.center_eq_bot_of_simple_perfect
    let eq : (B ⧸ pCore 2 B) ≃* B :=
      (QuotientGroup.quotientMulEquivOfEq hpc).trans QuotientGroup.quotientBot
    rcases hmodel with hm | hm | ⟨n,hn,hm⟩
    · cases hm with
      | linear n _ hm => exact (hno.1 n (hm.of_mulEquiv eq)).elim
      | unitary n hn hm =>
        have hmQ := hm.of_mulEquiv eq
        have hn7 : 7 ≤ n := by
          obtain ⟨F,_,_,J,hF,hJ,⟨e⟩⟩ := hmQ
          rw [primeRank_equiv 2 e,
            BenderSuzuki.MatrixGroups.HermitianForm.EvenTwoRank.two_rank J (by omega) hF hJ] at hr
          exact hr
        have hodd : Odd n := Nat.not_even_iff_odd.mp (fun heven => hno.2.2.2.2.2.1 n hn heven hmQ)
        exact Or.inr (Or.inl ⟨n,hn7,hodd,hmQ⟩)
      | suzuki m hm iso =>
        exact (extraspecial_four_not_suzuki_component
          d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ B hB
          (by omega) iso.some).elim
    · cases hm with
      | linear n hn hm =>
        obtain ⟨hnA,haA⟩ := extraspecial_four_ordinary_action
          d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
        let := hnA
        obtain ⟨_,_,_,_,_,_,f,hf,_⟩ := haA
        let g := (normalQuotientAction B (pCore 2 B)).range.subtype.comp f
        have hp := ExtraspecialFourModelExclusions_binary_three_parameter hr g (Subtype.val_injective.comp hf) hn (hm.of_mulEquiv eq)
        exact Or.inl ⟨n,hp.1,hp.2,hm.of_mulEquiv eq⟩
      | symplectic n hn hm => exact (hno.2.1 n hn (hm.of_mulEquiv eq)).elim
      | g2 n hn hm => exact (hno.2.2.1 n hn (hm.of_mulEquiv eq)).elim
      | triality n hn hm => exact Or.inr (Or.inr (Or.inl ⟨n,hn,hm.of_mulEquiv eq⟩))
      | ree m hm iso =>
        obtain ⟨r,⟨e⟩⟩ := iso
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m,hm,r,⟨eq.trans e⟩⟩)))
      | symplectic_derived iso =>
        let es := (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := ZMod 2)).symm
        let ed := (es.subgroupMap (commutator (ClassicalGroup.PSp 2 (ZMod 2)))).trans
          (MulEquiv.subgroupCongr (by rw [map_commutator_eq,MonoidHom.range_eq_top.mpr es.surjective]))
        let ea := (eq.trans iso.some).trans (ed.trans
          (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simp)))
        exact (hno.2.2.2.2.2.2 6 (by omega) ⟨ea⟩).elim
      | g2_derived iso => exact (hno.2.2.2.1 ⟨eq.trans iso.some⟩).elim
      | tits iso => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨eq.trans iso.some⟩)))
    · exact (hno.2.2.2.2.1 n hn (hm.of_mulEquiv eq)).elim
  | two_cover _ _ hm _ =>
    exact (extraspecial_four_ordinary_not_twoCover
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB hm).elim
  | six σ _ hm => exact (halt (Or.inl rfl) σ hm).elim
  | seven σ _ hm => exact (halt (Or.inr rfl) σ hm).elim
  | odd hm _ =>
    exact (extraspecial_four_ordinary_not_odd
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB hm).elim
  | sporadic name hn iso ht =>
    exact (extraspecial_four_ordinary_not_sporadic
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
      z hz α ha ht name hn iso.some).elim

/-- Apply the model exclusions to the original escaping centralizer, preserving
its normal component, point-residual inclusion and marked inner involution.
The five remaining quotient families are not yet excluded. -/
theorem extraspecial_four_ordinary_reduced_source
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    : ∃ (B : Subgroup (centralizer ({x} : Set G))) (z : G),
      IsComponent (centralizer ({x} : Set G)) B ∧ B.Normal ∧
      F.Li L 1 ≤ B.map (centralizer ({x} : Set G)).subtype ∧
      orderOf z = 2 ∧ zpowers z = F.Vi 1 ∧
      B.map (centralizer ({x} : Set G)).subtype =
        ⁅B.map (centralizer ({x} : Set G)).subtype,zpowers z⁆ ∧
      ¬ B.map (centralizer ({x} : Set G)).subtype ≤ F.H ∧
      ∃ α : MulAut B, (∀ y : B, ((α y : centralizer ({x} : Set G)) : G) = z * (y : G) * z⁻¹) ∧
        α ∈ (MulAut.conj (G := B)).range ∧
        ModelAction115 B α ∧
        ((∃ n, 4 ≤ n ∧ Even n ∧ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 3 (2^n)) ∨
        (∃ n, 7 ≤ n ∧ Odd n ∧ ClassicalGroup.IsPSU (B ⧸ pCore 2 B) 3 (2^n)) ∨
        (∃ n, 1 ≤ n ∧ Triality.Standard.IsTrialityGroupAt (2^n) (B ⧸ pCore 2 B)) ∨
        (∃ m, 1 ≤ m ∧ IsReeF4At (B ⧸ pCore 2 B) m) ∨
        Nonempty ((B ⧸ pCore 2 B) ≃* Tits.ParrottGroup)) := by
  obtain ⟨B,z,hB,hn,hLB,hz,hzp,hm,houtB,α,ha,hi,hmodel⟩ :=
    extraspecial_four_ordinary_inner_source
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
  exact ⟨B,z,hB,hn,hLB,hz,hzp,hm,houtB,α,ha,hi,hmodel,
    extraspecial_four_ordinary_model_reduction
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
      z hzp α ha hmodel⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Excluding the Ree ordinary component of the extraspecial centralizer

The actual intersection H ∩ B is solvable and contains the restriction of
the original centralizer Sylow subgroup. The normal component contains L₁,
whose cubic two-core quotient makes this intersection's order divisible
by three. The genuine Ree Borel theorem says a solvable full-Sylow overgroup
has order prime to three, also through the literal central two-kernel.
Thus B/O₂(B) cannot be a Ree F₄ model.

The final application retains the original normal component and marked
inner involution, and removes the Ree alternative from the preceding full
1.1.5 reduction. Large linear, large unitary, triality and Tits quotients
remain; this does not assert centralizer containment or TI.

Source: Aschbacher–Smith, 14.7.26, printed p.1053, refs/quasithin.pdf.
The imported Ree calculation retains the root-defined Borel and its source
reference to F.1.12. No Data or final recognition premise is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Representation Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterI.Section06To08 Chapter1.Section02.LocalModels
open Chapter15.Section03.Candidates.ComponentStructure
open scoped IsMulCommutative Pointwise commutatorElement MatrixGroups
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem ExtraspecialFourRee_H_solvable
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    Group.IsSolvable F.H := by
  apply isSolvable_of_prime_dvd_card_eq_two_or_three
  intro p hp hd
  by_cases hp2 : p = 2
  · exact Or.inl hp2
  have hdiv := odd_prime_dvd_twoCore_quotient_residual hp (hp.odd_of_ne_two hp2) hd
  obtain ⟨e⟩ := he
  rw [Nat.card_congr ((residualStarEquiv F).symm.trans e).toEquiv,
    HeisenbergPrime.card] at hdiv
  exact Or.inr (((Nat.dvd_prime Nat.prime_three).mp
    (hp.dvd_of_dvd_pow hdiv)).resolve_left hp.ne_one)

/-- The literal intersection of the original H with B is solvable, contains a
full Sylow two-subgroup of B, and has order divisible by three. -/
theorem extraspecial_four_ordinary_intersection
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (B : Subgroup (centralizer ({x} : Set G)))
    (hB : IsComponent (centralizer ({x} : Set G)) B)
    : let J := F.H.comap ((centralizer ({x} : Set G)).subtype.comp B.subtype)
      Group.IsSolvable J ∧ (∃ P : Sylow 2 B, (P : Subgroup B) ≤ J) ∧
        3 ∣ Nat.card J := by
  let C := centralizer ({x} : Set G)
  let J := F.H.comap (C.subtype.comp B.subtype)
  let : Group.IsSolvable F.H := ExtraspecialFourRee_H_solvable he
  let j : J →* F.H := (C.subtype.comp (B.subtype.comp J.subtype)).codRestrict F.H
    (fun a => a.property)
  have hj : Function.Injective j := by
    intro a b hh
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : F.H => (a : G)) hh
  have hsol : Group.IsSolvable J := Group.isSolvable_of_isSolvable_injective hj
  obtain ⟨hn,hLB,_,_,_,_⟩ := extraspecial_four_ordinary_structure
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  let := hn
  obtain ⟨_,_,_,_,_,P,hP,_⟩ := extraspecial_four_centralizer_source_setup
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
  obtain ⟨Q,hQ⟩ := P.exists_subgroupOf_eq_of_normal B
  have hQJ : (Q : Subgroup B) ≤ J := by
    intro a ha
    rw [hQ] at ha
    have hh : ((a : C) : G) ∈ (T : Subgroup G) ⊓ C :=
      hP ▸ mem_map_of_mem C.subtype ha
    exact F.invariant 1 hh.1
  let eB := B.equivMapOfInjective C.subtype C.subtype_injective
  let k : F.Li L 1 →* B := eB.symm.toMonoidHom.comp (inclusion hLB)
  have hval (a : F.Li L 1) : ((k a : C) : G) = a :=
    congrArg Subtype.val (eB.apply_symm_apply ⟨a,hLB a.property⟩)
  let kJ : F.Li L 1 →* J := k.codRestrict J (fun a => by
    change ((k a : C) : G) ∈ F.H
    rw [hval]
    exact (F.Li_le L 1 a.property).2)
  have hkJ : Function.Injective kJ := by
    intro a b hh
    apply Subtype.ext
    exact (hval a).symm.trans ((congrArg (fun y : J => ((y.val : C) : G)) hh).trans (hval b))
  have h3 : 3 ∣ Nat.card (F.Li L 1) := by
    have hd := (pCore 2 (F.Li L 1)).card_quotient_dvd_card
    rw [pointResidual_core_quotient_card h structural] at hd
    exact hd
  exact ⟨hsol,⟨Q,hQJ⟩,h3.trans (card_dvd_of_injective kJ hkJ)⟩

/-- A Ree quotient is impossible for the actual ordinary component: the original
solvable full-Sylow intersection has a factor of three, whereas Ree Borels do not. -/
theorem extraspecial_four_ordinary_not_ree
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (B : Subgroup (centralizer ({x} : Set G)))
    (hB : IsComponent (centralizer ({x} : Set G)) B)
    {m : ℕ} (hm : 1 ≤ m) (hmodel : IsReeF4At (B ⧸ pCore 2 B) m) : False := by
  obtain ⟨r,⟨e⟩⟩ := hmodel
  let eR := e.trans r.modelEquiv
  let f := eR.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B))
  have hf : Function.Surjective f := eR.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ eR.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  obtain ⟨hsol,⟨P,hPJ⟩,h3⟩ := extraspecial_four_ordinary_intersection
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  have hc := ReeF4.Parabolics.coprime_three_of_solvable_sylow_overgroup_of_two_kernel
    hm f hf hk P _ hsol hPJ
  exact Nat.prime_three.coprime_iff_not_dvd.mp hc h3

/-- The original escaping centralizer now leaves only large linear, large
unitary, triality and Tits quotients; the genuine Ree branch is discharged. -/
theorem extraspecial_four_ordinary_remaining_source
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    : ∃ (B : Subgroup (centralizer ({x} : Set G))) (z : G),
      IsComponent (centralizer ({x} : Set G)) B ∧ B.Normal ∧
      F.Li L 1 ≤ B.map (centralizer ({x} : Set G)).subtype ∧
      orderOf z = 2 ∧ zpowers z = F.Vi 1 ∧
      B.map (centralizer ({x} : Set G)).subtype =
        ⁅B.map (centralizer ({x} : Set G)).subtype,zpowers z⁆ ∧
      ¬ B.map (centralizer ({x} : Set G)).subtype ≤ F.H ∧
      ∃ α : MulAut B, (∀ y : B, ((α y : centralizer ({x} : Set G)) : G) = z * (y : G) * z⁻¹) ∧
        α ∈ (MulAut.conj (G := B)).range ∧
        ModelAction115 B α ∧
        ((∃ n, 4 ≤ n ∧ Even n ∧ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 3 (2^n)) ∨
        (∃ n, 7 ≤ n ∧ Odd n ∧ ClassicalGroup.IsPSU (B ⧸ pCore 2 B) 3 (2^n)) ∨
        (∃ n, 1 ≤ n ∧ Triality.Standard.IsTrialityGroupAt (2^n) (B ⧸ pCore 2 B)) ∨
        Nonempty ((B ⧸ pCore 2 B) ≃* Tits.ParrottGroup)) := by
  obtain ⟨B,z,hB,hn,hLB,hz,hzp,hm,houtB,α,ha,hi,hmodel,hcases⟩ :=
    extraspecial_four_ordinary_reduced_source
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
  refine ⟨B,z,hB,hn,hLB,hz,hzp,hm,houtB,α,ha,hi,hmodel,?_⟩
  rcases hcases with hl | hu | ht | ⟨m,hm,hr⟩ | hT
  · exact Or.inl hl
  · exact Or.inr (Or.inl hu)
  · exact Or.inr (Or.inr (Or.inl ht))
  · exact (extraspecial_four_ordinary_not_ree
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB hm hr).elim
  · exact Or.inr (Or.inr (Or.inr hT))

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Excluding triality in the original extraspecial centralizer

The actual U embeds in B/O₂(B), so that quotient has two-rank at least
seven. The genuine triality rank table excludes the field-order-two
endpoint. For every larger field, the literal quotient action contains
the faithful Heisenberg subgroup inside a solvable subgroup of odd index,
contradicting the intrinsic triality Borel obstruction. The model's
simplicity and perfectness are transported from the original component.

The final source application retains B, L₁, the original marked inner
involution and its movement. Only large binary PSL₃, large binary PSU₃
and Tits quotients remain. Those last alternatives, centralizer containment
and TI remain to be proved; no recognition callback is introduced.

Source: Aschbacher–Smith, 14.7.26, printed p.1053, refs/quasithin.pdf;
GLS3 root geometry for the imported triality calculations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Representation Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterI.Section06To08 Chapter1.Section02.LocalModels
open Chapter15.Section03.Candidates.ComponentStructure
open scoped IsMulCommutative Pointwise commutatorElement MatrixGroups
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem ExtraspecialFourTriality_transport_rankTwo_exclusion
    {Q W : Type*} [Group Q] [Finite Q] [Group W] [Finite W] (e : Q ≃* W)
    (exclude : ∀ (A : Subgroup (MulAut W)), MulAut.innerSubgroup W ≤ A →
      primeRank 3 A ≤ 2 → ∀ J : Subgroup A, Group.IsSolvable J → Odd J.index →
      ∀ f : HeisenbergPrime 3 →* A, Function.Injective f → (∀ y, f y ∈ J) → False)
    (A : Subgroup (MulAut Q)) (hA : MulAut.innerSubgroup Q ≤ A)
    (hr : primeRank 3 A ≤ 2) (J : Subgroup A) (hs : Group.IsSolvable J) (ho : Odd J.index)
    (f : HeisenbergPrime 3 →* A) (hf : Function.Injective f) (hJ : ∀ y, f y ∈ J) : False := by
  let ea := MulAut.congr e
  let A' := A.map ea.toMonoidHom
  let eA : A ≃* A' := ea.subgroupMap A
  let J' := J.map eA.toMonoidHom
  have hA' : MulAut.innerSubgroup W ≤ A' := by
    rw [←MulAut.map_innerSubgroup_congr e]
    exact map_mono hA
  have hr' : primeRank 3 A' ≤ 2 := (primeRank_equiv 3 eA).symm ▸ hr
  let := hs
  have hs' : Group.IsSolvable J' := Group.isSolvable_of_surjective
    (eA.toMonoidHom.subgroupMap_surjective J)
  have ho' : Odd J'.index := (index_map_of_bijective (f := eA.toMonoidHom) eA.bijective J).symm ▸ ho
  exact exclude A' hA' hr' J' hs' ho' (eA.toMonoidHom.comp f) (eA.injective.comp hf)
    (fun y => mem_map_of_mem _ (hJ y))


/-- The actual ordinary component has no triality quotient. Its original span
excludes the binary endpoint; the literal Heisenberg action excludes larger fields. -/
theorem extraspecial_four_ordinary_not_triality
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (B : Subgroup (centralizer ({x} : Set G)))
    (hB : IsComponent (centralizer ({x} : Set G)) B)
    {n : ℕ} (hn : 1 ≤ n)
    (hmodel : Triality.Standard.IsTrialityGroupAt (2^n) (B ⧸ pCore 2 B)) : False := by
  have hr2 := extraspecial_four_ordinary_twoRank
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  have heq := Triality.Standard.TwoRank.twoRank_eq_five_mul_of_model n (by omega) hmodel
  have hn2 : 1 < n := by omega
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ n (by omega)).mp hmodel
  let : IsQuasisimple B := hB.2
  let : IsSimpleGroup (B ⧸ pCore 2 B) := (extraspecial_four_ordinary_structure
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB).2.2.2.2.1
  let : IsSimpleGroup (Triality.Standard.BinaryCarrier n (by omega)) := e.symm.isSimpleGroup
  let : Group.IsPerfect (Triality.Standard.BinaryCarrier n (by omega)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B)))
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
  obtain ⟨hnB,ha⟩ := extraspecial_four_ordinary_action
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  let := hnB
  obtain ⟨_,hi,hr,hs,ho,_,f,hf,hfJ⟩ := ha
  exact ExtraspecialFourTriality_transport_rankTwo_exclusion e (fun A hA hr J hs ho f hf hJ => by
    let := hs
    exact Triality.Standard.LocalHeisenbergExclusion.no_action n hn2 A hA hr J ho f hf hJ)
    _ hi hr _ hs ho f hf hfJ

/-- The original source application now leaves only large linear, large unitary
and Tits quotients; all triality and Ree alternatives have been excluded. -/
theorem extraspecial_four_ordinary_three_family_source
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    : ∃ (B : Subgroup (centralizer ({x} : Set G))) (z : G),
      IsComponent (centralizer ({x} : Set G)) B ∧ B.Normal ∧
      F.Li L 1 ≤ B.map (centralizer ({x} : Set G)).subtype ∧
      orderOf z = 2 ∧ zpowers z = F.Vi 1 ∧
      B.map (centralizer ({x} : Set G)).subtype =
        ⁅B.map (centralizer ({x} : Set G)).subtype,zpowers z⁆ ∧
      ¬ B.map (centralizer ({x} : Set G)).subtype ≤ F.H ∧
      ∃ α : MulAut B, (∀ y : B, ((α y : centralizer ({x} : Set G)) : G) = z * (y : G) * z⁻¹) ∧
        α ∈ (MulAut.conj (G := B)).range ∧
        ModelAction115 B α ∧
        ((∃ n, 4 ≤ n ∧ Even n ∧ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 3 (2^n)) ∨
        (∃ n, 7 ≤ n ∧ Odd n ∧ ClassicalGroup.IsPSU (B ⧸ pCore 2 B) 3 (2^n)) ∨
        Nonempty ((B ⧸ pCore 2 B) ≃* Tits.ParrottGroup)) := by
  obtain ⟨B,z,hB,hn,hLB,hz,hzp,hm,houtB,α,ha,hi,hmodel,hcases⟩ :=
    extraspecial_four_ordinary_remaining_source
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
  refine ⟨B,z,hB,hn,hLB,hz,hzp,hm,houtB,α,ha,hi,hmodel,?_⟩
  rcases hcases with hl | hu | ⟨n,hn,ht⟩ | hT
  · exact Or.inl hl
  · exact Or.inr (Or.inl hu)
  · exact (extraspecial_four_ordinary_not_triality
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB hn ht).elim
  · exact Or.inr (Or.inr hT)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Closing the ordinary-component branch of the outside centralizer

The marked involution fixes a full Sylow two-subgroup of the ordinary component,
since its intersection with the original H contains such a Sylow subgroup.
Fixed points therefore lift through the actual central cover. The large linear
and unitary quotients contribute a prime greater than three in this fixed group.
For Tits the inner representative centralizes a full Sylow subgroup, and its
centralizer has a factor of five. The original fixed subgroup embeds in H,
whose only prime divisors are two and three. This excludes all three remaining
families and proves C_G(x) ≤ H for the original outside involutions.

Source: Aschbacher–Smith 14.7.26, printed pp.1052–1053, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter15.Section03.Candidates.ComponentStructure

private theorem ExtraspecialFourCentralizers_prime_of_cover {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (f : PerfectCentralCovering.Cover A B) (hz : center B = ⊥)
    (α : MulAut A) (hα : TwoCentralInner α)
    (hprime : ∀ y : B, orderOf y = 2 → ∀ P : Sylow 2 B,
      (∀ b ∈ P, Commute y b) → ∃ p : ℕ, p.Prime ∧ 3 < p ∧
        p ∣ Nat.card (centralizer ({y} : Set B))) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ Nat.card α.fixedSubgroup := by
  let := f.isPerfect
  obtain ⟨⟨x,hx⟩,ho,P,hP⟩ := hα
  let y := f.toMonoidHom x
  let β := MulAut.conj y
  have heq (a : A) : f.toMonoidHom (α a) = β (f.toMonoidHom a) := by
    rw [←hx]
    simp only [β,y,MulAut.conj_apply,map_mul,map_inv]
  have ha2 : α^2=1 := ho ▸ pow_orderOf_eq_one α
  have hb2 : β^2=1 := by
    ext b
    obtain ⟨a,rfl⟩ := f.surjective b
    change β (β (f.toMonoidHom a)) = f.toMonoidHom a
    rw [←heq,←heq]
    exact congrArg f.toMonoidHom (show α (α a) = a from DFunLike.congr_fun ha2 a)
  have hbne : β ≠ 1 := by
    intro hb
    have ha : α = 1 := MulAut.eq_one_of_central_displacement α (fun a => by
      apply f.ker_le_center
      rw [MonoidHom.mem_ker,map_mul,map_inv,heq,hb,MulAut.one_apply,inv_mul_cancel])
    rw [ha,orderOf_one] at ho
    contradiction
  have hy : orderOf y = 2 :=
    (MulAut.conj_orderOf_of_center_eq_bot hz y).symm.trans (orderOf_eq_prime hb2 hbne)
  let Q := P.mapSurjective f.surjective
  have hQ (b : B) (hb : b ∈ Q) : Commute y b := by
    obtain ⟨a,ha,rfl⟩ := hb
    have hh := heq a
    rw [hP ⟨a,ha⟩] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh.symm
  obtain ⟨p,hp,hp3,hd⟩ := hprime y hy Q hQ
  have hsurj := MulAut.fixedSubgroupMap_surjective_of_sylow_fixed α β f.toMonoidHom
    f.surjective f.ker_le_center heq ha2 P (fun a ha => hP ⟨a,ha⟩)
  refine ⟨p,hp,hp3,?_⟩
  have hd' : p ∣ Nat.card β.fixedSubgroup := by
    simpa only [β,MulAut.fixedSubgroup_conj] using hd
  exact hd'.trans (card_dvd_of_surjective _ hsurj)

open Representation Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterI.Section06To08
open scoped IsMulCommutative Pointwise commutatorElement MatrixGroups
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem ExtraspecialFourCentralizers_fixed_prime_false
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {x : G} (B : Subgroup (centralizer ({x} : Set G)))
    (z : G) (hz : zpowers z = F.Vi 1) (α : MulAut B)
    (ha : ∀ b : B, ((α b : centralizer ({x} : Set G)) : G) = z * (b : G) * z⁻¹)
    (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) (hd : p ∣ Nat.card α.fixedSubgroup) : False := by
  let C := centralizer ({x} : Set G)
  have hm (a : α.fixedSubgroup) : ((a.val : C) : G) ∈ F.H := by
    rw [F.H_eq_centralizer (by omega) z hz.symm]
    have hα : α a.val = a.val := (MulAut.mem_fixedSubgroup _ _).mp a.property
    have hh : z * (a.val : G) * z⁻¹ = (a.val : G) := by rw [←ha,hα]
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh).symm
  let f : α.fixedSubgroup →* F.H :=
    (C.subtype.comp (B.subtype.comp α.fixedSubgroup.subtype)).codRestrict F.H hm
  have hf : Function.Injective f := by
    intro a b hh
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun y : F.H => (y : G)) hh
  have hdiv := odd_prime_dvd_twoCore_quotient_residual hp (hp.odd_of_ne_two (by omega))
    (hd.trans (card_dvd_of_injective f hf))
  obtain ⟨e⟩ := he
  rw [Nat.card_congr ((residualStarEquiv F).symm.trans e).toEquiv,
    HeisenbergPrime.card] at hdiv
  have hh := hp.dvd_of_dvd_pow hdiv
  have hh' := Nat.le_of_dvd (by decide : 0 < 3) hh
  omega

/-- The actual original inner action fixes a full Sylow subgroup. This supplies
all the hypotheses needed to lift fixed points through the central cover. -/
theorem extraspecial_four_ordinary_twoCentralInner
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (B : Subgroup (centralizer ({x} : Set G)))
    (hB : IsComponent (centralizer ({x} : Set G)) B)
    (z : G) (hzo : orderOf z = 2) (hz : zpowers z = F.Vi 1)
    (houtB : ¬ B.map (centralizer ({x} : Set G)).subtype ≤ F.H)
    (α : MulAut B)
    (ha : ∀ b : B, ((α b : centralizer ({x} : Set G)) : G) = z * (b : G) * z⁻¹)
    (hi : α ∈ (MulAut.conj (G := B)).range) : TwoCentralInner α := by
  let C := centralizer ({x} : Set G)
  have hfix (b : B) (hb : (b : G) ∈ F.H) : α b = b := by
    rw [F.H_eq_centralizer (by omega) z hz.symm] at hb
    apply Subtype.ext
    apply Subtype.ext
    exact (ha b).trans (mul_inv_eq_of_eq_mul (mem_centralizer_singleton_iff.mp hb).symm)
  have hne : α ≠ 1 := by
    intro hh
    apply houtB
    rintro _ ⟨b,hb,rfl⟩
    rw [F.H_eq_centralizer (by omega) z hz.symm]
    have heq := ha ⟨b,hb⟩
    rw [hh,MulAut.one_apply] at heq
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp heq.symm).symm
  have hpow : α^2=1 := by
    have hzpow : z^2=1 := hzo ▸ pow_orderOf_eq_one z
    have hzsq : z*z=1 := by simpa only [pow_two] using hzpow
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    apply Subtype.ext
    change ((α (α b) : C) : G) = (b : G)
    rw [ha,ha]
    calc
      z * (z * (b : G) * z⁻¹) * z⁻¹ = (z*z) * (b : G) * (z*z)⁻¹ := by group
      _ = (b : G) := by rw [hzsq]; simp
  obtain ⟨_,⟨P,hPJ⟩,_⟩ := extraspecial_four_ordinary_intersection
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  exact ⟨hi,orderOf_eq_prime hpow hne,P,fun b => hfix b (hPJ b.property)⟩

/-- The outside involution centralizer lies in the original H. All ordinary
component families are excluded under the original source hypotheses. -/
theorem extraspecial_four_outside_centralizer_le
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    : centralizer ({x} : Set G) ≤ F.H := by
  by_contra hout
  obtain ⟨B,z,hB,hn,hLB,hzo,hz,hmove,houtB,α,ha,hi,hmodel,hcases⟩ :=
    extraspecial_four_ordinary_three_family_source
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
  have ht := extraspecial_four_ordinary_twoCentralInner
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    B hB z hzo hz houtB α ha hi
  let : IsQuasisimple B := hB.2
  let Q := B ⧸ pCore 2 B
  let : IsSimpleGroup Q := (extraspecial_four_ordinary_structure
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB).2.2.2.2.1
  let : Group.IsPerfect Q := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (pCore 2 B)) (QuotientGroup.mk'_surjective _)
  have exclude {W : Type} [Group W] [Finite W] (e : Q ≃* W)
      (hprime : ∀ y : W, orderOf y = 2 → ∀ P : Sylow 2 W,
        (∀ b ∈ P, Commute y b) → ∃ p : ℕ, p.Prime ∧ 3 < p ∧
          p ∣ Nat.card (centralizer ({y} : Set W))) : False := by
    let : IsSimpleGroup W := e.symm.isSimpleGroup
    let : Group.IsPerfect W := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    let c : PerfectCentralCovering.Cover B W :=
      { toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B))
        surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
        isPerfect := inferInstance
        ker_le_center := by
          rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
          exact IsQuasisimple.pCore_le_center 2 }
    obtain ⟨p,hp,hp3,hd⟩ := ExtraspecialFourCentralizers_prime_of_cover c Subgroup.center_eq_bot_of_simple_perfect α ht hprime
    exact ExtraspecialFourCentralizers_fixed_prime_false he B z hz α ha p hp hp3 hd
  rcases hcases with hl | hu | htits
  · obtain ⟨n,hn,heven,k,_,_,hk,⟨e⟩⟩ := hl
    exact exclude e (fun y hy _ _ =>
      Matrix.PSL3.EvenInnerCentralizers.exists_prime_gt_three_dvd_involution_centralizer
        k hn heven hk y hy)
  · obtain ⟨n,hn,hodd,k,_,_,J,hk,hJ,⟨e⟩⟩ := hu
    let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card
      (show Nat.card k = 2^(n*2) by simpa only [pow_mul] using hk)
    have hfixed : Nat.card {a : k // J.conj a = a} = 2^n :=
      FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hk hJ
    exact exclude e (fun y hy _ _ =>
      BenderSuzuki.MatrixGroups.HermitianForm.EvenInvolutionTwoGroup.exists_prime_gt_three_dvd_involution_centralizer
        J (by omega) hodd hk hfixed y hy)
  · obtain ⟨e⟩ := htits
    exact exclude (e.trans Tits.parrottFiniteImageEquiv) (fun y hy P hP =>
      ⟨5,by decide,by decide,Tits.five_dvd_centralizer_of_sylow_fixed y hy P hP⟩)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The original TI subgroup in the extraspecial branch

The cyclic and Sylow-central cases were settled when selecting the central
subgroup of order four. In the remaining elementary case, the original fusion
criterion and the now proved outside-centralizer containment establish TI.
This is 14.7.26, with D containing the marked V₁, lying in Z(K) and T, and
having precisely H as its normalizer. The subsequent weak-closure contradiction
on printed p.1054 is not assumed or asserted here.

Source: Aschbacher–Smith 14.7.25–26, printed pp.1052–1053, refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Subgroup Representation Theory.GroupTheory
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterI.Section06To08
open scoped IsMulCommutative Pointwise commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The actual central order-four subgroup is TI, including the noncentral
 elementary case and retaining its original point and normalizer. -/
theorem extraspecial_center_four_ti
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ∃ D : Subgroup G, F.Vi 1 ≤ D ∧ D ≤ (center (K F)).map (K F).subtype ∧
      Nat.card D = 4 ∧ D ≤ (T : Subgroup G) ∧ normalizer (D : Set G) = F.H ∧
      IsTISubgroup D := by
  obtain ⟨D,hZD,hDK,hcard,hDT,hND,hcases⟩ := extraspecial_center_four_ti_reduction
    d h hab structural previous faithful earlier he
  refine ⟨D,hZD,hDK,hcard,hDT,hND,?_⟩
  rcases hcases with ht | ⟨hele,_,hnc⟩
  · exact ht
  let := hele
  apply (extraspecial_four_ti_iff_centralizer_containment
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc).mpr
  intro x hx hxZ
  exact extraspecial_four_outside_centralizer_le
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Eliminating the original extraspecial residual by weak closure

For the actual central TI subgroup D of order four, every conjugate A lying
in R₁ centralizes U. If A meets U trivially, TI makes all its nonidentity
actors have the same fixed space. The fourth-power fixed-space calculation
makes a moving A elementary. The two-rank bound on R₁* gives a nonidentity
core actor, whose fixed hyperplane is then fixed by all of A. The faithful
extraspecial quotient has no such small actors, so A lies in O₂(H). Its
faithful commutator row would inject four elements into V₁, a contradiction.

If A meets U nontrivially and moves U, TI makes U normalize A. The common
commutator has order at most two, so the same displacement estimate puts A
in O₂(H), and [A,U] = V₁. Since D contains V₁, TI identifies A with D,
which centralizes U because D lies in Z(K) and U lies in K.

Consequently the literal W₀(R₁,D) lies in both O₂(LT) and O₂(H). It is
normal in LT and H and is nontrivial. The unique maximal two-local over LT
therefore contains H, contradicting the original escape property. Both the
K/O₂(K) and O²(H/O₂(H)) formulations use their actual residual comparison.
No source Data or extra local-recognition premise is assumed. The subsequent
solvable-local and component reductions through 14.7.52 remain separate.

Source: Aschbacher–Smith, conclusion of the proof of 14.7.14,
printed p.1054, following 14.7.26; refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Subgroup Representation Theory.GroupTheory
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterI.Section06To08
open scoped IsMulCommutative Pointwise commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem ExtraspecialExclusion_ti_fixed_commutator (A U : Subgroup G) (hTI : IsTISubgroup A)
    (hAU : A ≤ normalizer (U : Set G)) {a : G} (ha : a ∈ A) (hne : a ≠ 1) :
    ⁅U ⊓ centralizer ({a} : Set G), A⁆ ≤ A ⊓ U := by
  refine le_inf (le_normalizer_iff_commutator_le_right.mp
    (inf_le_right.trans (hTI.centralizer_le_normalizer ha hne))) ?_
  exact (commutator_mono inf_le_left le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp hAU)

omit [Finite G] in
private theorem ExtraspecialExclusion_ti_disjoint_fixed (A U : Subgroup G) (hTI : IsTISubgroup A)
    (hAU : A ≤ normalizer (U : Set G)) (hd : Disjoint A U)
    {a : G} (ha : a ∈ A) (hne : a ≠ 1) :
    U ⊓ centralizer ({a} : Set G) ≤ centralizer (A : Set G) := by
  exact commutator_eq_bot_iff_le_centralizer.mp
    (bot_unique ((ExtraspecialExclusion_ti_fixed_commutator A U hTI hAU ha hne).trans hd.le_bot))

private theorem ExtraspecialExclusion_ti_disjoint_elementary (A U : Subgroup G) [IsElementaryAbelian 2 U]
    (hTI : IsTISubgroup A) (hAU : A ≤ normalizer (U : Set G))
    (hd : Disjoint A U) (hcard : Nat.card A = 4)
    (hmove : ¬ A ≤ centralizer (U : Set G)) : IsElementaryAbelian 2 A := by
  let α : A →* MulAut U := U.normalizerMonoidHom.comp (inclusion hAU)
  have hk (a : A) (ha : α a = 1) : a = 1 := by
    by_contra hn
    apply hmove
    apply le_centralizer_iff.mp
    intro v hv
    apply ExtraspecialExclusion_ti_disjoint_fixed A U hTI hAU hd a.property
      (fun he => hn (Subtype.ext he))
    refine ⟨hv, mem_centralizer_singleton_iff.mpr ?_⟩
    have he := congrArg (fun f : MulAut U => (f ⟨v,hv⟩ : G)) ha
    change (a:G)*v*(a:G)⁻¹ = v at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hs (a : A) : a ^ 2 = 1 := by
    by_contra hn
    have hfour : α a ^ 4 = 1 := by
      rw [←map_pow, ←hcard, pow_card_eq_one',map_one]
    have he : FixedPoints.subgroup (zpowers (α a)) U =
        FixedPoints.subgroup (zpowers (α a ^ 2)) U := by
      ext v
      simp only [MulAut.mem_fixed_zpowers_iff]
      constructor
      · intro hv
        change α a (α a v) = v
        rw [hv,hv]
      · intro hv
        have hc : (v:G) ∈ centralizer (A : Set G) := by
          apply ExtraspecialExclusion_ti_disjoint_fixed A U hTI hAU hd (A.pow_mem a.property 2)
            (fun he => hn (Subtype.ext he))
          refine ⟨v.property, mem_centralizer_singleton_iff.mpr ?_⟩
          have he := congrArg (fun v : U => (v:G)) hv
          rw [←map_pow] at he
          change (a:G)^2*(v:G)*((a:G)^2)⁻¹ = v at he
          exact (mul_inv_eq_iff_eq_mul.mp he).symm
        apply Subtype.ext
        change (a:G)*(v:G)*(a:G)⁻¹ = v
        rw [hc a a.property,mul_inv_cancel_right]
    have ha : α a ≠ 1 := fun he => hn (by rw [hk a he,one_pow])
    have hh := MulAut.fixed_card_lt_square_fixed_card_of_fourth_power_eq_one (α a) hfour ha
    rw [he] at hh
    exact (lt_irrefl _ hh)
  exact { toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by simpa using hcard)
          exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }


private theorem ExtraspecialExclusion_rank_one_fourth_actor_trivial
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (P : Subgroup D) [P.Normal] [IsExtraspecial 3 P] (hP : Nat.card P = 27)
    (hexp : Monoid.exponent P = 3)
    (hc : centralizer (P : Set D) ≤ P) (t : D) (ht : t^4=1)
    (hs : BinaryOffender.fixedCodim ρ (zpowers t) ≤ 1) : t=1 := by
  have hcentral : t ∈ centralizer (P : Set D) := by
    intro p hp
    let x : P := ⟨⁅t,p⁆, P.mul_mem ((inferInstance : P.Normal).conj_mem p hp t) (P.inv_mem hp)⟩
    have hx : x=1 := by
      by_contra hn
      have hx3 : orderOf x=3 := orderOf_eq_prime
        (by simpa only [hexp] using Monoid.pow_exponent_eq_one x) hn
      have hlo := (ExtraspecialBinarySix.faithful_cubic_displacement_lower
        (ρ.comp P.subtype) (hf.comp P.subtype_injective) hP x hx3).1
      have hhi := BinaryOffender.fixedCodim_commutator_le_twice ρ t p
      simp only [BinaryOffender.fixedCodim_zpowers_eq_displacement_rank] at hlo hhi hs
      change 4 ≤ Module.finrank (ZMod 2) (ρ (t*p*t⁻¹*p⁻¹) - LinearMap.id).range at hlo
      omega
    exact (commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val hx)).symm
  have ht3 : t^3=1 := congrArg Subtype.val
    (show (⟨t,hc hcentral⟩ : P)^3=1 by
      simpa only [hexp] using Monoid.pow_exponent_eq_one (⟨t,hc hcentral⟩ : P))
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 4 3)
    (orderOf_dvd_of_pow_eq_one ht) (orderOf_dvd_of_pow_eq_one ht3))

variable {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}

private theorem ExtraspecialExclusion_small_actor_in_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (a : F.H) (ha4 : a^4=1)
    (hs : BinaryOffender.fixedCodim ρ (zpowers a) ≤ 1) : (a:G) ∈ F.H.pCoreIn 2 := by
  let : Finite W := Finite.of_surjective (fun u : F.U => (s.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨e⟩ := he
  let P := pResidual 2 (HStar F.H)
  let eP := (residualStarEquiv F).symm.trans e
  let : IsExtraspecial 3 P :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv eP.symm
  have hP : Nat.card P=27 := (Nat.card_congr eP.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent P=3 :=
    (Monoid.exponent_eq_of_mulEquiv eP).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  obtain ⟨σ,hσ⟩ := exists_star_representation h s
  have hf : Function.Injective σ := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 F.H) x
    have hb : b ∈ ρ.ker := by rw [←hσ]; exact hx
    rw [section_action_kernel_eq_core_of_escape h structural (h.flag_escape_at F previous) s] at hb
    exact (QuotientGroup.eq_one_iff _).mpr hb
  have hs' : BinaryOffender.fixedCodim σ (zpowers (starMap F a)) ≤ 1 := by
    rw [BinaryOffender.fixedCodim_zpowers_eq_displacement_rank] at hs ⊢
    change Module.finrank (ZMod 2) ((σ.comp (starMap F)) a-LinearMap.id).range ≤ 1
    rwa [hσ]
  have hx := ExtraspecialExclusion_rank_one_fourth_actor_trivial σ hf P hP hexp
    (Theory.GroupTheory.centralizer_pResidual_le_of_pCore_eq_bot (pCore_quotient_pCore_eq_bot 2))
    (starMap F a) (by rw [←map_pow,ha4,map_one]) hs'
  exact mem_map_of_mem F.H.subtype ((QuotientGroup.eq_one_iff a).mp hx)

omit [Finite G] in
private def ExtraspecialExclusion_centralRow (A Z : Subgroup G) (hZ : Z ≤ centralizer (A : Set G))
    (t : G) (ht : ∀ a ∈ A, ⁅t,a⁆ ∈ Z) : A →* Z where
  toFun a := ⟨⁅t,(a:G)⁆,ht a a.property⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by
    apply Subtype.ext
    change ⁅t,(a:G)*(b:G)⁆ = ⁅t,(a:G)⁆ * ⁅t,(b:G)⁆
    rw [commutatorElement_mul_right_eq_mul_conj]
    calc
      _ = ⁅t,(a:G)⁆ * ((a:G)*⁅t,(b:G)⁆) * (a:G)⁻¹ := by group
      _ = ⁅t,(a:G)⁆ * ⁅t,(b:G)⁆ := by rw [hZ (ht b b.property) a a.property]; group

omit [Finite G] in
private theorem ExtraspecialExclusion_centralRow_ker (A Z : Subgroup G) (hZ : Z ≤ centralizer (A : Set G))
    (t : G) (ht : ∀ a ∈ A, ⁅t,a⁆ ∈ Z) :
    (ExtraspecialExclusion_centralRow A Z hZ t ht).ker = (centralizer ({t} : Set G)).subgroupOf A := by
  ext a
  change (⟨⁅t,(a:G)⁆,ht a a.property⟩ : Z) = 1 ↔ (a:G) ∈ centralizer ({t} : Set G)
  rw [Subtype.ext_iff]
  change ⁅t,(a:G)⁆ = 1 ↔ (a:G) ∈ centralizer ({t}:Set G)
  rw [commutatorElement_eq_one_iff_mul_comm,mem_centralizer_singleton_iff,eq_comm]

private theorem ExtraspecialExclusion_core_element_centralizer_index
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    {b : G} (hb : b ∈ F.H.pCoreIn 2) :
    (F.U ⊓ centralizer ({b} : Set G)).relIndex F.U ≤ 2 := by
  have hZ : F.Vi 1 ≤ centralizer (F.U : Set G) :=
    le_centralizer_iff.mp (s.section_le.trans
      (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))))
  have ht (u : G) (hu : u ∈ F.U) : ⁅b,u⁆ ∈ F.Vi 1 :=
    section_core_commutator_le_point h s (commutator_mem_commutator hb hu)
  let f := ExtraspecialExclusion_centralRow F.U (F.Vi 1) hZ b ht
  have hc := Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective
  have hk := ExtraspecialExclusion_centralRow_ker F.U (F.Vi 1) hZ b ht
  rw [inf_relIndex_left]
  change ((centralizer ({b} : Set G)).subgroupOf F.U).index ≤ 2
  rw [←hk,index_ker]
  exact hc.trans_eq (by simpa using F.card 1 (by decide))

private theorem ExtraspecialExclusion_ti_disjoint_four_le_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (A : Subgroup G) (hA : A ≤ F.Ri L 1) (hc : Nat.card A=4)
    (hTI : IsTISubgroup A) (hd : Disjoint A F.U)
    (hmove : ¬ A ≤ centralizer (F.U : Set G)) : A ≤ F.H.pCoreIn 2 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  have hAH : A ≤ F.H := hA.trans ((pCoreIn_le 2 _).trans
    (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  have hAU := hAH.trans s.normalized
  let := ExtraspecialExclusion_ti_disjoint_elementary A F.U hTI hAU hd hc hmove
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have h27 : Nat.card ((K F) ⧸ pCore 2 (K F))=27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hmeet : A ⊓ F.H.pCoreIn 2 ≠ ⊥ := by
    intro hbot
    let f : A →* HStar F.H := (starMap F).comp (inclusion hAH)
    have hf : Function.Injective f := (MonoidHom.ker_eq_bot_iff _).mp (by
      apply bot_unique
      intro a ha
      have hcore : (a:G) ∈ F.H.pCoreIn 2 :=
        mem_map_of_mem F.H.subtype ((QuotientGroup.eq_one_iff _).mp ha)
      exact Subtype.ext (mem_bot.mp (hbot ▸ (show (a:G) ∈ A ⊓ F.H.pCoreIn 2 from ⟨a.property,hcore⟩))))
    have hr : f.range ≤ star F (F.Ri L 1) := by
      rintro _ ⟨a,rfl⟩
      exact mem_map_of_mem (starMap F) (hA a.property)
    let : IsElementaryAbelian 2 f.range := IsElementaryAbelian.of_surjective
      f.rangeRestrict f.rangeRestrict_surjective
    have hrank := (primeRank_mono 2 hr).trans
      (point_core_rank_one_of_extraspecial_residual h structural hex h27)
    have heq : Nat.card f.range = 4 := (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans hc
    let : IsElementaryAbelian 2 (⊤ : Subgroup f.range) :=
      IsElementaryAbelian.of_injective (⊤ : Subgroup f.range).subtype Subtype.val_injective
    have hb := (primeRank_le_iff_elementary_card_le f.range).mp hrank ⊤ inferInstance
    rw [card_top,heq] at hb
    norm_num at hb
  obtain ⟨⟨b,hb⟩,hbn⟩ := ne_bot_iff_exists_ne_one.mp hmeet
  have hbne : b ≠ 1 := fun he => hbn (Subtype.ext he)
  have hfixed := ExtraspecialExclusion_ti_disjoint_fixed A F.U hTI hAU hd hb.1 hbne
  have hindex := ExtraspecialExclusion_core_element_centralizer_index h s hb.2
  let B := F.U ⊓ centralizer ({b} : Set G)
  have hZB : F.Vi 1 ≤ B := le_inf s.kernel_le
    (le_centralizer_iff.mp ((zpowers_le.mpr (hAH hb.1)).trans
      (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide)))) |>.trans
        (centralizer_le (Set.singleton_subset_iff.mpr (mem_zpowers b))))
  have hsmall := BinaryConjugationSection.fixedCodim_le_one_of_fixed_index
    F.H F.U (F.Vi 1) A B ρ (MonoidHom.id F.H) s inf_le_left hZB
    (by rw [commutator_comm]; exact (commutator_eq_bot_iff_le_centralizer.mpr hfixed).le.trans bot_le) hindex
  intro a ha
  let aH : F.H := ⟨a,hAH ha⟩
  apply ExtraspecialExclusion_small_actor_in_core h structural previous ⟨e⟩ s aH
    (Subtype.ext (by simpa only [hc,Subgroup.coe_pow,Subgroup.coe_one] using congrArg Subtype.val (pow_card_eq_one' (x := (⟨a,ha⟩ : A)))))
  let : Finite _ := Finite.of_surjective (fun u : F.U => (s.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have hle := Submodule.finrank_mono (BinaryOffender.fixedSpace_antitone ρ
    (zpowers_le.mpr (show aH ∈ ((A.subgroupOf F.H).map (MonoidHom.id F.H)) by
      exact mem_map_of_mem _ ha)))
  have hsum := BinaryOffender.fixedCodim_add_finrank ρ (zpowers aH)
  have hsum' := BinaryOffender.fixedCodim_add_finrank ρ ((A.subgroupOf F.H).map (MonoidHom.id F.H))
  omega

/-- Every moving TI four-subgroup of the original R₁ meets U. This is the
first case of the weak-closure argument, with the actual two-core retained. -/
theorem extraspecial_ti_four_meets_span
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (A : Subgroup G) (hA : A ≤ F.Ri L 1) (hc : Nat.card A=4)
    (hTI : IsTISubgroup A) (hmove : ¬ A ≤ centralizer (F.U : Set G)) :
    A ⊓ F.U ≠ ⊥ := by
  intro hbot
  have hd : Disjoint A F.U := disjoint_iff.mpr hbot
  have hAQ := ExtraspecialExclusion_ti_disjoint_four_le_core h hab structural previous he A hA hc hTI hd hmove
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  have hAH := hAQ.trans (pCoreIn_le 2 F.H)
  have hAU := hAH.trans s.normalized
  have hcomm : ⁅F.U,A⁆ ≤ F.Vi 1 := by
    rw [commutator_comm]
    exact (commutator_mono hAQ le_rfl).trans (section_core_commutator_le_point h s)
  obtain ⟨v,hv,hvn⟩ : ∃ v ∈ F.U, v ∉ centralizer (A : Set G) := by
    by_contra! hh
    exact hmove (le_centralizer_iff.mp hh)
  have hZA : F.Vi 1 ≤ centralizer (A : Set G) :=
    le_centralizer_iff.mp (hAH.trans
      (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))))
  let f := ExtraspecialExclusion_centralRow A (F.Vi 1) hZA v
    (fun a ha => hcomm (commutator_mem_commutator hv ha))
  have hf : Function.Injective f := (MonoidHom.ker_eq_bot_iff _).mp (by
    apply bot_unique
    intro a ha
    by_contra hn
    have ha1 : a ≠ 1 := hn
    have he : ⁅v,(a:G)⁆=1 := congrArg Subtype.val ha
    apply hvn
    apply ExtraspecialExclusion_ti_disjoint_fixed A F.U hTI hAU hd a.property
      (fun he => ha1 (Subtype.ext he))
    exact ⟨hv,mem_centralizer_singleton_iff.mpr (commutatorElement_eq_one_iff_mul_comm.mp he)⟩)
  have hh := Nat.card_le_card_of_injective f hf
  rw [hc,show Nat.card (F.Vi 1)=2 by simpa using F.card 1 (by decide)] at hh
  omega

private theorem ExtraspecialExclusion_ti_four_moving_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (A : Subgroup G) (hA : A ≤ F.Ri L 1) (hc : Nat.card A=4)
    (hTI : IsTISubgroup A) (hmove : ¬ A ≤ centralizer (F.U : Set G)) :
    ⁅A,F.U⁆ = F.Vi 1 ∧ F.Vi 1 ≤ A := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  let C := A ⊓ F.U
  have hC : C ≠ ⊥ := extraspecial_ti_four_meets_span h hab structural previous he A hA hc hTI hmove
  have hAH : A ≤ F.H := hA.trans ((pCoreIn_le 2 _).trans
    (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  have hUA : F.U ≤ normalizer (A : Set G) :=
    ((le_centralizer_iff.mp ((show C ≤ F.U from inf_le_right).trans (le_centralizer _))).trans
      (Subgroup.centralizer_le_normalizer _)).trans (hTI.normalizer_le_of_ne_bot hC inf_le_left)
  have hcomm : ⁅A,F.U⁆ ≤ C := le_inf
    (le_normalizer_iff_commutator_le_left.mp hUA)
    (le_normalizer_iff_commutator_le_right.mp (hAH.trans s.normalized))
  have hC2 : Nat.card C ≤ 2 := by
    have hd := card_dvd_of_le (show C ≤ A from inf_le_left)
    rw [hc] at hd
    have hmem := Nat.mem_divisors.mpr ⟨hd,(by decide : (4:ℕ) ≠ 0)⟩
    have hvals : Nat.divisors 4 = {1,2,4} := by decide
    rw [hvals] at hmem
    simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
    rcases hmem with hh | hh | hh
    · omega
    · omega
    · have heq : C=A := eq_of_le_of_card_ge inf_le_left (by rw [hh,hc])
      exact (hmove (heq ▸ (show C ≤ centralizer (F.U : Set G) from
        inf_le_right.trans (le_centralizer _)))).elim
  have hAQ : A ≤ F.H.pCoreIn 2 := by
    intro a ha
    let aH : F.H := ⟨a,hAH ha⟩
    apply ExtraspecialExclusion_small_actor_in_core h structural previous he s aH
      (Subtype.ext (by simpa only [hc,Subgroup.coe_pow,Subgroup.coe_one] using congrArg Subtype.val (pow_card_eq_one' (x := (⟨a,ha⟩ : A)))))
    rw [BinaryOffender.fixedCodim_zpowers_eq_displacement_rank]
    exact s.displacement_rank_le_of_commutator_bound A C ⊥ bot_le hcomm 1
      (by simpa using hC2) aH ha
  have hCZ : ⁅A,F.U⁆ ≤ F.Vi 1 := (commutator_mono hAQ le_rfl).trans
    (section_core_commutator_le_point h s)
  have hCn : ⁅A,F.U⁆ ≠ ⊥ := fun hh => hmove (commutator_eq_bot_iff_le_centralizer.mp hh)
  have hZ2 : Nat.card (F.Vi 1)=2 := by simpa using F.card 1 (by decide)
  have hdiv := card_dvd_of_le hCZ
  rw [hZ2] at hdiv
  have hcardC : Nat.card (⁅A,F.U⁆ : Subgroup G)=2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hdiv).resolve_left
      (fun hh => hCn (card_eq_one.mp hh))
  have heq : ⁅A,F.U⁆ = F.Vi 1 := eq_of_le_of_card_ge hCZ (by rw [hcardC,hZ2])
  exact ⟨heq,heq ▸ hcomm.trans inf_le_left⟩

/-- Every conjugate of the selected central four-group lying in R₁ centralizes
U. This discharges the moving-conjugate premise in the p.1054 argument. -/
theorem extraspecial_four_conjugate_centralizes_span
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) (hZD : F.Vi 1 ≤ D)
    (hDK : D ≤ (center (K F)).map (K F).subtype) (hcard : Nat.card D=4)
    (hTI : IsTISubgroup D) (g : G)
    (hg : D.map (MulAut.conj g).toMonoidHom ≤ F.Ri L 1) :
    D.map (MulAut.conj g).toMonoidHom ≤ centralizer (F.U : Set G) := by
  by_contra hmove
  let A := D.map (MulAut.conj g).toMonoidHom
  have hA4 : Nat.card A=4 := (card_map_of_injective (MulAut.conj g).injective).trans hcard
  have hZA := (ExtraspecialExclusion_ti_four_moving_commutator h hab structural previous he A hg hA4
    (hTI.map_equiv (MulAut.conj g)) hmove).2
  have hAD : A=D := (hTI.eq_or_disjoint_conjugate g).resolve_right (by
    intro hd
    have hz := (le_inf hZA hZD).trans hd.le_bot
    have hz2 := F.card 1 (by decide)
    rw [le_bot_iff.mp hz,card_bot] at hz2
    norm_num at hz2)
  apply hmove
  change A ≤ centralizer (F.U : Set G)
  rw [hAD]
  have hCU : (center (K F)).map (K F).subtype ≤ centralizer (F.U : Set G) := by
    rintro x ⟨z,hz,rfl⟩ u hu
    let uK : K F := ⟨u,(span_le_residual_core h hab).trans (pCoreIn_le 2 (K F)) hu⟩
    exact congrArg Subtype.val (mem_center_iff.mp hz uK)
  exact hDK.trans hCU
/-- The actual weak closure is normal in both original overgroups, giving the
source contradiction at the end of the extraspecial branch. -/
theorem extraspecial_residual_impossible
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u}) :
    ¬ Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3) := by
  intro he
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  obtain ⟨D,hZD,hDK,hD4,hDT,hND,hTI⟩ := extraspecial_center_four_ti
    d h hab structural previous faithful earlier he
  let X := ChapterE.indexedWeakClosure D (F.Ri L 1) 0
  have hXU : X ≤ centralizer (F.U : Set G) := by
    change ChapterE.indexedWeakClosure D (F.Ri L 1) 0 ≤ _
    rw [ChapterE.weakClosure_eq_sSup_gamma]
    apply sSup_le
    intro A hA
    obtain ⟨g,rfl,hg⟩ := (ChapterE.mem_gamma_zero_iff D (F.Ri L 1) A).mp hA
    exact extraspecial_four_conjugate_centralizes_span h hab structural previous he
      D hZD hDK hD4 hTI g hg
  have hQX : X ≤ Q T L :=
    (le_inf ((ChapterE.indexedWeakClosure_le _ _ _).trans
      ((pCoreIn_le 2 _).trans Rechoice.group_le_LT))
      (hXU.trans (centralizer_le (le_conjugateSpanBy V F.H)))).trans
      (h.centralizer_LT_at structural).le
  have hQHX : X ≤ F.H.pCoreIn 2 := hXU.trans
    (centralizer_U_le_core_of_escape h structural (h.flag_escape_at F previous) s)
  have hQT : Q T L ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow _ (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right)
  have hQHT : F.H.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow _ (T.subtype (F.invariant 1))).trans_eq
      (map_subgroupOf_eq_of_le (F.invariant 1))
  have hQR : Q T L ≤ F.Ri L 1 :=
    (le_inf (hQT.trans le_sup_right) le_rfl).trans
      (inf_pCoreIn_le_of_le 2 Rechoice.group_le_LT)
  have hQHR : F.H.pCoreIn 2 ≤ F.Ri L 1 :=
    (le_inf (hQHT.trans le_sup_right) le_rfl).trans
      (inf_pCoreIn_le_of_le 2 Rechoice.group_le_H)
  have heq : X = ChapterE.indexedWeakClosure D (Q T L) 0 :=
    le_antisymm (SubgroupFamily.span_le_span_of_span_le hQX)
      (ChapterE.weakClosure_mono D 0 hQR)
  have heqH : X = ChapterE.indexedWeakClosure D (F.H.pCoreIn 2) 0 :=
    le_antisymm (SubgroupFamily.span_le_span_of_span_le hQHX)
      (ChapterE.weakClosure_mono D 0 hQHR)
  have hLT : L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) := by
    rw [heq]
    exact ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _
        (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)))).trans
      (ChapterE.normalizer_le_weakClosure_normalizer D (Q T L) 0)
  have hH : F.H ≤ normalizer (X : Set G) := by
    rw [heqH]
    exact (F.H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 F.H))).trans
      (ChapterE.normalizer_le_weakClosure_normalizer D (F.H.pCoreIn 2) 0)
  have hDcore : D ≤ F.H.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsPGroup.of_card (p := 2) (n := 2) hD4)
    (hDK.trans ((map_subtype_le _).trans (K_le_H F))) hND.ge
  have hXne : X ≠ ⊥ := by
    intro hx
    have hd : D=⊥ := le_bot_iff.mp (hx ▸ ChapterE.self_le_weakClosure_zero (hDcore.trans hQHR))
    rw [hd,card_bot] at hD4
    omega
  have hu : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro Y _ _ hY S M hM
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hY S hM
  have hn : normalizer (X : Set G) ≤ normalizer (L : Set G) :=
    normalizer_le_of_unique_maximalTwoLocal (J := L ⊔ (T : Subgroup G))
      (fun M hM hLM => Set.mem_singleton_iff.mp ((h.maximal_unique_at structural).2 ▸
        show M ∈ {M : Subgroup G | IsMaximalTwoLocal M ∧ L ⊔ (T : Subgroup G) ≤ M}
          from ⟨hM,hLM⟩)) ((isPGroup_pCoreIn 2 _).to_le hQX) hXne hLT
  exact h.flag_escape_at F previous (hH.trans hn)

/-- The source's star formulation, transported by the canonical comparison
of O²(H/O₂(H)) with the original K/O₂(K). -/
theorem extraspecial_star_residual_impossible
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u}) :
    ¬ Nonempty (pResidual 2 (HStar F.H) ≃* HeisenbergPrime 3) := by
  rintro ⟨e⟩
  exact extraspecial_residual_impossible d h hab structural previous faithful earlier
    ⟨(residualStarEquiv F).trans e⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The noncyclic three-core branch for the actual local family

Let J be any actual member of H_z. If J is solvable and every prime core
above three of J/O₂(J) vanishes, Fitting self-centralization and the local
Sylow order bound force its three-core to be noncyclic. Strong quasithinness
bounds its rank by two. A supercritical subgroup therefore has an actual
E₉ or order-27 Heisenberg marking. Taking the two-residual of its full
preimage constructs a subgroup normal in J, with precisely its intrinsic
two-core as quotient-action kernel and with the same model quotient.

The exhaustive solvable-local application leaves either a large-prime
core or these two normal lifts. At the original J = G₁, the completed
extraspecial exclusion forces a Heisenberg lift to be proper in O²(J).
It does not exclude proper Heisenberg lifts or identify them with K.
The large-prime exclusion, remaining ambient three-core analysis and
nonsolvability of every J remain to be proved before 14.7.27–29 close.

Source: Aschbacher–Smith, 14.7.6, 14.7.27–29, printed pp.1044–1045,
1054–1055; A.1.21 and A.1.25, printed pp.24–25, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- A solvable member of H_z with no large-prime core must have noncyclic three-core. -/
theorem local_solvable_threeCore_not_cyclic
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (hlarge : ∀ p : ℕ, p.Prime → 3 < p → pCore p (HStar J) = ⊥) :
    ¬ IsCyclic (pCore 3 (HStar J)) := by
  intro hc
  let := hs
  let := hc
  let S : Sylow 2 (HStar J) := Classical.choice inferInstance
  have hb := sylow_card_le_two_of_solvable_cyclic_threeCore
    (D := HStar J) inferInstance (pCore_quotient_pCore_eq_bot 2) hlarge S
  have hd := four_dvd_local_star_sylow_card_at h hab structural J hJ S
  have := Nat.le_of_dvd (Nat.card_pos (α := S)) hd
  omega

/-- The literal supercritical three-core has rank two, and its two-perfect
preimage has elementary-nine or Heisenberg quotient with the exact two-core kernel. -/
theorem local_noncyclic_threeCore_models
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hnc : ¬ IsCyclic (pCore 3 (HStar J))) :
    ∃ (X : Subgroup (pCore 3 (HStar J))) (_hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup J),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 J ∧
      Y.map (QuotientGroup.mk' (pCore 2 J)) = X.map (pCore 3 (HStar J)).subtype ∧
      ((QuotientGroup.mk' (pCore 2 J)).comp Y.subtype).ker = pCore 2 Y ∧
      (Nonempty ((Y ⧸ pCore 2 Y) ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∨
        Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3)) := by
  let P := pCore 3 (HStar J)
  have hP : IsPGroup 3 P := pCore_isPGroup
  have hne : F.Vi 1 ≠ ⊥ := by
    intro he
    have hc := F.card 1 (by decide)
    rw [he,card_bot] at hc
    norm_num at hc
  have hH : IsTwoLocal F.H := ⟨F.Vi 1,hne,IsPGroup.of_card (p := 2) (n := 1) (F.card 1 (by decide)),rfl⟩
  have hJrank : primeRank 3 J ≤ 2 :=
    (Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion hJ.2.1) (inclusion_injective hJ.2.1)).trans
      ((h.source.simpleQTKE.twoLocal_sqtk hH).stronglyQuasithin 3 (by decide) (by decide))
  have hr : primeRank 3 P ≤ 2 := (primeRank_subgroup_le 3 P).trans
    ((primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 J) pCore_isPGroup).trans hJrank)
  let : Nontrivial P := by
    cases subsingleton_or_nontrivial P with
    | inl hs => let := hs; exact (hnc inferInstance).elim
    | inr ht => exact ht
  obtain ⟨X,hX⟩ := hP.exists_supercriticalPSubgroup (by decide : 3 ≠ 2)
  let : X.Characteristic := hX.characteristic
  let X₀ := X.map P.subtype
  let : X₀.Characteristic := inferInstance
  obtain ⟨Y,hYn,hYp,hYle,hYm,hYk,⟨e⟩⟩ := Subgroup.exists_normal_three_residual_lift
    (QuotientGroup.mk' (pCore 2 J)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) X₀ (hP.to_subgroup X |>.map P.subtype)
  let eX : X ≃* X₀ := equivMapOfInjective X P.subtype P.subtype_injective
  refine ⟨X,hX,Y,hYn,hYp,hYle,hYm,hYk,?_⟩
  rcases (ChapterA.lemma_A_1_25_1 (by decide) hP hr X hX).2 with hc | hm | hm
  · have hrX : primeRank 3 X ≤ 1 := (primeRank_le_iff_elementary_card_le X).mpr
      (fun E _ => by simpa only [pow_one,hc.1] using (card_le_card_group E))
    have hrP := hX.primeRank_le_one_of_rank_le_one hP (by decide) hrX
    exact (hnc (hP.isCyclic_of_odd_of_elementary_card_le (by decide)
      (fun E hE => by
        let := hE
        exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hrP E))).elim
  · exact Or.inl ⟨e.trans (eX.symm.trans hm.2.some)⟩
  · exact Or.inr ⟨e.trans (eX.symm.trans hm.2.2.some)⟩

/-- The source solvable-local branch has an actual normal residual lift of one
of the two noncyclic supercritical models; no model-recognition premise is assumed. -/
theorem local_solvable_threeCore_models
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (hlarge : ∀ p : ℕ, p.Prime → 3 < p → pCore p (HStar J) = ⊥) :
    ∃ (X : Subgroup (pCore 3 (HStar J))) (_hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup J),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 J ∧
      Y.map (QuotientGroup.mk' (pCore 2 J)) = X.map (pCore 3 (HStar J)).subtype ∧
      ((QuotientGroup.mk' (pCore 2 J)).comp Y.subtype).ker = pCore 2 Y ∧
      (Nonempty ((Y ⧸ pCore 2 Y) ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∨
        Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3)) := by
  exact local_noncyclic_threeCore_models h J hJ
    (local_solvable_threeCore_not_cyclic h hab structural J hJ hs hlarge)

/-- An exhaustive reduction for any actual solvable overgroup: either a
large-prime core survives, or one of the two noncyclic three-core models has
an actual normal two-perfect lift. The large-prime exclusion and the ambient
exclusion of these lifts remain the subsequent source obligations. -/
theorem local_solvable_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    (∃ p : ℕ, p.Prime ∧ 3 < p ∧ pCore p (HStar J) ≠ ⊥) ∨
    ∃ (X : Subgroup (pCore 3 (HStar J))) (_hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup J),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 J ∧
      Y.map (QuotientGroup.mk' (pCore 2 J)) = X.map (pCore 3 (HStar J)).subtype ∧
      ((QuotientGroup.mk' (pCore 2 J)).comp Y.subtype).ker = pCore 2 Y ∧
      (Nonempty ((Y ⧸ pCore 2 Y) ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∨
        Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3)) := by
  by_cases hp : ∃ p : ℕ, p.Prime ∧ 3 < p ∧ pCore p (HStar J) ≠ ⊥
  · exact Or.inl hp
  have hlarge : ∀ p : ℕ, p.Prime → 3 < p → pCore p (HStar J) = ⊥ := by
    intro p hprime hgt
    by_contra hn
    exact hp ⟨p,hprime,hgt,hn⟩
  exact Or.inr (local_solvable_threeCore_models h hab structural J hJ hs hlarge)

/-- At the original point normalizer the completed extraspecial exclusion
makes every Heisenberg lift proper in O²(H). The other alternatives retain
their literal normal lift and quotient kernel. -/
theorem original_solvable_reduction
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : Chapter14.Section04.LargerDimension.LocalAction.Components.EarlierFaithfulClassification
      G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (hs : Group.IsSolvable F.H) :
    (∃ p : ℕ, p.Prime ∧ 3 < p ∧ pCore p (HStar F.H) ≠ ⊥) ∨
    ∃ (X : Subgroup (pCore 3 (HStar F.H))) (_hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup F.H),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 F.H ∧
      Y.map (starMap F) = X.map (pCore 3 (HStar F.H)).subtype ∧
      ((starMap F).comp Y.subtype).ker = pCore 2 Y ∧
      (Nonempty ((Y ⧸ pCore 2 Y) ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∨
        (Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3) ∧ Y < pResidual 2 F.H)) := by
  rcases local_solvable_reduction h hab structural F.H
    (F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)) hs with hp | hm
  · exact Or.inl hp
  obtain ⟨X,hX,Y,hYn,hYp,hYle,hYm,hYk,hm⟩ := hm
  refine Or.inr ⟨X,hX,Y,hYn,hYp,hYle,hYm,hYk,?_⟩
  rcases hm with hm | hm
  · exact Or.inl hm
  refine Or.inr ⟨hm,lt_of_le_of_ne hYle ?_⟩
  intro heq
  have hh : Nonempty (((pResidual 2 F.H) ⧸ pCore 2 (pResidual 2 F.H)) ≃*
      HeisenbergPrime 3) := heq ▸ hm
  let e : pResidual 2 F.H ≃* K F :=
    equivMapOfInjective (pResidual 2 F.H) F.H.subtype F.H.subtype_injective
  let eQ := QuotientGroup.congr (pCore 2 (pResidual 2 F.H)) (pCore 2 (K F)) e
    (pCore_map_iso 2 e)
  exact extraspecial_residual_impossible d h hab structural previous faithful earlier
    ⟨eQ.symm.trans hh.some⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end
