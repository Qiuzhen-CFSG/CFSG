module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourOrdinary
public import Theory.SpecificGroups.PSL4Two.SchurMultiplier
public import Theory.SpecificGroups.SU3.BinaryCubicRankParity
public import Theory.SpecificGroups.SU3.EvenSemilinear.CyclicOuter

/-!
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
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open ClassificationModels Chapter1.Section02.LocalModels
open Chapter15.Section03.Candidates.ComponentStructure
private theorem transport_rankTwo_exclusion
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


private theorem binary_linear_action_false {Q : Type*} [Group Q] [Finite Q]
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

private theorem binary_rankOne_action_false {Q : Type*} [Group Q] [Finite Q]
    (f : HeisenbergPrime 3 →* MulAut Q) (hf : Function.Injective f)
    {n : ℕ} (hm : ClassicalGroup.IsPSL Q 2 (2^n)) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let c := MulAut.congr (e.trans (BenderSuzuki.ZD.Linear.sl2QuotientEquiv F).symm)
  exact Matrix.SL2.no_heisenberg_automorphism_action
    (c.toMonoidHom.comp f) (c.injective.comp hf)

private theorem binary_unitary_even_action_false {Q : Type*} [Group Q] [Finite Q]
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

private theorem rankTwo_action_false {Q : Type*} [Group Q] [Finite Q]
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
    apply transport_rankTwo_exclusion
      (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)
      ?_ A hA hr J hs ho f hf hJ
    intro A hA hr J hs ho f hf hJ
    let := hs
    exact HeisenbergPrime.BinaryRankTwoExclusions.symplectic hF (by omega)
      (hF.symm ▸ hq) A hA hr J ho f hf hJ
  · let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    apply transport_rankTwo_exclusion e ?_ A hA hr J hs ho f hf hJ
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
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
  refine ⟨fun _ hm => binary_rankOne_action_false f' hf' hm,
    fun _ hn hm => rankTwo_action_false _ hi hr _ hs ho f hf hfJ hn (Or.inl hm),
    fun _ hn hm => rankTwo_action_false _ hi hr _ hs ho f hf hfJ hn (Or.inr hm),
    ?_, fun _ hn hm => binary_linear_action_false f' hf' hn hm,
    fun _ hn he hm => binary_unitary_even_action_false f' hf' hn he hm, ?_⟩
  · rintro ⟨e⟩
    exact Atlas.G2.BinaryLocalResidual.no_odd_index_heisenberg e _ hi _ ho hres
  · rintro n hn ⟨e⟩
    exact HeisenbergPrime.SmallAutomorphismExclusions.no_alternating_action hn e f' hf'

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
