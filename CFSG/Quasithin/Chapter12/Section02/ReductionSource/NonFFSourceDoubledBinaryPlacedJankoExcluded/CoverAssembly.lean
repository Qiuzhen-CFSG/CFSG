module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPlacedJankoExcluded.NativeLinearFive
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.CoverAssembly
/-!
# The original binary J₄ exclusion conditional on the native cover

The original maximal two-local is the full normalizer of its large-center
radical core. Its marked normal residual excludes both surviving native
locals. The four-local cover therefore removes J₄ from the same placed
component witness and leaves the Rudvalis and maximal-pushing-up alternatives.
Only the uniform cover is an additional input; the native quotient and all
normality, whole-module and component-map premises have been discharged.

Source: Aschbacher--Smith 4.4.3 and its original 12.2 application;
Kleidman--Wilson (1988), Section 2, pp.488--493.
-/

public section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory ChapterB.QuasisimpleSource
open Chapter7.NormalizedSource Chapter4 Chapter4.Section04
open Representation Representation.BinaryOffender BinaryLinearThree
open Janko4.LocalStructure.LargeCenterRadicals.LinearFiveLocal
open scoped IsMulCommutative
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)


/-- Conditional on the uniform cover, the original native geometry is impossible. -/
theorem native_janko_geometry_false_of_cover
    (hnative : Janko4.LocalStructure.LargeCenterRadicals.MaximalTwoLocalCover)
    (A : Subgroup G) (K : Subgroup (normalizer (A : Set G)))
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (e : (K ⧸ center K) ≃* Janko4.Model)
    (hg : D.BinaryPlacedNativeGeometry A K hr e) : False := by
  obtain ⟨m,hm,hP,hN,hlarge,hq⟩ := D.native_janko_geometry_quotients_excluded A K hr e hg
  obtain ⟨_,_,m',hm',hu,_⟩ := hg
  have he : m' = m := by
    ext x
    exact (hm' x).trans (hm x).symm
  subst m'
  apply Janko4.LocalStructure.LargeCenterRadicals.maximal_radical_false_of_cover
    hnative _ hP hlarge
  · simpa only [hN] using hu.1
  · dsimp only
    rw [hN]
    exact hq

/-- All original chosen-module hypotheses feed the conditional J₄ exclusion. -/
theorem sourceOrbit_binary_oddNormalizer_janko_false_of_cover
    (hnative : Janko4.LocalStructure.LargeCenterRadicals.MaximalTwoLocalCover)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K) (hcore : pCore 2 K = ⊥)
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (e : (K ⧸ center K) ≃* Janko4.Model) : False := by
  exact D.native_janko_geometry_false_of_cover hnative A K hr e
    (D.sourceOrbit_binary_oddNormalizer_native_placement h hd F hF hmodel A hAC ho hu
      K hK hcore hr .j4 (Or.inl rfl) e)

/-- The original native placed case with only its J₄ alternative removed.
Every other source clause, witness and quotient marking is retained. -/
@[expose] def BinaryPlacedNativeRudvalisCase (A : Subgroup G) : Prop :=
  UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
  ∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K,D.sourceOrbit.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    (∀ q : ℕ, Odd q → ¬ ClassicalGroup.IsPSL (K ⧸ center K) 2 q) ∧
    (∀ p : ℕ, p.Prime → Odd p →
      (¬ ClassicalGroup.IsPSL (K ⧸ center K) 3 p) ∧
      (¬ ClassicalGroup.IsPSU (K ⧸ center K) 3 p)) ∧
    (∀ p : ℕ, p.Prime → Odd p →
      (¬ ClassicalGroup.IsPSL (K ⧸ center K) 3 (p^2)) ∧
      (¬ ClassicalGroup.IsPSU (K ⧸ center K) 3 (p^2))) ∧
    (K.Normal ∧ D.sourceOrbit ≤ K.map (normalizer (A : Set G)).subtype ∧
      ∃ hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype,
      centralizer (K : Set (normalizer (A : Set G))) = pPrimeCore 2 (normalizer (A : Set G)) ∧
      6 ≤ primeRank 2 (K ⧸ center K) ∧
      ¬ ChapterA.Section02.IsTheoremBOddModel (K ⧸ center K) ∧
      DoubledBinaryPlacedLocals.LocalData (K ⧸ center K) ∧
      (∃ e : (K ⧸ center K) ≃* Rudvalis.Model, D.BinaryPlacedNativeGeometry A K hr e) ∧
      (∀ p : ℕ, (∃ k : ℕ, p = 2 ^ (2 ^ k) + 1) →
        ¬ ClassicalGroup.IsPSL (K ⧸ center K) 4 p) ∧
      ∃ j : oddActorResidual L A →* K ⧸ center K, IsPGroup 2 j.ker ∧
        ∃ f : j.range →* BinaryLinearThree.Group, Function.Surjective f)

/-- The same original placed witness is Rudvalis once the uniform cover is supplied. -/
theorem binaryPlacedNativeCase_rudvalis_of_janko_cover
    (hnative : Janko4.LocalStructure.LargeCenterRadicals.MaximalTwoLocalCover)
    (A : Subgroup G) (hc : D.BinaryPlacedNativeCase A) :
    D.BinaryPlacedNativeRudvalisCase A := by
  obtain ⟨hu,K,hK,hm,hout,hcore,hmodels,h2,h3,hsquare,
    hn,hW,hr,hC,hrank,hodd,hl,⟨name,hname,e,hg⟩,hfour,j,hj,f,hf⟩ := hc
  rcases hname with rfl | rfl
  · exact (D.native_janko_geometry_false_of_cover hnative A K hr e hg).elim
  · exact ⟨hu,K,hK,hm,hout,hcore,hmodels,h2,h3,hsquare,
      hn,hW,hr,hC,hrank,hodd,hl,⟨e,hg⟩,hfour,j,hj,f,hf⟩

/-- The actual original obstruction retains precisely the maximal-pushing-up
and Rudvalis alternatives after the conditional J₄ exclusion. -/
theorem sourceOrbit_binary_rudvalis_oddLocal_obstruction_of_janko_cover
    (hnative : Janko4.LocalStructure.LargeCenterRadicals.MaximalTwoLocalCover)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : D.SourceOrbitNonFF)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ A : Subgroup G,
        A ≤ H ∧ A ≤ centralizer (D.sourceOrbit : Set G) ∧ Nat.card A = p ∧
        ¬ H ⊓ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
        ((∃ J P : Subgroup G,
          J ∈ muStar (normalizer (L : Set G)) L
            (coveringOvergroup (normalizer (L : Set G)) L (oddActorResidual L A)) ∧
          PushLE L (oddActorResidual L A) J ∧
          IsMaximalTwoLocal P ∧ J ≤ P ∧ ¬ P ≤ normalizer (L : Set G) ∧
          IsSQTK KnownSimple.IsKnownSimple P ∧ D.sourceOrbit ≤ J.pCoreIn 2 ∧
          J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L) ∨
        D.BinaryPlacedNativeRudvalisCase A) := by
  obtain ⟨H,hH,p,hp,hpo,A,hAH,hAC,hcard,hout,hcases⟩ :=
    D.sourceOrbit_binary_native_oddLocal_obstruction h hd hmany hnon F hF hmodel
  refine ⟨H,hH,p,hp,hpo,A,hAH,hAC,hcard,hout,?_⟩
  exact hcases.imp id (D.binaryPlacedNativeCase_rudvalis_of_janko_cover hnative A)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
