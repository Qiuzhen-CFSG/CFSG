module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourJankoCentralizers
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianJankoComparison

/-!
# Excluding the normal J₄ alternative for the actual Hermitian centers

The original noncubic odd actor and the original T-fixed involution put
the full component-centralizer residual inside N_G(L). The same original
nine-space makes that containment impossible. This excludes the normal
J₄ component supplied by residual uniqueness, without an SQTK assumption
on the odd normalizer.

For every extraspecial Sylow supplement in the literal tensor construction,
its actual center has prime order greater than three and is therefore an
elementary actor. The final theorem applies the exclusion to each center
on both weak-closure branches. It retains the full four-space, residual,
central and odd-core data, H-star membership and escaping normalizers.
The ordinary pushing-up J₄ branch, whole-normalizer containment, and the
subsequent 8.2.7--13 assembly remain to be proved.

Source: Aschbacher--Smith 4.4.3 and Remark 4.4.2, printed pp.619,623,
applied in 8.2.7, printed p.718, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
open Chapter4.Section02.RankOneReciprocalEscape
open Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The residual-uniqueness J₄ case is impossible for an original
noncubic elementary actor. Both comparisons use the same T-fixed involution
and the full centralizer residual of the same covering component. -/
theorem sourceOrbit_hermitian_no_normal_janko
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    {p : ℕ} (hp : p.Prime) (hgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (hc : HermitianNormalJankoCase L D.sourceOrbit A) : False := by
  obtain ⟨hu,K,hK,hn,hmove,hout,hcore,hVK,hFK,hcent,hr,⟨e⟩,he⟩ := hc
  let := hn
  let := hK.2
  obtain ⟨z,hzV,hz,hTz,hRM⟩ :=
    D.sourceOrbit_hermitian_janko_fixed_residual_comparison h.toHypothesis1221 hV hp hgt
      A hne hAe (hA.trans (D.sourceOrbit_relative_centralizer_le_sectionCentralizer
        h.toHypothesis1221 hV)) (by simpa only [hV] using hA.trans inf_le_right)
      K (by simpa only [hV] using hVK) hcent e
  exact D.sourceOrbit_hermitian_normal_janko_residual_escape
    h hmany hV hnon d A K hVK hcent e z (by simpa only [hV] using hzV) hz hRM

/-- Every escaping noncubic elementary actor in the actual field-four
Hermitian action must therefore take the ordinary pushing-up branch. -/
theorem sourceOrbit_hermitian_field_four_oddActor_pushingUp
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2)
    {p : ℕ} (hp : p.Prime) (hgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    HermitianPushingUpJankoCase L D.sourceOrbit A := by
  let : Fact p.Prime := ⟨hp⟩
  let := hAe
  have ho : Odd (Nat.card A) := by
    obtain ⟨n,hn⟩ := hAe.isPGroup.exists_card_eq
    rw [hn]
    exact (hp.odd_of_ne_two (by omega)).pow
  exact (D.sourceOrbit_hermitian_field_four_oddActor_janko_cases
    h hmany hV hnon d B eQ hfield A hne hA ho hout).resolve_left
    (D.sourceOrbit_hermitian_no_normal_janko h hmany hV hnon d hp hgt A hne hAe hA)

/-- Every actual extraspecial Sylow center in the original tensor construction
has the ordinary pushing-up configuration. The residual-uniqueness case is
excluded, and all original four-space, residual and center data are retained. -/
theorem sourceOrbit_hermitian_tensor_nilpotent_center_pushingUp
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n) :
    n = 1 ∧ B.degree = 2 ∧
      ∃ U : Subgroup G, ∃ hU : IsElementaryAbelian 2 U, letI := hU
        U ≤ D.sourceOrbit ∧ rank U = 4 ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
        let R := Chapter8.Section02.Normalizer.localResidual L U
        R ⊓ centralizer (U : Set G) = R.pCoreIn 2 ∧
        Nonempty ((R ⧸ pCore 2 R) ≃* SL(2,E 1)) ∧
        Group.IsSolvable (L ⊓ centralizer (U : Set G) : Subgroup G) ∧
        ∃ K : Subgroup G, K ≤ normalizer (U : Set G) ∧
          (K.subgroupOf (normalizer (U : Set G))).IsCComponent ∧
          R ≤ K ∧ normalizer (U : Set G) ≤ normalizer (K : Set G) ∧
          ¬ Chapter1.Section02.A36Natural (Chapter1.XiQuotient K) ∧
          (Chapter1.Section02.A36Nilpotent (Chapter1.XiQuotient K) →
            ∀ (p : ℕ) (_ : Fact p.Prime),
              p ∣ Nat.card (fittingSubgroup (Chapter1.XiQuotient K)) →
              Chapter1.Section02.LocalModels.OddExtraspecialThree p
                (pCore p (Chapter1.XiQuotient K)) ∧
              IsExtraspecial p (Chapter1.XiQuotient (Chapter1.XiP p K)) ∧
              Nat.card (Chapter1.XiQuotient (Chapter1.XiP p K)) = p^3 ∧
              Monoid.exponent (Chapter1.XiQuotient (Chapter1.XiP p K)) = p ∧
              (Chapter1.XiP p K ⊔ (T : Subgroup G) ∈
                Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
                (Chapter1.XiP p K ⊔ (T : Subgroup G)) ⊓ normalizer (R : Set G) =
                  (Chapter1.XiP p K ⊔ (T : Subgroup G)) ⊓ normalizer (L : Set G) ∧
                ∀ P : Sylow p (Chapter1.XiP p K),
                  let Y := (P : Subgroup (Chapter1.XiP p K)).map (Chapter1.XiP p K).subtype
                  let Z := (center Y).map Y.subtype
                  Nat.card Z = p ∧ IsCyclic Z ∧ Z ≠ ⊥ ∧
                    Z ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) ∧
                    ¬ normalizer (Z : Set G) ≤ normalizer (L : Set G) ∧
                    (pPrimeCore 2 (normalizer (Z : Set G))).map (normalizer (Z : Set G)).subtype ≤
                      normalizer (L : Set G) ∧
                    HermitianPushingUpJankoCase L D.sourceOrbit Z)) := by
  obtain ⟨hn,hB,U,hU,hUV,hu,hTU,hker,hR,hsol,K,hKU,hK,hRK,hNK,hnat,hcores⟩ :=
    D.sourceOrbit_hermitian_tensor_nilpotent_center_janko_cases
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    (ρ := D.orbitRepresentation) (Q := D.orbitComponent) hs B C n hdegree hfield hmodel
  subst hn
  let := hU
  refine ⟨rfl,hB,U,hU,hUV,hu,hTU,hker,hR,hsol,K,hKU,hK,hRK,hNK,hnat,?_⟩
  intro hnil p hp hd
  let := hp
  obtain ⟨hfull,hx,hcard,hexp,hH,heq,hcenters⟩ := hcores hnil p hp hd
  have hgt := (Chapter1.RadicalStructure.radical_core (Or.inr hnil) hd).2.1
  refine ⟨hfull,hx,hcard,hexp,hH,heq,?_⟩
  intro P
  obtain ⟨hc,hcyc,hne,hplaced,hout,hcore,hcase⟩ := hcenters P
  let Y := (P : Subgroup (Chapter1.XiP p K)).map (Chapter1.XiP p K).subtype
  let Z := (center Y).map Y.subtype
  let : IsCyclic Z := hcyc
  let : CommGroup Z := IsCyclic.commGroup
  let hZe : IsElementaryAbelian p Z := {
    exponent_dvd_p := by rw [←hc]; exact Group.exponent_dvd_nat_card }
  exact ⟨hc,hcyc,hne,hplaced,hout,hcore,hcase.resolve_left
    (D.sourceOrbit_hermitian_no_normal_janko h hmany hV hnon d
      (Fact.out : p.Prime) hgt Z hne hZe hplaced)⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
