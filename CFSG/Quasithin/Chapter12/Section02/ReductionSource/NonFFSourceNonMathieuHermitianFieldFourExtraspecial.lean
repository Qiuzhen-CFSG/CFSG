module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourExtraspecial
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourNilpotent

/-!
# The original Hermitian extraspecial radicals centralize the four-space

At the Sylow-normal four-space selected by either tensor branch, the
nilpotent A.3.6 radical is a Xi member. Its actual conjugation image on the
four-space is trivial by the p²-divisibility obstruction. Relative
normality of the source residual and its simple SL₂(4) quotient still force
the radical outside N_G(L). The two-core supplement identity then puts
every actual odd Sylow supplement outside N_G(L).

The tensor application retains the original action, Sylow, fixed subgroup,
residual quotient, full centralizer kernel and containing normal component.
Each surviving supplement is extraspecial of order p³ and exponent p. Its
actual center is cyclic of order p, centralizes the four-space, and has a
normalizer escaping N_G(L). No placement of that center in N_G(L) or C_G(V)
is assumed or asserted. That placement and the odd-normalizer contradiction
are the remaining extraspecial step of 8.2.7; quasisimplicity, zero-closure
exclusion and 8.2.8--13 are not proved by this module.

Source: Aschbacher--Smith, 8.2.7, printed pp.717--718, using 1.3.1--3,
refs/quasithin.pdf (1 March 2004 manuscript).
-/

public noncomputable section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The full nilpotent radical centralizes the original four-space but lies
outside N_G(L); every one of its odd Sylow supplements also lies outside. -/
theorem sourceOrbit_hermitian_nilpotent_radical_centralizer
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (U K : Subgroup G) [IsElementaryAbelian 2 U]
    (hUV : U ≤ D.sourceOrbit) (hu : rank U = 4)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hKU : K ≤ normalizer (U : Set G))
    (hK : (K.subgroupOf (normalizer (U : Set G))).IsCComponent)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hRK : Chapter8.Section02.Normalizer.localResidual L U ≤ K)
    (hR : Nonempty (((Chapter8.Section02.Normalizer.localResidual L U) ⧸
      pCore 2 (Chapter8.Section02.Normalizer.localResidual L U)) ≃* SL(2,E 1)))
    (p : ℕ) [Fact p.Prime]
    (hnil : Chapter1.Section02.A36Nilpotent (Chapter1.XiQuotient K))
    (hd : p ∣ Nat.card (fittingSubgroup (Chapter1.XiQuotient K))) :
    let X := Chapter1.XiP p K
    Chapter1.XiMember (T : Subgroup G) X ∧
      X ≤ centralizer (U : Set G) ∧ ¬ X ≤ normalizer (L : Set G) ∧
      ∀ P : Sylow p X,
        ¬ (P : Subgroup X).map X.subtype ≤ normalizer (L : Set G) := by
  have hUne : U ≠ ⊥ := by
    intro hz
    rw [hz,Representation.BinaryOffender.rank_bot] at hu
    omega
  have hlocal : K ∈ Chapter1.L G (T : Subgroup G) := by
    refine ⟨hK.subgroupOf_of_le le_sup_left (sup_le hKU hTU),?_,?_⟩
    · exact ⟨T.subtype le_sup_right,map_subgroupOf_eq_of_le le_sup_right⟩
    · exact ne_bot_of_le_ne_bot hUne
        (le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 U)
          (hUV.trans (D.sourceOrbit_weakClosure_setup.le_sylow.trans le_sup_right))
          (sup_le hKU hTU))
  have hQ := Chapter1.Section02.uniqueness_local_quotient_sqtk h.simpleQTKE hlocal.2.2
  have hA36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  obtain ⟨hp,hq,hXi⟩ := nilpotent_radical_member hA36 hlocal hQ hTK p hnil hd
  have hcent := xi_radical_centralizes_four_space hXi hTU
    ((Chapter1.XiP_le p K).trans hKU) hu hp hq
  have hn := nilpotent_not_quasisimple hnil
  have ho : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left (by omega)
  let R := Chapter8.Section02.Normalizer.localResidual L U
  let H := L ⊓ normalizer (U : Set G)
  let er : solvableResidual H ≃* R :=
    (solvableResidual H).equivMapOfInjective H.subtype H.subtype_injective
  let : Group.IsPerfect R := Group.IsPerfect.ofSurjective
    (f := er.toMonoidHom) er.surjective
  let : IsSimpleGroup PSL(2,E 1) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [card_E]; norm_num)
  let : IsSimpleGroup SL(2,E 1) := (Theory.PSL2.sl2QuotientEquiv (E 1)).isSimpleGroup
  let : IsSimpleGroup (R ⧸ pCore 2 R) := hR.some.isSimpleGroup
  have hTR := Chapter8.Section02.Normalizer.normalizes_localResidual L U T
    D.sylow_normalizes_component hTU
  have hMR := Chapter8.Section02.Normalizer.normalizes_localResidual L U
    (normalizer (L : Set G) ⊓ normalizer (U : Set G)) inf_le_left inf_le_right
  have hout := radical_not_le_relative_normalizer hA36 hlocal hQ hTK hTR hRK hKU hMR
    hn ho hd hXi
  refine ⟨hXi,hcent,hout,?_⟩
  intro P hPM
  apply hout
  rw [←hXi.sylow_sup hq P]
  have hc := hXi.pCoreIn_le_of_isSylowIn
    (show Chapter1.IsSylowIn 2 (T : Subgroup G)
      (Chapter1.XiP p K ⊔ (T : Subgroup G)) from
      ⟨T.subtype le_sup_right,map_subgroupOf_eq_of_le le_sup_right⟩)
  exact sup_le (hc.trans D.sylow_normalizes_component) hPM

/-- On both original tensor branches, every surviving extraspecial radical
centralizes the canonical four-space, while each actual odd Sylow supplement
escapes the original normalizer. The full residual and centralizer kernels
are retained. -/
theorem sourceOrbit_hermitian_tensor_nilpotent_centralizers
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
              let X := Chapter1.XiP p K
              IsExtraspecial p (Chapter1.XiQuotient X) ∧
              Nat.card (Chapter1.XiQuotient X) = p^3 ∧
              Monoid.exponent (Chapter1.XiQuotient X) = p ∧
              X ≤ centralizer (U : Set G) ∧ ¬ X ≤ normalizer (L : Set G) ∧
              ∀ P : Sylow p X,
                let Y := (P : Subgroup X).map X.subtype
                IsExtraspecial p Y ∧ Nat.card Y = p^3 ∧ Monoid.exponent Y = p ∧
                Y ≤ centralizer (U : Set G) ∧ ¬ Y ≤ normalizer (L : Set G) ∧
                let Z := (center Y).map Y.subtype
                Nat.card Z = p ∧ IsCyclic Z ∧ Z ≠ ⊥ ∧ Z ≤ centralizer (U : Set G) ∧
                  Y ≤ normalizer (Z : Set G) ∧
                  ¬ normalizer (Z : Set G) ≤ normalizer (L : Set G)) := by
  obtain ⟨hn,hB,U,hU,hUV,hu,hTU,hker,hR,hsol,K,hKU,hK,hRK,hNK,hnat,hcores⟩ :=
    D.sourceOrbit_hermitian_tensor_component_nilpotent_radicals
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel
  let := hU
  refine ⟨hn,hB,U,hU,hUV,hu,hTU,hker,hR,hsol,K,hKU,hK,hRK,hNK,hnat,?_⟩
  intro hnil p hp hd
  let := hp
  obtain ⟨hfull,hx,hcard,hexp⟩ := hcores hnil p hp hd
  obtain ⟨hXi,hcent,hout,hSyl⟩ := D.sourceOrbit_hermitian_nilpotent_radical_centralizer
    h.toHypothesis1221 U K hUV hu hTU hKU hK (hTU.trans hNK) hRK hR p hnil hd
  refine ⟨hfull,hx,hcard,hexp,hcent,hout,?_⟩
  intro P
  have hp3 := (Chapter1.RadicalStructure.radical_core (Or.inr hnil) hd).2.1
  have ho : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left (by omega)
  have hq : Chapter1.XiOddQuotient p (Chapter1.XiQuotient (Chapter1.XiP p K)) :=
    Or.inr ⟨hx,hcard,hexp⟩
  let e := hXi.ambientSylowQuotientEquiv ho hq P
  let := IsExtraspecial.of_mulEquiv e.symm hx
  have hYU := (map_subtype_le (P : Subgroup (Chapter1.XiP p K))).trans hcent
  exact ⟨inferInstance,(Nat.card_congr e.toEquiv).trans hcard,
    (Monoid.exponent_eq_of_mulEquiv e).trans hexp,hYU,hSyl P,
    extraspecial_supplement_center_escape hYU (hSyl P)⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
