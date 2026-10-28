module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourPointProduct
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourPointQuotientExclusion

/-!
# Exclusion of the positive weak-closure Hermitian branch

Source 8.2.12 identifies the actual extraspecial centralizer core and gives
EV = O₂(L_z). Passing to C_G(z)/O₂(C_G(z)) therefore retains the five-point
A₅ action on V/V_z as the complete two-core of the image of L_z. Its original
Sylow still normalizes that local C-component. The full-Sylow deleted-five
SQTK exclusion, with the full known-simple catalogue, gives a contradiction.

All local premises are discharged on the original chosen-module tensor.
The independent zero weak-closure branch remains for the full Hermitian
exclusion. Source: Aschbacher–Smith 8.2.13(1), pp.722–723, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups commutatorElement

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Stellmacher ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter8.Section02.HermitianSource Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
set_option backward.isDefEq.respectTransparency false

/-- The original positive weak-closure Hermitian tensor branch is impossible. -/
theorem sourceOrbit_hermitian_tensor_positive_impossible
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
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n)
    (hw : 0 < globalW D.sourceOrbit T) : False := by
  obtain ⟨hn,_,_,_,z,hzne,hzo,hZ,_,hE,_,hprod,hVE,_,_,_⟩ :=
    D.sourceOrbit_hermitian_tensor_point_product
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw
  obtain ⟨_,_,_,_,hcommL⟩ := D.sourceOrbit_hermitian_tensor_core_commutators
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw
  rcases hn with rfl
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree hfield hmodel
  have hz : (z : G) ∈ centralizer (T : Set G) :=
    ((mem_omegaOneCenterAmbient_iff _ _).mp (hZ.le (mem_zpowers _))).2.2
  have hTz : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G) :=
    fun t ht => mem_centralizer_singleton_iff.mpr (hz t ht)
  obtain ⟨_,_,_,_,_,_,hcomp⟩ := D.sourceOrbit_hermitian_point_centralizer
    h hmany hV hnon hcommL d z hz hzne
  have hVX := (D.sourceOrbit_hermitian_point_core h hmany hV hnon hcommL d z hz hzne).2
  have hsections := D.sourceOrbit_hermitian_point_sections h hmany hV hnon hcommL d z hz hzne
  let Cz := centralizer ({(z : G)} : Set G)
  have hC : IsSQTK KnownSimple.IsKnownSimple Cz := h.simpleQTKE.involution_centralizer_sqtk hzo
  have hQ : IsSQTK KnownSimple.IsKnownSimple (Cz ⧸ pCore 2 Cz) := by
    refine ⟨?_,hC.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hC.stronglyQuasithin p hp ho)
  rw [hE] at hprod hVE
  exact point_quotient_exclusion L D.sourceOrbit T z hQ D.sylow_normalizes_component
    D.sourceOrbit_weakClosure_setup.normalizes hTz hcomp hVX hsections hprod hVE

/-- The complete positive-closure exclusion leaves precisely the original zero branch. -/
theorem sourceOrbit_hermitian_tensor_weakClosure_zero
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
    globalW D.sourceOrbit T = 0 := by
  by_contra hw
  exact D.sourceOrbit_hermitian_tensor_positive_impossible
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel (bot_lt_iff_ne_bot.mpr hw)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
