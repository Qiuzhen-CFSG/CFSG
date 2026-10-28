module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourRadicalDisplacement
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianOrdinaryExclusion

/-!
# Whole odd-normalizer control for the original Hermitian nine-space

The literal tensor marking supplies the original order 512 and the
original non-FF setup supplies zero fixed space. These discharge the
ordinary J₄ exclusion with the full covering component retained.
The previously excluded normal J₄ alternative leaves the ordinary one
for any escaping noncubic elementary actor. Its exclusion therefore gives
containment of the actor's entire normalizer in the original N_G(L).

This is the whole-normalizer step required for each extraspecial Sylow
center in 8.2.7; odd-core containment alone was insufficient.
Source: Aschbacher--Smith 4.4.3 and Remark 4.4.2, pp.619,623,
as applied in 8.2.7, p.718, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
open Chapter4.Section02.RankOneReciprocalEscape
open Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual chosen-module tensor excludes its ordinary J4 cover. -/
theorem sourceOrbit_hermitian_no_ordinary_janko
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2)
    {A J H W : Subgroup G} (hw : Witness L D.sourceOrbit A J H W)
    (K : Subgroup H) (hK : IsComponent H K) : False := by
  obtain ⟨e⟩ := D.sourceOrbit_hermitian_field_four_ordinary_janko
    h hmany hV hnon d B eQ hfield hw K hK
  have hw' : Witness L V A J H W := by simpa only [hV] using hw
  have hfix : V ⊓ centralizer (L : Set G) = ⊥ :=
    (D.sourceOrbit_fixed_and_thompson_of_many h hmany hnon).1
  have hcard : Nat.card V = 512 := by
    rw [hV]
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive D.sourceOrbit)
    change Nat.card D.sourceOrbit = _ at hc
    rw [Nat.card_zmod,(D.hermitianOrbitCoordinates 1 d).finrank_eq,finrank_binary] at hc
    exact hc
  exact D.sourceOrbit_hermitian_ordinary_false_of_card h.toHypothesis1221 hV hfix hcard
    eQ (by rw [B.card_eq,hfield]; decide) hnon hw' K hK e

/-- Control of the whole normalizer, for every actual noncubic elementary
actor in the original module centralizer. -/
theorem sourceOrbit_hermitian_field_four_oddActor_normalizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2)
    {p : ℕ} (hp : p.Prime) (hgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G)) :
    normalizer (A : Set G) ≤ normalizer (L : Set G) := by
  by_contra hout
  obtain ⟨J,H,W,hw,K,hK,_⟩ := D.sourceOrbit_hermitian_field_four_oddActor_pushingUp
    h hmany hV hnon d B eQ hfield hp hgt A hne hAe hA hout
  exact D.sourceOrbit_hermitian_no_ordinary_janko h hmany hV hnon d B eQ hfield hw K hK

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
