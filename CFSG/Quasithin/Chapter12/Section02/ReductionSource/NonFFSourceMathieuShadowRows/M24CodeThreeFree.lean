module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M24CodeNonNormalization
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.Nonsolvable
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.PerfectResidualRank

/-!
# The original M24-code parabolic has order prime to three

The original parabolic is nonsolvable, so its two-residual is perfect.
It centralizes the full local 3.A6 quotient, whose cubic rank is two.
In the actual local join, SQTK bounds the cubic rank by two. Perfect
central-cover transfer removes central cubic torsion from the residual,
and rank addition forces the original parabolic to have cubic rank zero.
All original actors and intrinsic two-core kernels are retained.

Source: Aschbacher--Smith, proof of 8.2.9(3), printed p.720,
refs/quasithin.pdf. This is the three-free step, not yet the code exclusion.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode Atlas.Codes
open MathieuCode.SextetLayers.CoordinateTransport
open Chapter7.NormalizedSource.MathieuShadowRows
open Chapter8.Section02.HermitianSource Chapter8.Section02.MathieuShadowRows
open Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.Normalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original M24-code parabolic has order prime to three, retaining
its original orbit, selected pair and full local two-core. -/
theorem sourceOrbit_m24_code_parabolic_three_free
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Code)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      codeRepresentation (a b) (E v))
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ¬ 3 ∣ Nat.card H := by
  obtain ⟨h28,_⟩ := D.sourceOrbit_m24_hstar_setup h hmany hV hq hnon hH
  obtain ⟨t,ht,htP,htM⟩ := h28.minimal
  let : Group.IsPerfect (pResidual 2 H) :=
    ChapterB.minimalParabolic_nonsolvable_residual_perfect t htP
      (D.sourceOrbit_m24_code_parabolic_not_solvable h hmany hV hq hnon a E hE hH)
  obtain ⟨I,i,S,s,hw,hOff,hfix,hker,hIC,hr,hU,hUT,hTU,⟨e⟩,hcomm,hRI,hRP,
    hgen,hHN,hresC,hc,hcore,h3,h5,hn,hHR,hact,hK⟩ :=
    D.sourceOrbit_m24_code_parabolic_pair_of_many h hmany hV hq hnon a E hE hH
  let A := offenderNormalizer D.sourceOrbit i.val⁻¹
  let U := D.sourceOrbit ⊓ centralizer (A : Set G)
  let R := localResidual L U
  have hUne : U ≠ ⊥ := by
    intro hz
    change rank U = 4 at hU
    rw [hz,Representation.BinaryOffender.rank_bot] at hU
    omega
  have hlocal : IsTwoLocal (normalizer (U : Set G)) :=
    ⟨U,hUne,(IsElementaryAbelian.isPGroup 2 D.sourceOrbit).to_le inf_le_left,rfl⟩
  have hjoin : H ⊔ R ≤ normalizer (U : Set G) :=
    sup_le hHN ((localResidual_le L U).trans inf_le_right)
  have hj : primeRank 3 (H ⊔ R : Subgroup G) ≤ 2 :=
    (_root_.primeRank_le_of_injective 3 (inclusion hjoin) (inclusion_injective hjoin)).trans
      ((h.simpleQTKE.twoLocal_sqtk hlocal).stronglyQuasithin 3 (by decide) (by decide))
  have hR : 2 ≤ primeRank 3 R := calc
    2 ≤ primeRank 3 (R ⧸ pCore 2 R) := by
      rw [primeRank_congr 3 e]
      exact Hexacode.two_le_primeRank_even
    _ ≤ primeRank 3 R := primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup
  exact ResidualCentralizerRank.rank_zero_of_perfect_residual_normalized_factor
    (by decide) H R hHR hc h3 hR hj

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
