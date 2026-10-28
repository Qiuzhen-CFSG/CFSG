module
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels.BlockEightCentralizers
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase.ModelAction.SylowAction

/-!
# The enlarged natural-block exclusion in E.6.25

The original V-action on an actual centralizer block is inner by elements
of the common Sylow omega-center. Applied to the involution in U/W, the
conjugating element is noncentral because the induced automorphism has order
two. In an L₂(8) block its centralizer is a two-group, contradicting the
relative C-component supplied by the original enlargement.

The only earlier local input here is E.6.21, expressed as OddCoreFree.
The proof constructs the inner action via the established common-Sylow
block theorem and preserves the original subgroup J and automorphism.

Source: Aschbacher–Smith, E.6.25, printed p.256 (PDF p.267).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels
open Hyperplanes.Enlargement Hyperplanes.Enlargement.BlockInspection
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L W J : Subgroup G}

/-- An actual two-factor enlargement cannot be a natural L₂(8) block. -/
theorem TwoCentralEnlargement.not_block_eight
    (h : HypothesisE61 K T M V) (ho : OddCoreFree V)
    (d : TwoCentralEnlargement M V U L W J) (hUV : U ≤ V)
    (hJ : CentralizerBlock W J) (hmodel : ChapterC.IsL2EvenBlock J 3) : False := by
  obtain ⟨t,ht,_,_,_,_,hL,a,ha,hact,_,hf⟩ := d.action
  obtain ⟨S,_,hinner⟩ := BlockCase.block_common_sylow_action h ho d.obstruction hJ
  obtain ⟨z,hz,hzact⟩ := hinner t (hUV ht)
  have haz : a = MulAut.conj z := by
    apply MulEquiv.ext
    intro x
    exact Subtype.ext ((hact x).trans (hzact x).symm)
  have hnz : z ∉ center J := by
    intro hzcen
    have ha1 : a = 1 := by
      apply MulEquiv.ext
      intro x
      rw [haz]
      change z * x * z⁻¹ = x
      rw [← mem_center_iff.mp hzcen x, mul_inv_cancel_right]
    simp [ha1] at ha
  have hfix : a.fixedSubgroup = centralizer ({z} : Set J) := by
    rw [haz, MulAut.fixedSubgroup_conj]
  have hp : IsPGroup 2 a.fixedSubgroup := by
    rw [hfix]
    exact blockEightCentralizer_isPGroup hmodel S z hz hnz
  let := hp.isNilpotent
  exact fixedSubgroup_not_solvable hL hf inferInstance
end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels
