module

public import Theory.GroupTheory.CComponent.TwoComponent.Involution
public import Theory.SpecificGroups.Suzuki.RankOneRoots
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki

/-!
# B₂ for the Suzuki family

The odd outer index makes every involutory automorphism inner. Centerlessness
then gives an actual involution of the concrete Suzuki group, whose centralizer
is a two-group by the root calculation. Such a fixed group is solvable and
therefore has no two-components.

Sources: GLS II, Definition 2.4; Huppert--Blackburn III, XI.3.1 and XI.3.3;
GLS IV, Chapter 4, Lemma 3.1(b), for the inner-field automorphism description.
-/

public section

open Subgroup Theory.GroupTheory

namespace BenderSuzuki.MatrixGroups

/-- The actual fixed subgroup of every Suzuki involutory automorphism is a two-group. -/
theorem suzuki_involution_fixed_isPGroup (m : ℕ) (hm : 1 ≤ m)
    (a : MulAut (SuzukiMatrixGroup m)) (ha : orderOf a = 2) :
    IsPGroup 2 a.fixedSubgroup := by
  have hsq : a ^ 2 = 1 := by simpa only [ha] using pow_orderOf_eq_one a
  obtain ⟨b, hb, _⟩ := ZD.suzuki_involutoryAut_inner_and_twoRank m hm a hsq
  subst a
  have hb1 : b ≠ 1 := by
    intro h
    simp [h] at ha
  have hbo : orderOf b = 2 :=
    orderOf_eq_prime (ZD.suzuki_conj_sq_eq_one m hm b hsq) hb1
  obtain ⟨_, _, _, _, _, hc⟩ := suzuki_involution_root_geometry m (by omega) b hbo
  rwa [MulAut.fixedSubgroup_conj]

/-- Every group in the full Suzuki parameter range satisfies the B₂ condition. -/
theorem suzuki_hasInvolutoryB2 (m : ℕ) (hm : 1 ≤ m) :
    HasInvolutoryB2 (SuzukiMatrixGroup m) := by
  apply HasInvolutoryB2.of_fixed_solvable
  intro a ha
  let := (suzuki_involution_fixed_isPGroup m hm a ha).isNilpotent
  infer_instance

end BenderSuzuki.MatrixGroups
