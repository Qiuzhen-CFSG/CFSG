module

public import Theory.SpecificGroups.G2.MultiplierThree.UpperBound.LocalReduction
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddTwoPrimary.OrthogonalMap.QuaternionTwist
public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.CharacterGeometry.InvolutionConjugacy

/-!
# The concrete ternary orthogonal subgroup and its involution fusion

The split-quaternion map over ZMod 3, extended by the simultaneous matrix
conjugation of determinant minus one, has the diagonal scalar kernel.
Its image has order 576 and odd index 7371 in the actual octonion group.
The already proved ternary involution-line conjugacy implies conjugacy of
its marked scalar, outer, and paired involutions. These are the geometric
inputs of the double-cover splitting in `InvolutionLift.RankOne`.

Source: the local calculation underlying Aschbacher–Smith I.1.4(2), printed
p.408 (PDF p.419), and GLS3 §6.1. The split-octonion and quaternion-coordinate
maps retain the licensed ATLAS realization; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

namespace Atlas.G2.FiniteCover.MultiplierThree.InvolutionLift
open Subgroup
open MultiplierOrdinary.OddTwoPrimary

/-- The actual quaternion-coordinate map, with outer determinant minus one. -/
def localInclusion := OrthogonalMap.inclusion (1 : ZMod 3) one_ne_zero

theorem localInclusion_kernel (x) : localInclusion x = 1 ↔
    x = 1 ∨ x = SemidirectProduct.inl (-1,-1) :=
  OrthogonalMap.inclusion_kernel (1 : ZMod 3) one_ne_zero (by decide) x

/-- Exact order and index of the image of the concrete ternary local map. -/
theorem localInclusion_card_and_index :
    Nat.card localInclusion.range = 576 ∧ localInclusion.range.index = 7371 := by
  let D := (RankOne 3 × RankOne 3) ⋊[OrthogonalMap.action (1 : ZMod 3) one_ne_zero] C2
  let d : D := SemidirectProduct.inl (-1,-1)
  have hd : localInclusion d = 1 := (localInclusion_kernel d).mpr (Or.inr rfl)
  have hdn : d ≠ 1 := by
    intro h
    have h1 : (-1 : RankOne 3) = 1 := congrArg (fun x : D => x.left.1) h
    exact (by decide : (-1 : RankOne 3) ≠ 1) h1
  have hk : Nat.card localInclusion.ker = 2 := by
    apply (Nat.card_eq_two_iff' (1 : localInclusion.ker)).mpr
    refine ⟨⟨d,hd⟩, fun h => hdn (congrArg Subtype.val h), ?_⟩
    intro x hx
    rcases (localInclusion_kernel x).mp x.property with h | h
    · exact (hx (Subtype.ext h)).elim
    · exact Subtype.ext h
  have hD : Nat.card D = 1152 := by
    rw [SemidirectProduct.card, Nat.card_prod, Atlas.card_sl_two]
    norm_num [C2]
  have hlocal : Nat.card localInclusion.range = 576 := by
    have he := localInclusion.ker.card_mul_index
    rw [index_ker, hk, hD] at he
    omega
  refine ⟨hlocal, ?_⟩
  have he := localInclusion.range.card_mul_index
  rw [hlocal, card_Model] at he
  norm_num at he
  omega

/-- The local model is constructed on the literal ternary split-octonion group. -/
def localModel : LocalModel 3 (Model (ZMod 3)) where
  action := OrthogonalMap.action (1 : ZMod 3) one_ne_zero
  inclusion := localInclusion
  kernel := localInclusion_kernel
  odd_index := by rw [localInclusion_card_and_index.2]; decide

/-- Involution-line conjugacy gives actual element conjugacy, since a line
of order two has just one nonidentity element. -/
theorem involutions_isConj (x y : Model (ZMod 3))
    (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  classical
  have hi : orderOf TernaryLocals.involution = 2 :=
    orderOf_eq_prime_iff.mpr ⟨TernaryLocals.involution_sq, TernaryLocals.involution_ne_one⟩
  have hc (z : Model (ZMod 3)) (hz : orderOf z = 2) :
      IsConj TernaryLocals.involution z := by
    have hcard : Nat.card (zpowers z) = 2 := (Nat.card_zpowers z).trans hz
    have hsq : z ^ 2 = 1 := by simpa only [hz] using pow_orderOf_eq_one z
    obtain ⟨g,hg⟩ :=
      TernaryLocals.CharacterGeometry.InvolutionConjugacy.elementary_card_two_conjugate
        (zpowers z) (IsElementaryAbelian.zpowers_of_pow_eq_one hsq) hcard
    have hzmem : z ∈ (zpowers TernaryLocals.involution).map (MulAut.conj g).toMonoidHom :=
      hg ▸ mem_zpowers z
    obtain ⟨w,hw,hwz⟩ := hzmem
    have hw' : w = 1 ∨ w = TernaryLocals.involution := by
      have hwfin := (mem_zpowers_iff_mem_range_orderOf
        (x := TernaryLocals.involution) (y := w)).mp hw
      obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hwfin
      have hn2 : n < 2 := by simpa only [hi, Finset.mem_range] using hn
      have hn01 : n = 0 ∨ n = 1 := by omega
      rcases hn01 with rfl | rfl
      · exact Or.inl (by simpa using he.symm)
      · exact Or.inr (by simpa using he.symm)
    rcases hw' with rfl | rfl
    · have hz1 : z = 1 := by simpa using hwz.symm
      simp [hz1] at hz
    · exact isConj_iff.mpr ⟨g,hwz⟩
  exact (hc x hx).symm.trans (hc y hy)

private theorem scalar_image_order : orderOf (localModel.inclusion localModel.scalar) = 2 := by
  apply orderOf_eq_prime_iff.mpr
  refine ⟨by rw [← map_pow, localModel.scalar_sq, map_one], ?_⟩
  intro h
  rcases (localModel.kernel _).mp h with h | h
  · exact (by decide : (-1 : RankOne 3) ≠ 1)
      (congrArg (fun x : localModel.Domain => x.left.1) h)
  · exact (by decide : (-1 : RankOne 3) ≠ 1)
      (congrArg (fun x : localModel.Domain => x.left.2) h).symm

/-- Fusion of the actual outer involution with the scalar involution. -/
theorem outer_fusion :
    IsConj (localModel.inclusion localModel.scalar) (localModel.inclusion localModel.outer) :=
  involutions_isConj _ _ scalar_image_order localModel.outer_image_order

/-- Fusion of the paired order-four image kills the diagonal lift defect. -/
theorem paired_fusion :
    IsConj (localModel.inclusion localModel.scalar) (localModel.inclusion localModel.paired) :=
  involutions_isConj _ _ scalar_image_order localModel.paired_image_order

end Atlas.G2.FiniteCover.MultiplierThree.InvolutionLift
