module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Basic
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.Representation.BinaryPermutation.OffenderFixedSpace
public import Theory.SpecificGroups.Alternating.EightNineInvolutionCounts.Basic
public import Mathlib.Tactic

/-!
# The moved plane of a fixed-point-free eight-letter involution

For `(01)(23)(45)(67)`, the even cubic `(024)(135)` commutes with the
involution. A displacement in the augmentation core is constant on each
swapped pair. If its class modulo constants is fixed by the cubic, it is
constant on all eight letters, so its class is zero. The cubic therefore
cycles the three nonzero vectors of the moved plane.

An odd permutation centralizing the representative prevents its symmetric
conjugacy class from splitting in A₈. Actual alternating conjugacy transports
the calculation, and the even witnesses belong to every subgroup containing
A₈. The rank-two hypothesis is the one supplied by the source involution.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
G.11.2(4–5), printed p.364 (PDF p.375), and the proof of 6.2.19,
printed p.691 (PDF p.708).
-/

@[expose] public section

namespace Representation.RankTwo.Symmetric
open _root_.Equiv BinaryPermutation

private abbrev Ω := Fin 8
private def fourPairs : Perm Ω := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7
private def rotation : Perm Ω := swap 0 2 * swap 2 4 * (swap 1 3 * swap 3 5)

private theorem fourPairs_even : fourPairs ∈ alternatingGroup Ω := by rw [Perm.mem_alternatingGroup]; decide +kernel
private theorem rotation_even : rotation ∈ alternatingGroup Ω := by rw [Perm.mem_alternatingGroup]; decide +kernel
private theorem rotation_cube : rotation ^ 3 = 1 := by decide +kernel
private theorem rotation_commutes : Commute rotation fourPairs := by
  unfold Commute SemiconjBy; decide +kernel

private theorem full_fixed_displacement (u : core Ω)
    (hfix : representation Ω rotation (representation Ω fourPairs u.val - u.val) =
      representation Ω fourPairs u.val - u.val) :
    representation Ω fourPairs u.val - u.val ∈ constants Ω := by
  have h2 := congrFun hfix 2
  have h4 := congrFun hfix 4
  change u.val 1 - u.val 0 = u.val 3 - u.val 2 at h2
  change u.val 3 - u.val 2 = u.val 5 - u.val 4 at h4
  have hs := u.property
  change ∑ i : Fin 8, u.val i = 0 at hs
  simp only [Fin.sum_univ_succ] at hs
  change u.val 0 + (u.val 1 + (u.val 2 + (u.val 3 + (u.val 4 +
    (u.val 5 + (u.val 6 + (u.val 7 + 0))))))) = 0 at hs
  rw [mem_constants_iff]
  refine ⟨u.val 1 - u.val 0, ?_⟩
  intro i
  fin_cases i
  · change u.val 1 - u.val 0 = _; rfl
  · change u.val 0 - u.val 1 = _
    simp [sub_eq_add_neg, CharTwo.neg_eq, add_comm]
  · change u.val 3 - u.val 2 = _; exact h2.symm
  · change u.val 2 - u.val 3 = _
    simpa [sub_eq_add_neg, CharTwo.neg_eq, add_comm] using h2.symm
  · change u.val 5 - u.val 4 = _; exact (h2.trans h4).symm
  · change u.val 4 - u.val 5 = _
    simpa [sub_eq_add_neg, CharTwo.neg_eq, add_comm] using (h2.trans h4).symm
  · change u.val 7 - u.val 6 = _
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hs + h4
  · change u.val 6 - u.val 7 = _
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hs + h4

private theorem rotation_fixed_moved (w : natural Ω)
    (hw : w ∈ movedSpace (naturalRepresentation Ω) fourPairs)
    (hc : naturalRepresentation Ω rotation w = w) : w = 0 := by
  obtain ⟨x, rfl⟩ := hw
  obtain ⟨u, rfl⟩ := coreToNatural_surjective x
  have he : naturalRepresentation Ω fourPairs (coreToNatural Ω u) - coreToNatural Ω u =
      coreToNatural Ω (coreRepresentation Ω fourPairs u - u) := by
    rw [map_sub, coreToNatural_equivariant]
  change naturalRepresentation Ω rotation
      (naturalRepresentation Ω fourPairs (coreToNatural Ω u) - coreToNatural Ω u) =
      naturalRepresentation Ω fourPairs (coreToNatural Ω u) - coreToNatural Ω u at hc
  change naturalRepresentation Ω fourPairs (coreToNatural Ω u) - coreToNatural Ω u = 0
  rw [he] at hc ⊢
  have hc' : representation Ω rotation (representation Ω fourPairs u.val - u.val) =
      representation Ω fourPairs u.val - u.val :=
    (deleted_fixed_iff_of_fixed_point rotation _ 6 (by decide +kernel)).mp
      (congrArg Subtype.val hc)
  apply Subtype.ext
  exact (Submodule.Quotient.mk_eq_zero _).mpr (full_fixed_displacement u hc')

private def fourPairsA : alternatingGroup Ω := ⟨fourPairs, fourPairs_even⟩
private def rotationA : alternatingGroup Ω := ⟨rotation, rotation_even⟩
private abbrev σ := alternatingNaturalRepresentation (Ω := Ω)

private theorem representative_transitive
    (hr : Module.finrank (ZMod 2) (movedSpace σ fourPairsA) = 2) :
    StabilizerTransitive σ (movedSpace σ fourPairsA) := by
  apply stabilizerTransitive_of_order_three σ fourPairsA rotationA hr
  · exact Subtype.ext rotation_commutes.eq
  · exact Subtype.ext rotation_cube
  · exact rotation_fixed_moved

private def actorEquiv (g : alternatingGroup Ω) : natural Ω ≃ₗ[ZMod 2] natural Ω where
  toLinearMap := σ g
  invFun := σ g⁻¹
  left_inv x := by
    change σ g⁻¹ (σ g x) = x
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]
  right_inv x := by
    change σ g (σ g⁻¹ x) = x
    simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply]

private theorem actorEquiv_intertwines (h g : alternatingGroup Ω) (x : natural Ω) :
    actorEquiv h (σ g x) = σ (MulAut.conj h g) (actorEquiv h x) := by
  change σ h (σ g x) = σ (h * g * h⁻¹) (σ h x)
  simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]

theorem alternating_fourPairs_transitive (v : alternatingGroup (Fin 8))
    (hv : v.val.cycleType = {2, 2, 2, 2})
    (hr : Module.finrank (ZMod 2)
      (movedSpace (alternatingNaturalRepresentation (Ω := Fin 8)) v) = 2) :
    StabilizerTransitive (alternatingNaturalRepresentation (Ω := Fin 8))
      (movedSpace (alternatingNaturalRepresentation (Ω := Fin 8)) v) := by
  have hc : IsConj fourPairsA v := by
    apply (alternatingGroup.EightNineInvolutionCounts.isConj_iff_of_odd_commuting
      fourPairsA v (swap 0 1) (by decide +kernel)
      (by unfold Commute SemiconjBy; decide +kernel)).mpr
    rw [hv]
    decide +kernel
  obtain ⟨h, hh⟩ := isConj_iff.mp hc.symm
  change MulAut.conj h v = fourPairsA at hh
  have he := finrank_movedSpace_transport σ σ (MulAut.conj h) (actorEquiv h)
    (actorEquiv_intertwines h) v
  have hr' : Module.finrank (ZMod 2) (movedSpace σ fourPairsA) = 2 := by
    rw [hh] at he
    exact he.symm.trans hr
  apply stabilizerTransitive_transport σ σ (MulAut.conj h) (actorEquiv h)
    (actorEquiv_intertwines h) v
  rw [hh]
  exact representative_transitive hr'

theorem subgroup_fourPairs_transitive (H : Subgroup (Perm (Fin 8)))
    (hH : alternatingGroup (Fin 8) ≤ H) (v : H)
    (hv : v.val.cycleType = {2, 2, 2, 2})
    (hr : Module.finrank (ZMod 2)
      (movedSpace ((naturalRepresentation (Fin 8)).comp H.subtype) v) = 2) :
    StabilizerTransitive ((naturalRepresentation (Fin 8)).comp H.subtype)
      (movedSpace ((naturalRepresentation (Fin 8)).comp H.subtype) v) := by
  have hvA : v.val ∈ alternatingGroup (Fin 8) := by
    rw [Perm.mem_alternatingGroup, Perm.sign_of_cycleType, hv]
    decide +kernel
  have ht := alternating_fourPairs_transitive ⟨v.val, hvA⟩ hv hr
  intro u hu hu0 w hw hw0
  obtain ⟨g, hg, hgu⟩ := ht u hu hu0 w hw hw0
  exact ⟨⟨g.val, hH g.property⟩, hg, hgu⟩

end Representation.RankTwo.Symmetric
