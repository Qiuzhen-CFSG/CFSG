module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.SpinActions

/-!
# The signed spin action on the orthogonal sum of its two halves

Restriction identifies the signed vectors on the second and third Parker axes
with `(δ₂(b), 0)` and `(0, δ₃(b))`. Transport of the orbit-function action
therefore constructs a monomial representation on `SpinDirectSum`, with its
orthogonal sum form and orthonormal basis. Its kernel fixes every actual `k1`
orbit, and its special central generators have the computed signs. The two
odd-automorphism formulas certify the exchange of halves inside this action.

The representation is constructed from permutations preserving the union of
axes and commuting with the actual `k1` and `z1`. These are the normalization
hypotheses for a restriction to an ambient group; no linear action or kernel
subgroup is assumed.

Source: Aschbacher, *Sporadic Groups*, Lemma 14.6 and the construction following
Lemma 27.3, printed pp. 146–147, including the spin part of Lemma 27.5(4).
The separate irreducibility module supplies the extraspecial-quotient adapter;
structural subgroup-kernel identifications belong to the triality assembly.
-/

@[expose] public section
open Atlas.Fischer Atlas.Codes
open Sporadic.Monster.Construction.TrialitySpin
open SignedModules SpinActions
noncomputable section
attribute [local instance] Classical.propDecidable

namespace Sporadic.Monster.Construction.TrialitySpin.SpinDirectSum

private theorem sumSpaceEquiv_delta_inl {X Y : Type*} (s : SignedSet X) (t : SignedSet Y) (x : X) :
    sumSpaceEquiv s t ((sumSigns s t).delta (Sum.inl x)) = (s.delta x, 0) := by
  classical
  apply Prod.ext
  · apply Subtype.ext
    funext y
    change ((sumSigns s t).delta (Sum.inl x)).val (Sum.inl y) = (s.delta x).val y
    simp [SignedSet.delta_apply, sumSigns, sumPairing]
  · apply Subtype.ext
    funext y
    change ((sumSigns s t).delta (Sum.inl x)).val (Sum.inr y) = 0
    simp [SignedSet.delta_apply, sumSigns, sumPairing]

private theorem sumSpaceEquiv_delta_inr {X Y : Type*} (s : SignedSet X) (t : SignedSet Y) (y : Y) :
    sumSpaceEquiv s t ((sumSigns s t).delta (Sum.inr y)) = (0, t.delta y) := by
  classical
  apply Prod.ext
  · apply Subtype.ext
    funext x
    change ((sumSigns s t).delta (Sum.inr y)).val (Sum.inl x) = 0
    simp [SignedSet.delta_apply, sumSigns, sumPairing]
  · apply Subtype.ext
    funext x
    change ((sumSigns s t).delta (Sum.inr y)).val (Sum.inr x) = (t.delta y).val x
    simp [SignedSet.delta_apply, sumSigns, sumPairing]

theorem restriction_vector2 (b : ParkerLoop) :
    spinRestriction (bothAxesDomain.vector ⟨axis2 b, Or.inl ⟨b, rfl⟩⟩) = (delta2 b, 0) := by
  let s := sumSigns secondAxisDomain.signedOrbits thirdAxisDomain.signedOrbits
  let e := s.transport bothAxesDomain.signedOrbits spinOrbitUnion spinOrbitUnion_sign
  have h := s.transport_delta bothAxesDomain.signedOrbits spinOrbitUnion spinOrbitUnion_sign
    (Sum.inl (secondAxisDomain.pairing.orbit (axis2Equiv b)))
  change e (s.delta _) = bothAxesDomain.vector _ at h
  change spinRestriction (bothAxesDomain.vector (axisUnion (Sum.inl (axis2Equiv b)))) = _
  refine (congrArg spinRestriction h.symm).trans ?_
  change sumSpaceEquiv _ _ (e.symm (e _)) = _
  rw [e.symm_apply_apply]
  exact sumSpaceEquiv_delta_inl _ _ _

theorem restriction_vector3 (b : ParkerLoop) :
    spinRestriction (bothAxesDomain.vector ⟨axis3 b, Or.inr ⟨b, rfl⟩⟩) = (0, delta3 b) := by
  let s := sumSigns secondAxisDomain.signedOrbits thirdAxisDomain.signedOrbits
  let e := s.transport bothAxesDomain.signedOrbits spinOrbitUnion spinOrbitUnion_sign
  have h := s.transport_delta bothAxesDomain.signedOrbits spinOrbitUnion spinOrbitUnion_sign
    (Sum.inr (thirdAxisDomain.pairing.orbit (axis3Equiv b)))
  change e (s.delta _) = bothAxesDomain.vector _ at h
  change spinRestriction (bothAxesDomain.vector (axisUnion (Sum.inr (axis3Equiv b)))) = _
  refine (congrArg spinRestriction h.symm).trans ?_
  change sumSpaceEquiv _ _ (e.symm (e _)) = _
  rw [e.symm_apply_apply]
  exact sumSpaceEquiv_delta_inr _ _ _

/-- The orthogonal sum form, pulled back through restriction. -/
def form : LinearMap.BilinForm ℝ SpinDirectSum :=
  bothAxesDomain.form.compl₁₂ spinRestriction.symm.toLinearMap spinRestriction.symm.toLinearMap

theorem form_eq (v w : SpinDirectSum) :
    form v w = secondAxisDomain.form v.1 w.1 + thirdAxisDomain.form v.2 w.2 := by
  change bothAxesDomain.form (spinRestriction.symm v) (spinRestriction.symm w) = _
  have h := spinRestriction_isometry (spinRestriction.symm v) (spinRestriction.symm w)
  simpa only [LinearEquiv.apply_symm_apply] using h.symm

theorem form_pos (v : SpinDirectSum) (hv : v ≠ 0) : 0 < form v v :=
  bothAxesDomain.form_pos _ (fun h => hv (spinRestriction.symm.injective (by simpa using h)))

def basis : Module.Basis bothAxesDomain.signedOrbits.toPairing.Orbit ℝ SpinDirectSum :=
  bothAxesDomain.basis.map spinRestriction

theorem basis_orthonormal (a b : bothAxesDomain.signedOrbits.toPairing.Orbit) :
    form (basis a) (basis b) = if a = b then 1 else 0 := by
  change bothAxesDomain.form (spinRestriction.symm (spinRestriction (bothAxesDomain.basis a)))
    (spinRestriction.symm (spinRestriction (bothAxesDomain.basis b))) = _
  simpa only [LinearEquiv.symm_apply_apply] using bothAxesDomain.basis_orthonormal a b

section Action
variable {G : Type*} [Group G] (ρ : G →* Equiv.Perm Triple)
  (hA : ∀ g a, a ∈ A ↔ ρ g a ∈ A)
  (hk : ∀ g a, ρ g (k1.val a) = k1.val (ρ g a))
  (hz : ∀ g a, ρ g (z1 a) = z1 (ρ g a))

/-- The actual signed-axis action in direct-sum coordinates. -/
def representation : Representation ℝ G SpinDirectSum :=
  spinRestriction.conjRingEquiv.toMonoidHom.comp
    (bothAxesDomain.inducedRepresentation ρ hA hk hz)

theorem representation_apply (g : G) (v : SpinDirectSum) :
    representation ρ hA hk hz g v =
      spinRestriction (bothAxesDomain.inducedRepresentation ρ hA hk hz g
        (spinRestriction.symm v)) := rfl

theorem representation_restriction (g : G) (v : SpinSpace) :
    representation ρ hA hk hz g (spinRestriction v) =
      spinRestriction (bothAxesDomain.inducedRepresentation ρ hA hk hz g v) := by
  rw [representation_apply, spinRestriction.symm_apply_apply]

theorem representation_kernel_iff (g : G) :
    representation ρ hA hk hz g = 1 ↔
      ∀ a ∈ A, ρ g a = a ∨ ρ g a = k1.val a := by
  change spinRestriction.conjRingEquiv (bothAxesDomain.inducedRepresentation ρ hA hk hz g) = 1 ↔ _
  rw [← spinRestriction.conjRingEquiv.map_one, spinRestriction.conjRingEquiv.injective.eq_iff]
  exact bothAxesDomain.inducedRepresentation_kernel_iff ρ hA hk hz g

theorem representation_isometry (g : G) (v w : SpinDirectSum) :
    form (representation ρ hA hk hz g v) (representation ρ hA hk hz g w) = form v w := by
  simp only [representation_apply, form, LinearMap.compl₁₂_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  exact bothAxesDomain.representation_isometry _ _ _ g _ _

theorem representation_monomial (g : G) (a : bothAxesDomain.signedOrbits.toPairing.Orbit) :
    ∃ b, representation ρ hA hk hz g (basis a) = basis b ∨
      representation ρ hA hk hz g (basis a) = -basis b := by
  obtain ⟨b, hb⟩ := bothAxesDomain.representation_monomial
    (bothAxesDomain.restrictPermutations ρ hA)
    (fun g a => Subtype.ext (hk g a.val)) (fun g a => Subtype.ext (hz g a.val)) g a
  refine ⟨b, ?_⟩
  change representation ρ hA hk hz g (spinRestriction (bothAxesDomain.basis a)) =
      spinRestriction (bothAxesDomain.basis b) ∨
    representation ρ hA hk hz g (spinRestriction (bothAxesDomain.basis a)) =
      -spinRestriction (bothAxesDomain.basis b)
  simp only [representation_restriction]
  rcases hb with hb | hb
  · exact Or.inl (congrArg spinRestriction hb)
  · right
    exact (congrArg spinRestriction hb).trans (map_neg spinRestriction _)

theorem representation_of_z1 (g : G) (hg : ρ g = z1) (v : SpinDirectSum) :
    representation ρ hA hk hz g v = -v := by
  rw [representation_apply, bothAxesDomain.inducedRepresentation_of_z1 ρ hA hk hz g hg,
    map_neg, spinRestriction.apply_symm_apply]

theorem representation_of_psi2_signOmega (g : G)
    (hg : ρ g = psi2 (parkerSign 1 parkerOmega)) : representation ρ hA hk hz g = 1 := by
  apply (representation_kernel_iff ρ hA hk hz g).2
  intro a ha
  rw [hg]
  exact psi2_signOmega_orbits ha

/-- Covariance on signed vectors ties the direct-sum action to the actual triples. -/
theorem representation_vector (g : G) (a b : bothAxesDomain.points)
    (hab : ρ g a.val = b.val) :
    representation ρ hA hk hz g (spinRestriction (bothAxesDomain.vector a)) =
      spinRestriction (bothAxesDomain.vector b) := by
  rw [representation_restriction]
  apply congrArg spinRestriction
  exact (bothAxesDomain.representation_vector _ _ _ g a).trans
    (congrArg bothAxesDomain.vector (Subtype.ext hab))

/-- The first half is carried to the second half by the actual odd first automorphism. -/
theorem representation_psiAut1Odd_delta2 (g : G) (e : Equiv.Perm ParkerLoop)
    (he : IsStandard e) (hε : e parkerOmega ≠ parkerOmega)
    (hg : ρ g = psiAut1 e) (b : ParkerLoop) :
    representation ρ hA hk hz g (delta2 b, 0) =
      (0, psiAut1Odd e he hε (delta2 b)) := by
  rw [psiAut1Odd_delta, ← restriction_vector2, ← restriction_vector3]
  apply representation_vector
  exact hg ▸ psiAut1_odd_axis e he hε b

/-- The reverse half has the corresponding signed formula under the same permutation. -/
theorem representation_psiAut1Odd_delta3 (g : G) (e : Equiv.Perm ParkerLoop)
    (he : IsStandard e) (hε : e parkerOmega ≠ parkerOmega)
    (hg : ρ g = psiAut1 e) (b : ParkerLoop) :
    representation ρ hA hk hz g (0, delta3 b) =
      (psiAut1OddBack e he hε (delta3 b), 0) := by
  rw [psiAut1OddBack_delta, ← restriction_vector3, ← restriction_vector2]
  apply representation_vector
  exact hg ▸ psiAut1_odd_axis3 e he hε b

end Action
end Sporadic.Monster.Construction.TrialitySpin.SpinDirectSum
