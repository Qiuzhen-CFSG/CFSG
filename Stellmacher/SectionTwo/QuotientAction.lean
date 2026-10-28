module

public import Stellmacher.SectionsOneToFourDefs
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Algebra.GroupWithZero.Action.End

/-!
# The faithful quotient action on V

For Section 2, V is the normal closure of the central involutions of a
Sylow 2-subgroup, and C is its centralizer. Any surjection q with kernel C
therefore gives a faithful action of its codomain on V by automorphisms.
The named action below is an explicit reusable instance; its computation
lemma identifies the action of q g with conjugation by g.

We lift the conjugation homomorphism to MulAut V through q. Membership in
the centralizer makes the kernel act trivially, and conversely any element
fixing all of V lifts to that centralizer, hence is trivial in the quotient.
For every ambient subgroup A, the intrinsic points fixed by q(A) map
injectively onto V ∩ C_G(A). The subgroup image equality also transports
fixed-space decompositions in the opposite-conjugate step of (2.3); its
cardinality corollary supplies the offender inequality. No finiteness, solvability, or elementary-abelian
assumption is needed here.

This supplies the quotient-action setup in Stellmacher (2.2), journal p.20,
in `refs/latex/stellmacher-n-group.tex`, independently of the classification
results subsequently applied to this action.
-/

namespace Stellmacher.SectionTwo

universe u v
variable {G : Type u} [Group G] (S : Sylow 2 G)
  {barG : Type v} [Group barG] (q : G →* barG)
  (hq : Function.Surjective q) (hker : q.ker = cSubgroup S)

public noncomputable abbrev quotientConjugationAction :
    MulDistribMulAction barG (vSubgroup S) := by
  classical
  letI : (vSubgroup S).Normal := Subgroup.normalClosure_normal
  let act : G →* MulAut (vSubgroup S) := MulAut.conjNormal
  have hact : q.ker ≤ act.ker := by
    intro g hg
    rw [hker] at hg
    change g ∈ Subgroup.centralizer (vSubgroup S : Set G) at hg
    rw [Subgroup.mem_centralizer_iff] at hg
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change g * (x : G) * g⁻¹ = x
    rw [← hg x x.property, mul_inv_cancel_right]
  exact MulDistribMulAction.compHom (vSubgroup S)
    (q.liftOfSurjective hq ⟨act, hact⟩)

public theorem quotientConjugationAction_smul_coe (g : G) (x : vSubgroup S) :
    letI := quotientConjugationAction S q hq hker
    ((q g • x : vSubgroup S) : G) = g * (x : G) * g⁻¹ := by
  let : (vSubgroup S).Normal := Subgroup.normalClosure_normal
  change (((q.liftOfSurjective hq _ : barG →* MulAut (vSubgroup S)) (q g)) x : G) = _
  rw [MonoidHom.liftOfRightInverse_comp_apply]
  rfl

public theorem quotientConjugationAction_faithful :
    letI := quotientConjugationAction S q hq hker
    fixingSubgroup barG (Set.univ : Set (vSubgroup S)) = ⊥ := by
  let := quotientConjugationAction S q hq hker
  apply bot_unique
  intro b hb
  obtain ⟨g, rfl⟩ := hq b
  have hg : g ∈ q.ker := by
    rw [hker]
    change g ∈ Subgroup.centralizer (vSubgroup S : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [mem_fixingSubgroup_iff] at hb
    have hfix := hb ⟨x, hx⟩ (Set.mem_univ _)
    have heq := congrArg Subtype.val hfix
    rw [quotientConjugationAction_smul_coe S q hq hker] at heq
    exact (mul_inv_eq_iff_eq_mul.mp heq).symm
  exact hg

public theorem quotientConjugationAction_fixedPoints_image_map
    {G : Type u} [Group G] (S : Sylow 2 G)
    {barG : Type v} [Group barG] (q : G →* barG)
    (hq : Function.Surjective q) (hker : q.ker = cSubgroup S)
    (A : Subgroup G) :
    letI := quotientConjugationAction S q hq hker
    (FixedPoints.subgroup (A.map q) (vSubgroup S)).map
      (vSubgroup S).subtype = vSubgroup S ⊓ Subgroup.centralizer (A : Set G) := by
  let := quotientConjugationAction S q hq hker
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.property, ?_⟩
    change (y : G) ∈ Subgroup.centralizer (A : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hfix := (FixedPoints.mem_subgroup (M := A.map q) (a := y)).mp hy
      ⟨q a, Subgroup.mem_map_of_mem q ha⟩
    change q a • y = y at hfix
    have heq := congrArg Subtype.val hfix
    rw [quotientConjugationAction_smul_coe S q hq hker] at heq
    exact mul_inv_eq_iff_eq_mul.mp heq
  · rintro ⟨hxV, hxA⟩
    refine ⟨⟨x, hxV⟩, ?_, rfl⟩
    change (⟨x, hxV⟩ : vSubgroup S) ∈ FixedPoints.subgroup (A.map q) (vSubgroup S)
    rw [FixedPoints.mem_subgroup]
    intro a
    obtain ⟨a₀, ha₀, heq⟩ := a.property
    apply Subtype.ext
    change ((a.val • (⟨x, hxV⟩ : vSubgroup S) : vSubgroup S) : G) = x
    rw [← heq, quotientConjugationAction_smul_coe S q hq hker]
    change x ∈ Subgroup.centralizer (A : Set G) at hxA
    rw [Subgroup.mem_centralizer_iff] at hxA
    rw [hxA a₀ ha₀, mul_inv_cancel_right]

public theorem quotientConjugationAction_fixedPoints_card
    {G : Type u} [Group G] (S : Sylow 2 G)
    {barG : Type v} [Group barG] (q : G →* barG)
    (hq : Function.Surjective q) (hker : q.ker = cSubgroup S)
    (A : Subgroup G) :
    letI := quotientConjugationAction S q hq hker
    Nat.card (FixedPoints.subgroup (A.map q) (vSubgroup S)) =
      Nat.card (vSubgroup S ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := by
  let := quotientConjugationAction S q hq hker
  rw [← quotientConjugationAction_fixedPoints_image_map S q hq hker A,
    Subgroup.card_map_of_injective (vSubgroup S).subtype_injective]

end Stellmacher.SectionTwo
