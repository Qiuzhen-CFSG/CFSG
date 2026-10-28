module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.HalfActions
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SpinIrreducible
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.DirectSum

/-!
# The actual triality action on the orthogonal sum of spin halves

The checked restriction isometry identifies the concrete spin action with
an action on `B1(A2) × B1(A3)`. On `NPlus` this is the product of the two
actual half actions; the odd first standard automorphisms exchange them
with the source square-weight sign. The kernel and distinguished scalar
actions follow from the constructed representation and its orbit geometry.

Source: Aschbacher, *Sporadic Groups*, Lemma 14.6 and the construction
following Lemma 27.3, printed pp. 146–147.
-/

@[expose] public section
noncomputable section
open Atlas.Fischer
namespace Sporadic.Monster.Construction.TrialitySpin.DirectSumAction
open SpinActions

/-- The unconditional action on the displayed orthogonal sum. -/
def representation : Representation ℝ N1 SpinDirectSum :=
  SpinDirectSum.representation SpinAction.permutations SpinAction.preserves_axes
    SpinAction.commutes_k1 SpinAction.commutes_z1

theorem representation_restriction (g : N1) (v : SpinSpace) :
    representation g (spinRestriction v) = spinRestriction (SpinAction.representation g v) :=
  SpinDirectSum.representation_restriction _ _ _ _ g v

/-- A representation equivalence, including the action, between the two realizations. -/
def restrictionEquiv : SpinAction.representation.Equiv representation :=
  .mk spinRestriction (fun g => LinearMap.ext (fun v => (representation_restriction g v).symm))

theorem restriction_isometry (v w : SpinSpace) :
    SpinDirectSum.form (spinRestriction v) (spinRestriction w) = bothAxesDomain.form v w := by
  rw [SpinDirectSum.form_eq]
  exact spinRestriction_isometry v w

theorem representation_kernel : representation.ker = J.subgroupOf N1 := by
  ext g
  change representation g = 1 ↔ g.val ∈ J
  exact (SpinDirectSum.representation_kernel_iff SpinAction.permutations SpinAction.preserves_axes
    SpinAction.commutes_k1 SpinAction.commutes_z1 g).trans (N1_orbit_kernel g.val g.prop)

theorem representation_isometry (g : N1) (v w : SpinDirectSum) :
    SpinDirectSum.form (representation g v) (representation g w) = SpinDirectSum.form v w :=
  SpinDirectSum.representation_isometry _ _ _ _ g v w

theorem representation_monomial (g : N1) (a : bothAxesDomain.signedOrbits.toPairing.Orbit) :
    ∃ b, representation g (SpinDirectSum.basis a) = SpinDirectSum.basis b ∨
      representation g (SpinDirectSum.basis a) = -SpinDirectSum.basis b :=
  SpinDirectSum.representation_monomial _ _ _ _ g a

theorem representation_z (v : SpinDirectSum) : representation SpinAction.z v = -v :=
  SpinDirectSum.representation_of_z1 _ _ _ _ SpinAction.z rfl v

theorem representation_c : representation SpinAction.c = 1 :=
  SpinDirectSum.representation_of_psi2_signOmega _ _ _ _ SpinAction.c rfl

/-- The odd first standard automorphism belongs to the actual first centralizer. -/
def standard (α : ParkerStandardGroup) : N1 := ⟨psiAut1N α, psiAut1N_mem_N1 α⟩

theorem representation_odd_delta2 (α : ParkerStandardGroup)
    (hα : α.val parkerOmega ≠ parkerOmega) (b : ParkerLoop) :
    representation (standard α) (delta2 b, 0) =
      (0, delta3 (parkerSign (golayQuarterWeight b.1) (α.val b))) := by
  exact (SpinDirectSum.representation_psiAut1Odd_delta2 SpinAction.permutations
    SpinAction.preserves_axes SpinAction.commutes_k1 SpinAction.commutes_z1
    (standard α) α.val α.prop hα rfl b).trans
      (congrArg (fun v : B1A3 => (0,v)) (psiAut1Odd_delta α.val α.prop hα b))

theorem representation_odd_delta3 (α : ParkerStandardGroup)
    (hα : α.val parkerOmega ≠ parkerOmega) (b : ParkerLoop) :
    representation (standard α) (0, delta3 b) =
      (delta2 (parkerSign (golayQuarterWeight b.1) (α.val b)), 0) := by
  exact (SpinDirectSum.representation_psiAut1Odd_delta3 SpinAction.permutations
    SpinAction.preserves_axes SpinAction.commutes_k1 SpinAction.commutes_z1
    (standard α) α.val α.prop hα rfl b).trans
      (congrArg (fun v : B1A2 => (v,0)) (psiAut1OddBack_delta α.val α.prop hα b))

/-- The source's exchange of the two whole halves, not only of their signed vectors. -/
theorem representation_odd (α : ParkerStandardGroup)
    (hα : α.val parkerOmega ≠ parkerOmega) (v : SpinDirectSum) :
    representation (standard α) v =
      (psiAut1OddBack α.val α.prop hα v.2, psiAut1Odd α.val α.prop hα v.1) := by
  have h2 : (representation (standard α)).comp (LinearMap.inl ℝ B1A2 B1A3) =
      (LinearMap.inr ℝ B1A2 B1A3).comp (psiAut1Odd α.val α.prop hα).toLinearMap := by
    apply firstSecond.geometry.vector_ext
    intro a
    obtain ⟨b,rfl⟩ := axis2Equiv.surjective a
    exact SpinDirectSum.representation_psiAut1Odd_delta2 SpinAction.permutations
      SpinAction.preserves_axes SpinAction.commutes_k1 SpinAction.commutes_z1
      (standard α) α.val α.prop hα rfl b
  have h3 : (representation (standard α)).comp (LinearMap.inr ℝ B1A2 B1A3) =
      (LinearMap.inl ℝ B1A2 B1A3).comp (psiAut1OddBack α.val α.prop hα).toLinearMap := by
    apply firstThird.geometry.vector_ext
    intro a
    obtain ⟨b,rfl⟩ := axis3Equiv.surjective a
    exact SpinDirectSum.representation_psiAut1Odd_delta3 SpinAction.permutations
      SpinAction.preserves_axes SpinAction.commutes_k1 SpinAction.commutes_z1
      (standard α) α.val α.prop hα rfl b
  calc
    _ = representation (standard α) ((v.1,0) + (0,v.2)) := by simp
    _ = representation (standard α) (v.1,0) + representation (standard α) (0,v.2) := map_add _ _ _
    _ = _ := by
      rw [show representation (standard α) (v.1,0) = (0,psiAut1Odd α.val α.prop hα v.1) from
        LinearMap.congr_fun h2 v.1,
        show representation (standard α) (0,v.2) = (psiAut1OddBack α.val α.prop hα v.2,0) from
        LinearMap.congr_fun h3 v.2]
      simp

/-- On the even subgroup the actual action is the product of its two restrictions. -/
theorem representation_even (g : NPlus) (v : SpinDirectSum) :
    representation (HalfActions.inclusion g) v =
      (HalfActions.secondRepresentation g v.1, HalfActions.thirdRepresentation g v.2) := by
  have h : (representation (HalfActions.inclusion g)).comp spinRestriction.toLinearMap =
      ((HalfActions.secondRepresentation g).prodMap (HalfActions.thirdRepresentation g)).comp
        spinRestriction.toLinearMap := by
    apply (domainGeometry bothAxesDomain).vector_ext
    rintro ⟨a,ha⟩
    rcases ha with ⟨b,rfl⟩ | ⟨b,rfl⟩
    · obtain ⟨c,hc⟩ := (HalfActions.preserves_axis2 g (axis2 b)).mp ⟨b,rfl⟩
      have hs : SpinAction.representation (HalfActions.inclusion g)
          (bothAxesDomain.vector ⟨axis2 b, Or.inl ⟨b,rfl⟩⟩) =
          bothAxesDomain.vector ⟨axis2 c, Or.inl ⟨c,rfl⟩⟩ := by
        exact (SpinAction.representation_vector (HalfActions.inclusion g) _).trans
          (congrArg bothAxesDomain.vector (Subtype.ext hc.symm))
      have hh := induced_delta2 HalfActions.permutations HalfActions.preserves_axis2
        HalfActions.commutes_k1 HalfActions.commutes_z1 g b c hc.symm
      change representation (HalfActions.inclusion g)
          (spinRestriction (bothAxesDomain.vector ⟨axis2 b, Or.inl ⟨b,rfl⟩⟩)) = _
      calc
        _ = spinRestriction (bothAxesDomain.vector ⟨axis2 c, Or.inl ⟨c,rfl⟩⟩) :=
          (representation_restriction _ _).trans (congrArg spinRestriction hs)
        _ = (delta2 c, 0) := SpinDirectSum.restriction_vector2 c
        _ = ((HalfActions.secondRepresentation g).prodMap (HalfActions.thirdRepresentation g))
            (delta2 b, 0) := by
          change (delta2 c, 0) = (HalfActions.secondRepresentation g (delta2 b),
            HalfActions.thirdRepresentation g 0)
          rw [show HalfActions.secondRepresentation g (delta2 b) = delta2 c from hh, map_zero]
        _ = _ := congrArg ((HalfActions.secondRepresentation g).prodMap
          (HalfActions.thirdRepresentation g)) (SpinDirectSum.restriction_vector2 b).symm
    · obtain ⟨c,hc⟩ := (HalfActions.preserves_axis3 g (axis3 b)).mp ⟨b,rfl⟩
      have hs : SpinAction.representation (HalfActions.inclusion g)
          (bothAxesDomain.vector ⟨axis3 b, Or.inr ⟨b,rfl⟩⟩) =
          bothAxesDomain.vector ⟨axis3 c, Or.inr ⟨c,rfl⟩⟩ := by
        exact (SpinAction.representation_vector (HalfActions.inclusion g) _).trans
          (congrArg bothAxesDomain.vector (Subtype.ext hc.symm))
      have hh : HalfActions.thirdRepresentation g (delta3 b) = delta3 c := by
        calc
          _ = thirdAxisDomain.vector
              (thirdAxisDomain.restrictPermutations HalfActions.permutations
                HalfActions.preserves_axis3 g (axis3Equiv b)) :=
            thirdAxisDomain.representation_vector
              (thirdAxisDomain.restrictPermutations HalfActions.permutations HalfActions.preserves_axis3)
              (fun g a => Subtype.ext (HalfActions.commutes_k1 g a.val))
              (fun g a => Subtype.ext (HalfActions.commutes_z1 g a.val)) g (axis3Equiv b)
          _ = delta3 c := congrArg thirdAxisDomain.vector (Subtype.ext hc.symm)
      change representation (HalfActions.inclusion g)
          (spinRestriction (bothAxesDomain.vector ⟨axis3 b, Or.inr ⟨b,rfl⟩⟩)) = _
      calc
        _ = spinRestriction (bothAxesDomain.vector ⟨axis3 c, Or.inr ⟨c,rfl⟩⟩) :=
          (representation_restriction _ _).trans (congrArg spinRestriction hs)
        _ = (0, delta3 c) := SpinDirectSum.restriction_vector3 c
        _ = ((HalfActions.secondRepresentation g).prodMap (HalfActions.thirdRepresentation g))
            (0, delta3 b) := by
          change (0, delta3 c) = (HalfActions.secondRepresentation g 0,
            HalfActions.thirdRepresentation g (delta3 b))
          rw [hh, map_zero]
        _ = _ := congrArg ((HalfActions.secondRepresentation g).prodMap
          (HalfActions.thirdRepresentation g)) (SpinDirectSum.restriction_vector3 b).symm
  obtain ⟨w,rfl⟩ := spinRestriction.surjective v
  exact LinearMap.congr_fun h w

/-- Irreducibility is retained under the concrete equivariant restriction isometry. -/
theorem representation_irreducible : Representation.IsIrreducible representation := by
  let : Representation.IsIrreducible SpinAction.representation := SpinAction.representation_irreducible
  let : Nontrivial SpinDirectSum :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_spinDirectSum]; norm_num)
  have : Nontrivial (Subrepresentation representation) := by
    refine ⟨⟨⊥,⊤,?_⟩⟩
    intro h
    exact (bot_ne_top : (⊥ : Submodule ℝ SpinDirectSum) ≠ ⊤)
      (congrArg Subrepresentation.toSubmodule h)
  constructor
  intro W
  let W' : Subrepresentation SpinAction.representation :=
    { toSubmodule := W.toSubmodule.comap spinRestriction.toLinearMap
      apply_mem_toSubmodule := by
        intro g v hv
        change spinRestriction (SpinAction.representation g v) ∈ W
        rw [← representation_restriction]
        exact W.apply_mem_toSubmodule g hv }
  have hmap : Submodule.map spinRestriction.toLinearMap W'.toSubmodule = W.toSubmodule :=
    Submodule.map_comap_eq_of_surjective spinRestriction.surjective _
  rcases eq_bot_or_eq_top W' with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    rw [← hmap, h]
    exact Submodule.map_bot _
  · right
    apply Subrepresentation.toSubmodule_injective
    rw [← hmap, h]
    exact Submodule.map_comap_eq_of_surjective spinRestriction.surjective ⊤

end Sporadic.Monster.Construction.TrialitySpin.DirectSumAction
