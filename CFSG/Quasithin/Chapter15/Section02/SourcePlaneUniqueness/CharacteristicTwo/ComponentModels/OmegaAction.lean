module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.OmegaAction.PlaneInput
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.OmegaAction.Transport
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.OmegaAction.RestrictedActions

/-!
# The Omega/index-six connector: source reduction and transport

The original NI ≤ MI branch is proved in Reduction. Otherwise the actual
Sz(2) image is excluded and the residual image in genuine Omega is nonnormal.
The finite calculation still required is the recognition of this subgroup
as the stabilizer of one of the two noncentral points of the fixed plane.
Once that calculation supplies its actual point and image isomorphism,
the theorem below constructs the original complement and faithful S₃ action,
computes index six, and applies the literal pushing-up setup.
Transport also applies the resulting action to the escaping-component consumer.

This module does not yet assert the unconditional 15.2.18(3) alternative.
Final assembly remains qt-e-152-component-omega-connector. Earlier restricted
actions and the distinguished inverting involution are supplied by
qt-e-152-plane-geometry and qt-e-152-small-parabolic. The finite nonnormal
residual recognition is a separate remaining obligation.

Source: Aschbacher--Smith, 15.2.13--14 and 15.2.18(3)--19(2),
printed pp.1112--1113, refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.OmegaAction
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open Chapter1.RadicalExclusions
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The source residual obstruction survives the actual coordinate isomorphism
into the Siegel-generated Omega group. This is the input for finite recognition. -/
theorem omega_action_reduction (hI : PlaneEscapes Mc ZS I)
    (ha : letI := hsource.prepared.elementary;
      Nonempty (internalActionImage M V hsource.prepared.normalized ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
      SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized))
    (hout : ¬ M ⊓ I ≤ Mc ⊓ I) :
    letI := hsource.prepared.elementary;
    ∃ (x : Additive V ≃ₗ[ZMod 2] OrthogonalFourBinary.Space)
      (a : internalActionImage M V hsource.prepared.normalized ≃* OrthogonalFourBinary.omega),
      (∀ g v, x (imageRepresentation M V hsource.prepared.normalized g v) =
        (a g).val.val (x v)) ∧
      ¬ ((pResidual 2 ((intersectionImage hsource I).map a.toMonoidHom)).map
        ((intersectionImage hsource I).map a.toMonoidHom).subtype).Normal := by
  let := hsource.prepared.elementary
  obtain ⟨x,a,hx⟩ := (omega_of_restricted_actions d hI ha hout).2.2.2.2
  refine ⟨x,a,hx,?_⟩
  rw [←map_embedded_pResidual]
  intro hn
  exact residualImage_not_normal d hI hout ((MulEquiv.normal_map_iff (f := a)).mp hn)

/-- Lift the finite stabilizer recognition, including its actual point, to
all the original complement, centralizer, index and pushing-up conclusions.
The point-stabilizer equality and image isomorphism remain model inputs. -/
theorem original_stabilizer_consequences (hI : PlaneEscapes Mc ZS I)
    (ho : letI := hsource.prepared.elementary;
      SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized))
    (w : V) (hw : (w : G) ∈ ZS) (hwZ : (w : G) ∉ centralInvolutions T)
    (hpoint : intersectionImage hsource I = pointStabilizer hsource w)
    (e : intersectionImage hsource I ≃* Equiv.Perm (Fin 3)) :
    ∃ Z1 : Subgroup G, Z1 ≤ ZS ∧ Disjoint (centralInvolutions T) Z1 ∧
      centralInvolutions T ⊔ Z1 = ZS ∧
      M ⊓ I = M ⊓ centralizer (Z1 : Set G) ∧ (M ⊓ I).relIndex M = 6 ∧
      ∃ f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3), Function.Surjective f ∧
        f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I) ∧
        PushingUpSetup KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) := by
  obtain ⟨hle,hdisj,hsup⟩ := plane_complement_of_point d hI w hw hwZ
  obtain ⟨f,hf,hker⟩ := exists_symmetricThree_action_of_image_equiv e
  exact ⟨zpowers (w : G),hle,hdisj,hsup,
    intersection_eq_centralizer_of_image d hI w hpoint,
    intersection_index_six_of_image_equiv d hI ho e,
    f,hf,hker,d.intersection_pushingUpSetup_of_symmetricThree hI f hf hker⟩

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.OmegaAction
