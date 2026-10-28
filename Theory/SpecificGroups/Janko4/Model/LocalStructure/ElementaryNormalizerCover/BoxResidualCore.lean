module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.BoxResidualGeometry

/-!
# Canonical two-core enlargement at the original seed

The central omega of the two-core of C(X), and its intrinsic form radical,
are preserved by the entire N(X). The kernel fixed by X lies in this two-core:
it is an elementary normal subgroup of C(X), whose seed places C(X) in max1.
An odd invariant finite set has a fixed element under any two-group. The box
pair-orbit applications use this to construct actual central involutions.
Source motivation: Kleidman--Wilson (1988), Proposition 2.3.2, p.492.
-/

set_option backward.isDefEq.respectTransparency true
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover.BoxResidual
open InvolutionCentralizers.Second LargeCenterRadicals.OuterHalf
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup Cardinality.localKernel

def coreOmega (X : Subgroup Model) : Subgroup Model :=
  omegaCenterIn ((centralizer (X : Set Model)).pCoreIn 2)
instance coreOmega_elementary (X : Subgroup Model) : IsElementaryAbelian 2 (coreOmega X) :=
  inferInstanceAs (IsElementaryAbelian 2 (omegaCenterIn ((centralizer (X : Set Model)).pCoreIn 2)))
def coreZeroWitness (X : Subgroup Model) : Subgroup Model := formRadical (coreOmega X)
instance coreZeroWitness_elementary (X : Subgroup Model) : IsElementaryAbelian 2 (coreZeroWitness X) :=
  inferInstanceAs (IsElementaryAbelian 2 (formRadical (coreOmega X)))

theorem coreOmega_normalizer (X : Subgroup Model) :
    normalizer (X : Set Model) ≤ normalizer (coreOmega X : Set Model) :=
  ((normalizer_le_normalizer_centralizer X).trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 (centralizer (X : Set Model))))).trans
      (normalizer_le_normalizer_omegaCenterIn _)

theorem coreZeroWitness_form (X : Subgroup Model) : intrinsicElementaryForm (coreZeroWitness X) = 0 :=
  formRadical_form_zero _

theorem coreZeroWitness_normalizer (X : Subgroup Model) :
    normalizer (X : Set Model) ≤ normalizer (coreZeroWitness X : Set Model) :=
  (coreOmega_normalizer X).trans (normalizer_le_formRadical_normalizer _)

theorem kernel_centralizer_le_core (X : Subgroup Model) (hs : (seed : Model) ∈ X) :
    embeddedKernel ⊓ centralizer (X : Set Model) ≤ (centralizer (X : Set Model)).pCoreIn 2 := by
  have hCM : centralizer (X : Set Model) ≤ Local :=
    (centralizer_le (Set.singleton_subset_iff.mpr hs)).trans ambient_le_max1
  apply le_pCoreIn_of_normalizes
    (embedded_localKernel_isPRadical.isPGroup.to_le inf_le_left) inf_le_right
  apply (le_inf ?_ (centralizer (X : Set Model)).le_normalizer).trans inf_normalizer_le_normalizer_inf
  rwa [embedded_localKernel_normalizer_eq_max1]

theorem exists_fixed_of_odd_conjugation {G : Type*} [Group G]
    (P : Subgroup G) (hP : IsPGroup 2 P) (S : Finset G)
    (hodd : ¬2 ∣ S.card)
    (hinv : ∀ g ∈ P, ∀ x ∈ S, g*x*g⁻¹ ∈ S) :
    ∃ x ∈ S, ∀ g ∈ P, g*x = x*g := by
  let : MulAction P S :=
    { smul g x := ⟨(g : G)*x.val*(g : G)⁻¹,hinv g g.property x x.property⟩
      one_smul x := by
        apply Subtype.ext
        change (1 : G) * x.val * (1 : G)⁻¹ = x.val
        simp
      mul_smul g h x := by
        apply Subtype.ext
        change ((g : G) * h) * x.val * ((g : G) * h)⁻¹ =
          (g : G) * ((h : G) * x.val * (h : G)⁻¹) * (g : G)⁻¹
        simp [mul_assoc] }
  have hcard : ¬2 ∣ Nat.card S := by simpa using hodd
  obtain ⟨x,hx⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card S hcard
  refine ⟨x,x.property,fun g hg => ?_⟩
  have he := congrArg Subtype.val (hx (⟨g,hg⟩ : P))
  exact mul_inv_eq_iff_eq_mul.mp he


theorem elementary_le_coreOmega (X : Subgroup Model) [IsElementaryAbelian 2 X] : X ≤ coreOmega X := by
  have hXQ : X ≤ (centralizer (X : Set Model)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 X) X.le_centralizer
      (centralizer_le_normalizer (X : Set Model))
  intro x hx
  exact (mem_omegaCenterIn_iff _ _).mpr
    ⟨hXQ hx,fun g hg => ((pCoreIn_le 2 (centralizer (X : Set Model)) hg) x hx).symm,
      elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx⟩

open Cardinality KernelCount QuotientCount.Image LinearFive M22Images.KernelAction
open Simplicity.Max1Fusion Simplicity.Max1Fusion.KernelOrbits

theorem kernelValue_mem_core_of_fixed_image (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X) (m : ℕ)
    (hm : ∀ p ∈ (X.subgroupOf Local).map starHom, SylowCore.starMask p m = m) :
    (kernelValue m : Model) ∈ (centralizer (X : Set Model)).pCoreIn 2 := by
  have hCM : centralizer (X : Set Model) ≤ Local :=
    (centralizer_le (Set.singleton_subset_iff.mpr hs)).trans ambient_le_max1
  have hXM := X.le_centralizer.trans hCM
  apply kernel_centralizer_le_core X hs
  refine ⟨⟨kernelValue m,(maskValue _ _ m).property,rfl⟩,?_⟩
  intro x hx
  let x0 : Local := ⟨x,hXM hx⟩
  have he := kernel_conjugation x0 m
  change x0 * kernelValue m * x0⁻¹ = kernelValue (SylowCore.starMask (starHom x0) m) at he
  rw [hm _ (mem_map_of_mem starHom (show x0 ∈ X.subgroupOf Local from hx))] at he
  exact congrArg (fun y : Local => (y : Model)) (mul_inv_eq_iff_eq_mul.mp he)

end Janko4.LocalStructure.ElementaryNormalizerCover.BoxResidual
