module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models.Actions
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure.QuotientAction

/-!
# The actual Omega-image pair from the two layer actions

The tensor action is faithful, so its actor kernel is the relative
centralizer of V. The original natural orthogonal action has the same
kernel. The first isomorphism theorem therefore identifies their actual
images, with a pointwise equation on every element of I. Cubic displacement
shows that each ordered factor moves all of V; the upper layer coordinates
then give the literal natural quotient pair used in 15.3.60.

Source: Aschbacher–Smith, 15.3.53–54, 15.3.58(2), and the setup of 15.3.60,
printed pp.1146, 1148, and 1150.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry.LayerAdapters
open Subgroup Core.Automizers Core.Automizers.Models
open Cubic.MLocal.Structure
open scoped commutatorElement
variable {G : Type*} [Group G] {M I Y P V : Subgroup G}
variable {hIP : I ≤ normalizer (P : Set G)} {hIV : I ≤ normalizer (V : Set G)}
variable [(V.subgroupOf P).Normal]

theorem layer_actor_ker (r : LayerActions I Y P V hIP hIV) :
    r.actor.ker = (centralizer (V : Set G)).subgroupOf I := by
  have h := congrArg MonoidHom.ker r.lower_hom_transport
  rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.congr r.lowerCoordinates).injective,
    MonoidHom.ker_comp_of_injective _ _ tensorAction_injective] at h
  exact h.symm.trans (lowerAction_ker I V hIV)

theorem imageActor_onto (a : NaturalOrthogonalAction M V) (hIM : I ≤ M) :
    Function.Surjective (imageActor a I hIM) := by
  rintro ⟨x, m, hm, rfl⟩
  exact ⟨⟨m, hm⟩, rfl⟩

theorem imageActor_ker (a : NaturalOrthogonalAction M V) (hIM : I ≤ M) :
    (imageActor a I hIM).ker = (centralizer (V : Set G)).subgroupOf I := by
  ext i
  change (⟨a.actor ⟨i, hIM i.property⟩, _⟩ : a.image I) = 1 ↔ _
  rw [Subtype.ext_iff]
  change ⟨i, hIM i.property⟩ ∈ a.actor.ker ↔ _
  rw [a.ker_actor]
  rfl

def layerImageEquiv (r : LayerActions I Y P V hIP hIV)
    (a : NaturalOrthogonalAction M V) (hIM : I ≤ M) : a.image I ≃* Actor :=
  (QuotientGroup.quotientKerEquivOfSurjective (imageActor a I hIM)
    (imageActor_onto a hIM)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq
        ((imageActor_ker a hIM).trans (layer_actor_ker r).symm)).trans
          (QuotientGroup.quotientKerEquivOfSurjective r.actor r.onto))

theorem layerImageEquiv_apply (r : LayerActions I Y P V hIP hIV)
    (a : NaturalOrthogonalAction M V) (hIM : I ≤ M) (i : I) :
    layerImageEquiv r a hIM (imageActor a I hIM i) = r.actor i := by
  unfold layerImageEquiv
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply]
  have he := (QuotientGroup.quotientKerEquivOfSurjective (imageActor a I hIM)
    (imageActor_onto a hIM)).symm_apply_apply
      (QuotientGroup.mk' (imageActor a I hIM).ker i)
  change (QuotientGroup.quotientKerEquivOfSurjective r.actor r.onto)
    ((QuotientGroup.quotientMulEquivOfEq _)
      ((QuotientGroup.quotientKerEquivOfSurjective (imageActor a I hIM)
        (imageActor_onto a hIM)).symm
          ((QuotientGroup.quotientKerEquivOfSurjective (imageActor a I hIM)
            (imageActor_onto a hIM))
              (QuotientGroup.mk' (imageActor a I hIM).ker i)))) = _
  rw [he]
  rfl

theorem tensor_second_displacement : ∀ x : TensorVector,
    ∃ w : TensorVector, tensorAction (1, rotation) w * w⁻¹ = x := by
  decide +kernel

private theorem tensor_factor_moves (r : LayerActions I Y P V hIP hIV)
    (K : Subgroup G) (hKI : K ≤ I) (b : Actor)
    (hb : ∃ i : I, (i : G) ∈ K ∧ r.actor i = b)
    (hmove : ∀ x : TensorVector, ∃ w, tensorAction b w * w⁻¹ = x) : ⁅V, K⁆ = V := by
  apply le_antisymm (le_normalizer_iff_commutator_le_left.mp (hKI.trans hIV))
  intro v hv
  obtain ⟨i, hi, he⟩ := hb
  obtain ⟨w, hw⟩ := hmove (r.lowerCoordinates ⟨v, hv⟩)
  let u := r.lowerCoordinates.symm w
  have heq : ((lowerAction I V hIV i u) * u⁻¹ : V) = ⟨v, hv⟩ := by
    apply r.lowerCoordinates.injective
    rw [map_mul, map_inv, r.lower_compatible, he, r.lowerCoordinates.apply_symm_apply]
    exact hw
  have hmem : ⁅(i : G), (u : G)⁆ ∈ ⁅K, V⁆ := commutator_mem_commutator hi u.property
  rw [commutator_comm K V] at hmem
  have hg := congrArg V.subtype heq
  change ⁅(i : G), (u : G)⁆ = v at hg
  rwa [← hg]

def naturalPairOfLayers (r : LayerActions I Y P V hIP hIV)
    (a : NaturalOrthogonalAction M V) (hIM : I ≤ M) :
    NaturalQuotientPair a I P hIM hIP where
  factors := layerImageEquiv r a hIM
  first_moves := by
    apply tensor_factor_moves r _ (map_subtype_le _) (rotation, 1) _ tensor_displacement
    obtain ⟨i, hi⟩ := r.onto (rotation, 1)
    refine ⟨i, ⟨i, ?_, rfl⟩, hi⟩
    change (layerImageEquiv r a hIM (imageActor a I hIM i)).2 = 1
    rw [layerImageEquiv_apply, hi]
  second_moves := by
    apply tensor_factor_moves r _ (map_subtype_le _) (1, rotation) _ tensor_second_displacement
    obtain ⟨i, hi⟩ := r.onto (1, rotation)
    refine ⟨i, ⟨i, ?_, rfl⟩, hi⟩
    change (layerImageEquiv r a hIM (imageActor a I hIM i)).1 = 1
    rw [layerImageEquiv_apply, hi]
  coordinates := r.upperCoordinates
  compatible := by
    intro i p
    rw [layerImageEquiv_apply]
    have h := r.upper_compatible i (QuotientGroup.mk' (V.subgroupOf P) p)
    rw [upperAction_mk] at h
    exact h

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry.LayerAdapters
