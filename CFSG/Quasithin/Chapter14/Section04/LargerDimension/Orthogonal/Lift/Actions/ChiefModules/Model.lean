module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.Actions.MovedInterval
public import Theory.Representation.BinaryPermutation.GroupIrreducible

/-!
# The selected moved module in the orthogonal lift

The input below records only the source's identification of the literal moved
image in U/Z(U). Its actor is K U, its kernel is exactly U, and its action is
ambient conjugation. Restriction to K still covers A₅. The binary-core theorem
therefore proves the invariant interval and constructs the elementary lift.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
variable {G : Type*} [Group G]

/-- The literal image of the cyclic commutator in the central quotient. -/
abbrev movedImage (U : Subgroup G) (i : G) : Subgroup (U ⧸ center U) :=
  ((⁅U,zpowers i⁆).subgroupOf U).map (QuotientGroup.mk' (center U))

/-- Selection data for the actual A₅ action. No irreducibility or lifted-module
conclusion is included. The map `π` presents the literal quotient K U/U. -/
structure MovedCoreModel (U K : Subgroup G) (i : G)
    (hKU : K ≤ normalizer (U : Set G)) where
  π : ↥(K ⊔ U) →* alternatingGroup (Fin 5)
  surjective : Function.Surjective π
  kernel : π.ker = U.subgroupOf (K ⊔ U)
  action : ↥(K ⊔ U) →* MulAut (U ⧸ center U)
  formula : ∀ (p : ↥(K ⊔ U)) (u : U), action p (QuotientGroup.mk' (center U) u) =
    QuotientGroup.mk' (center U) ⟨(p : G) * (u : G) * (p : G)⁻¹,
      (mem_normalizer_iff.mp ((sup_le hKU U.le_normalizer) p.property) u).mp u.property⟩
  invariant : ∀ (p : ↥(K ⊔ U)) v, v ∈ movedImage U i → action p v ∈ movedImage U i
  equiv : movedImage U i ≃* Multiplicative (BinaryPermutation.core (Fin 5))
  equivariant : ∀ (p : ↥(K ⊔ U)) (v : movedImage U i),
    equiv ⟨action p v, invariant p v v.property⟩ = Multiplicative.ofAdd
      (BinaryPermutation.coreRepresentation (Fin 5) (π p).val (equiv v).toAdd)

namespace MovedCoreModel
variable {U K : Subgroup G} {i : G} {hKU : K ≤ normalizer (U : Set G)}
variable (m : MovedCoreModel U K i hKU)

/-- The selected presentation is an isomorphism of the literal quotient. -/
noncomputable def actorEquiv :
    letI := normal_subgroupOf_of_le_normalizer (sup_le hKU U.le_normalizer)
    (↥(K ⊔ U) ⧸ U.subgroupOf (K ⊔ U)) ≃* alternatingGroup (Fin 5) := by
  letI := normal_subgroupOf_of_le_normalizer (sup_le hKU U.le_normalizer)
  exact (QuotientGroup.quotientMulEquivOfEq m.kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective m.π m.surjective)


/-- The actor isomorphism agrees with the selected quotient presentation. -/
@[simp] theorem actorEquiv_mk (p : ↥(K ⊔ U)) :
    let _ := normal_subgroupOf_of_le_normalizer (sup_le hKU U.le_normalizer)
    m.actorEquiv (QuotientGroup.mk' (U.subgroupOf (K ⊔ U)) p) = m.π p := by
  rfl

/-- Restricting the actor to K still gives the whole alternating group. -/
theorem restriction_surjective :
    Function.Surjective (m.π.comp (inclusion (le_sup_left : K ≤ K ⊔ U))) := by
  intro a
  obtain ⟨p,hp⟩ := m.surjective a
  have hp' : (p : G) ∈ (U : Set G) * (K : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left U K hKU, sup_comm]
    exact p.property
  obtain ⟨u,hu,k,hk,huk⟩ := hp'
  have hπu : m.π ⟨u,(le_sup_right : U ≤ K ⊔ U) hu⟩ = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [m.kernel]
    exact hu
  refine ⟨⟨k,hk⟩, ?_⟩
  have he : p = (⟨u,(le_sup_right : U ≤ K ⊔ U) hu⟩ : ↥(K ⊔ U)) * ⟨k,(le_sup_left : K ≤ K ⊔ U) hk⟩ :=
    Subtype.ext huk.symm
  rw [he, map_mul, hπu, one_mul] at hp
  exact hp

/-- Irreducibility is derived from the binary core, for the subgroup K that
centralizes the selected involution. -/
theorem irreducible (F : Subgroup (U ⧸ center U)) (hF : F ≤ movedImage U i)
    (hinv : ∀ k : K, ∀ v ∈ F,
      m.action (inclusion (le_sup_left : K ≤ K ⊔ U) k) v ∈ F) :
    F = ⊥ ∨ F = movedImage U i := by
  exact BinaryPermutation.invariant_subgroup_of_fiveCore (movedImage U i)
    (m.action.comp (inclusion le_sup_left))
    (fun k => m.invariant (inclusion le_sup_left k))
    (m.π.comp (inclusion le_sup_left)) m.restriction_surjective m.equiv
    (fun k => m.equivariant (inclusion le_sup_left k)) F hF hinv

variable [Finite G] [IsExtraspecial 2 U]
include m

/-- The actual binary action discharges the interval premise upstairs. -/
theorem invariant_interval (z : G)
    (hZ : (center U).map U.subtype = zpowers z)
    (hiU : i ∈ normalizer (U : Set G))
    (hmoved : Nat.card (movedImage U i) = 16) :
    ∀ E : Subgroup G, zpowers z ≤ E → E ≤ liftBase U z i →
      K ≤ normalizer (E : Set G) → E = zpowers z ∨ E = liftBase U z i := by
  apply liftBase_invariant_interval_of_moved_image U K z i hZ hiU hKU hmoved
    (m.action.comp (inclusion le_sup_left))
    (fun k u => m.formula (inclusion le_sup_left k) u)
  exact m.irreducible

/-- Construction of A and D requires no separate irreducibility input. -/
theorem elementary_lift (z : G) (hz : orderOf z = 2) (hi : orderOf i = 2)
    (hZ : (center U).map U.subtype = zpowers z)
    (hiU : i ∈ normalizer (U : Set G)) (hiz : i ∈ centralizer ({z} : Set G))
    (hout : i ∉ U) (hKi : K ≤ centralizer ({i} : Set G))
    (hmoved : Nat.card (movedImage U i) = 16) :
    IsElementaryAbelian 2 (centralizerLift U z i) ∧
      Nat.card (centralizerLift U z i) = 64 ∧
      IsElementaryAbelian 2 (liftBase U z i) ∧ Nat.card (liftBase U z i) = 32 := by
  exact centralizerLift_elementary_and_card_of_moved_image U K z i hz hi hZ hiU hiz
    hout hKU hKi hmoved (m.action.comp (inclusion le_sup_left))
    (fun k u => m.formula (inclusion le_sup_left k) u) m.irreducible
end MovedCoreModel
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
