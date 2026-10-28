module

public import Theory.Representation.BinaryConjugationSection.ConjugationCoordinates
public import Theory.Representation.BinaryConjugationSection.ActionKernel
public import Theory.Representation.BinaryConjugationSection.OffenderQuotientIndex
public import Theory.Representation.BinaryOffender.ActionImage

/-!
# A faithful offender on the literal partner section

The original elementary actor is compared with the actual kernel of its
action on F/U. The coordinate action is constructed from conjugation, and
the faithful image has exactly the prescribed commutator-preimage kernel.
Thus a centralizer-index bound gives an offender without transporting a
Thompson subgroup through a quotient or assuming that an offender survives.

The prime-five source consumer uses the original module as actor, after
the two original supports bound its section image and its fixed index.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.DecomposableQuinticControl
variable {G : Type*} [Group G] [Finite G]

/-- A comparison with the actual section kernel constructs a faithful
section action and an offender given by the image of the original actor. -/
theorem exists_faithful_section_offender_of_kernel_index
    (H F U A : Subgroup G) [IsElementaryAbelian 2 F] [IsElementaryAbelian 2 A]
    (hFH : F ≤ H) (hUF : U ≤ F)
    (hnF : H ≤ normalizer (F : Set G)) (hnU : H ≤ normalizer (U : Set G))
    (hAH : A ≤ H)
    (hne : 1 < (commutatorPreimage H F U).relIndex A)
    (hi : (centralizer (A : Set G)).relIndex F ≤
      (commutatorPreimage H F U).relIndex A) :
    ∃ ρ : Representation (ZMod 2) H (Additive (F ⧸ U.subgroupOf F)),
      Nonempty (BinaryConjugationSection H F U ρ) ∧
      Function.Injective (imageRepresentation ρ) ∧
      (actionHom ρ).ker.map H.subtype = commutatorPreimage H F U ∧
      Nat.card (actionSubgroup ρ (A.subgroupOf H)) =
        (commutatorPreimage H F U).relIndex A ∧
      IsOffender (imageRepresentation ρ) (actionSubgroup ρ (A.subgroupOf H)) := by
  obtain ⟨ρ, ⟨d⟩⟩ := BinaryConjugationSection.exists_conjugation_coordinates
    H F U hFH hnF hUF hnU
  have hk : (actionHom ρ).ker = ρ.ker := by
    ext a
    change actionHom ρ a = 1 ↔ ρ a = 1
    rw [actionHom_eq_one_iff]
    constructor
    · exact fun he => LinearMap.ext he
    · exact fun he v => congrArg (fun f : Module.End (ZMod 2)
        (Additive (F ⧸ U.subgroupOf F)) => f v) he
  have hkm : (actionHom ρ).ker.map H.subtype = commutatorPreimage H F U := by
    rw [hk]
    exact d.action_kernel_map hnU
  have hc : Nat.card (actionSubgroup ρ (A.subgroupOf H)) =
      (commutatorPreimage H F U).relIndex A := by
    change Nat.card ((A.subgroupOf H).map (actionHom ρ)) = _
    rw [←relIndex_ker]
    have he := relIndex_map_map_of_injective (actionHom ρ).ker
      (A.subgroupOf H) H.subtype_injective
    rw [hkm, map_subgroupOf_eq_of_le hAH] at he
    exact he.symm
  let : IsElementaryAbelian 2 (A.subgroupOf H) :=
    IsElementaryAbelian.subgroupOf hAH
  have he : IsElementaryTwo (actionSubgroup ρ (A.subgroupOf H)) := by
    refine ⟨?_, IsElementaryAbelian.map (actionHom ρ)⟩
    intro hz
    rw [hz] at hc
    simp only [Subgroup.card_bot] at hc
    omega
  refine ⟨ρ, ⟨d⟩, imageRepresentation_injective ρ, hkm, hc, ?_⟩
  apply BinaryConjugationSection.offender_of_section_index
    (imageRepresentation ρ) (actionHom ρ) d A (centralizer (A : Set G))
  · rw [commutator_comm, commutator_eq_bot_iff_le_centralizer.mpr le_rfl]
    exact bot_le
  · exact he
  · change (centralizer (A : Set G)).relIndex F ≤
      Nat.card (actionSubgroup ρ (A.subgroupOf H))
    rwa [hc]

end CFSG.Quasithin.Chapter15.DecomposableQuinticControl
