module
public import Theory.GroupTheory.SimpleQuotientActionImage
public import Glauberman.PushingUpOmegaAction
public import Theory.Representation.BinaryOffender.QuadraticImageBound
/-!
# Structure of the original pushing-up omega action

The two-core Q=O₂(H) centralizes V=Ω₁(Z(Q)), whereas the source offender
makes the original action on V nontrivial. The unique-maximal kernel
reduction then places its kernel inside the given K and makes its faithful
image perfect. We retain the literal map from that image to H/K, identify
its kernel with the image of K, and prove that kernel odd, nilpotent and
contained in the image's Frattini subgroup.

These are structural inputs to Niles's Lemmas 2.8–2.9, “Pushing-up in finite
groups”, printed pp. 32–33, for the original PSL₂(4) quotient. No perfection
of H, recognition of the action quotient, or degree bound is assumed.
-/

set_option backward.isDefEq.respectTransparency false
public section
noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace Glauberman
variable {H : Type*} [Group H]

/-- The original two-core centralizes its own central omega subgroup. -/
theorem twoCore_le_omegaAction_kernel : pCore 2 H ≤ (omegaAction H).ker := by
  rw [omegaAction_kernel]
  apply le_centralizer_iff.mpr
  intro v hv
  exact ((mem_omegaCenterIn_iff _ _).mp hv).2.1

variable [Finite H] {F : Type*} [Field F] [Finite F]

/-- Original source hypotheses force a nontrivial omega action. -/
theorem original_psl2_four_omegaAction_kernel_ne_top
    (hF : Nat.card F=4) (S : Sylow 2 H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H=pCore 2 H)
    (hno : NoCharacteristicNormal (S : Subgroup H)) : (omegaAction H).ker≠⊤ := by
  obtain ⟨A,hA,hAK,hquad,hfirst,hrest⟩ :=
    original_psl2_four_nontrivial_quadratic_offender hF S hu K e hf hno
  intro he
  rw [omegaAction_kernel] at he
  have hc : omegaCenterIn (pCore 2 H)≤center H := centralizer_eq_top_iff_subset.mp he
  apply hfirst
  rw [inf_eq_left.mpr (hc.trans (center_le_centralizer _)),inf_eq_left.mpr hc]

/-- The faithful image of the literal omega action maps onto the original
quotient, with an odd nilpotent kernel and its original element markings. -/
theorem original_psl2_four_omegaAction_image_structure
    (hF : Nat.card F=4) (S : Sylow 2 H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H=pCore 2 H)
    (hno : NoCharacteristicNormal (S : Subgroup H)) :
    let ρ := omegaAction H
    let I := actionImage ρ
    let a : H →* I := actionHom ρ
    pCore 2 H ≤ ρ.ker ∧ ρ.ker ≤ K ∧ Group.IsPerfect I ∧
      ∃ q : I →* (H ⧸ K), Function.Surjective q ∧
        (∀ h, q (a h)=QuotientGroup.mk' K h) ∧
        q.ker=K.map a ∧ Group.IsNilpotent q.ker ∧ Odd (Nat.card q.ker) ∧
        q.ker ≤ frattini I := by
  dsimp only
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let b := e.trans a
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (H ⧸ K) := b.isSimpleGroup
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect (H ⧸ K) := Group.IsPerfect.ofSurjective (f:=b.symm.toMonoidHom) b.symm.surjective
  obtain ⟨hSK,hFr,hNil,hOdd,hRed⟩ :=
    Theory.SpecificGroups.SL2.original_kernel_reduction_of_psl2_four hF S hu K e
  have hcore : pCore 2 H ≤ (actionHom (omegaAction H)).ker := by
    rw [actionHom_ker_eq]
    exact twoCore_le_omegaAction_kernel
  have hnt : (actionHom (omegaAction H)).ker≠⊤ := by
    rw [actionHom_ker_eq]
    exact original_psl2_four_omegaAction_kernel_ne_top hF S hu K e hf hno
  obtain ⟨hk,hp,q,hqs,hqe,hqk,hqn,hqo⟩ :=
    Theory.GroupTheory.SimpleQuotientActionImage.structure_of_supplement_reduction
      (pCore 2 H) K hRed hNil hOdd (actionHom (omegaAction H))
      (omegaAction H).asGroupHom.rangeRestrict_surjective hcore hnt
  rw [actionHom_ker_eq] at hk
  refine ⟨twoCore_le_omegaAction_kernel,hk,hp,q,hqs,hqe,hqk,hqn,hqo,?_⟩
  rw [hqk]
  exact Theory.GroupTheory.SimpleQuotientActionImage.map_le_frattini_of_quotient_image_le
    (pCore 2 H) K hFr (actionHom (omegaAction H))
    (omegaAction H).asGroupHom.rangeRestrict_surjective hcore
end Glauberman
