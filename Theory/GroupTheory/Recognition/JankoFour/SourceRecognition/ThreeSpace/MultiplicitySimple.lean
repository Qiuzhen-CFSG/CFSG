module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.Multiplicity
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.FaithfulRadical
public import Theory.GroupAction.FiveOnSixteenIrreducible
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderFiveQuadraticAction

/-!
# The faithful irreducible four-space in the source tensor argument

The three-copy coordinates imply that the S/R action on the original pair
section has the same kernel as its action on R/Z. Hence it is faithful.
Its marked alternating-five subgroup contains an order-five automorphism;
on sixteen elements such an automorphism has no nonidentity fixed point,
and orbit counting forces every invariant subgroup to be trivial or full.
Thus the four-space is irreducible for both original actors.

The S₅ marking is exactly `SQuotientEquiv`, and its representative formula
uses the original conjugation action. These conclusions do not identify the
four-space with the natural L₂(4) module: that identification must still
preserve the native action, since dimension and irreducibility alone do not
distinguish it from the deleted permutation module.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*,
Invent. Math. 105 (1991), (4.4), pp.597–598, DOI 10.1007/BF01232280.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition

private theorem invariant_simple_of_five_divides {A V : Type*} [Group A] [Finite A]
    [Group V] [Finite V] (hV : Nat.card V = 16) (ρ : A →* MulAut V)
    (hρ : Function.Injective ρ) (hA : 5 ∣ Nat.card A) (U : Subgroup V)
    (hU : ∀ a v, v ∈ U → ρ a v ∈ U) : U = ⊥ ∨ U = ⊤ := by
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := A) 5 (hp := ⟨by decide⟩) hA
  let B := zpowers (ρ a)
  have hB : Nat.card B = 5 := by
    rw [Nat.card_zpowers,orderOf_injective ρ hρ,ha]
  have hBR : B ≤ ρ.range := zpowers_le.mpr ⟨a,rfl⟩
  have hforward (b : B) (v : V) (hv : v ∈ U) : b • v ∈ U := by
    obtain ⟨c,hc⟩ := hBR b.property
    change b.val v ∈ U
    rw [←hc]
    exact hU c v hv
  let : IsInvariant B V U := ⟨fun b v => ⟨hforward b v,fun hv => by
    simpa only [inv_smul_smul] using hforward b⁻¹ (b • v) hv⟩⟩
  exact invariant_eq_bot_or_top_of_five_actor hB hV
    (SmallNonabelianTwoGroup.order_five_actor_fixed_subgroup_eq_bot hV B hB) U

namespace ThreeSpaceData
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : CubicAutomorphismQuotient (centralizer z ⧸ core z)}
  {X : Sylow 3 (LocalGeometry.CubicLift.subgroup e)}
variable (d : ThreeSpaceData z e X)
attribute [local instance] R_normal_in_K R_normal_in_S_intrinsic R_normal_in_normalizer

theorem multiplicitySpace_elementary (h : IsTypeJ4 z) :
    IsElementaryAbelian 2 d.multiplicitySpace := by
  let := d.R_center_quotient_elementary h
  exact IsElementaryAbelian.of_injective d.multiplicitySpace.subtype
    d.multiplicitySpace.subtype_injective

theorem multiplicitySpace_rank (h : IsTypeJ4 z) : primeRank 2 d.multiplicitySpace = 4 := by
  let := d.multiplicitySpace_elementary h
  rw [←IsElementaryAbelian.log_card_eq_primeRank (p := 2),d.multiplicitySpace_card h]
  norm_num

/-- The same original four-space carries a faithful S/R action. -/
theorem multiplicityAction_injective (h : IsTypeJ4 z) :
    Function.Injective (d.multiplicityAction h) := by
  obtain ⟨f,_,hf⟩ := d.exists_multiplicity_coordinates h
  intro a b hab
  apply d.SRadicalAction_injective h
  apply MulEquiv.ext
  intro x
  obtain ⟨⟨u,v,w⟩,rfl⟩ := f.surjective x
  rw [←hf a u v w,←hf b u v w,hab]

/-- The four-space action with exactly the previously constructed S/R ≃ S₅ marking. -/
noncomputable def markedMultiplicityAction (h : IsTypeJ4 z) :
    Equiv.Perm (Fin 5) →* MulAut d.multiplicitySpace :=
  (d.multiplicityAction h).comp (d.SQuotientEquiv h).symm.toMonoidHom

@[simp] theorem markedMultiplicityAction_quotient (h : IsTypeJ4 z)
    (a : d.S ⧸ d.R.subgroupOf d.S) :
    d.markedMultiplicityAction h (d.SQuotientEquiv h a) = d.multiplicityAction h a := by
  exact congrArg (d.multiplicityAction h) ((d.SQuotientEquiv h).symm_apply_apply a)

theorem markedMultiplicityAction_injective (h : IsTypeJ4 z) :
    Function.Injective (d.markedMultiplicityAction h) :=
  (d.multiplicityAction_injective h).comp (d.SQuotientEquiv h).symm.injective

/-- The original marking sends each representative to its literal radical conjugation. -/
theorem markedMultiplicityAction_mk (h : IsTypeJ4 z) (s : d.S) (w : d.multiplicitySpace) :
    (d.markedMultiplicityAction h (d.SQuotientEquiv h (QuotientGroup.mk' _ s)) w :
        d.R ⧸ center d.R) =
      d.radicalAction (inclusion (Subgroup.centralizer_le_normalizer _) s) w := by
  rw [d.markedMultiplicityAction_quotient,d.multiplicityAction_apply,d.SRadicalAction_mk]

/-- The alternating subgroup acts irreducibly on this actual four-space. -/
theorem multiplicity_alternating_irreducible (h : IsTypeJ4 z)
    (U : Subgroup d.multiplicitySpace)
    (hU : ∀ a : alternatingGroup (Fin 5), ∀ w : d.multiplicitySpace,
      w ∈ U → d.markedMultiplicityAction h a w ∈ U) : U = ⊥ ∨ U = ⊤ := by
  apply invariant_simple_of_five_divides (d.multiplicitySpace_card h)
    ((d.markedMultiplicityAction h).comp (alternatingGroup (Fin 5)).subtype)
    ((d.markedMultiplicityAction_injective h).comp (alternatingGroup (Fin 5)).subtype_injective)
    (by rw [nat_card_alternatingGroup,Nat.card_fin]; decide) U hU

/-- The original S/R action is irreducible as well. -/
theorem multiplicity_irreducible (h : IsTypeJ4 z) (U : Subgroup d.multiplicitySpace)
    (hU : ∀ a : d.S ⧸ d.R.subgroupOf d.S, ∀ w : d.multiplicitySpace,
      w ∈ U → d.multiplicityAction h a w ∈ U) : U = ⊥ ∨ U = ⊤ := by
  apply d.multiplicity_alternating_irreducible h U
  intro a w hw
  exact hU ((d.SQuotientEquiv h).symm a) w hw

end ThreeSpaceData
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
end
