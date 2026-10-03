module
public import Stellmacher.SectionOne.OneSevenIdentification
public import Stellmacher.SectionOne.OneSevenModuleProduct

/-!
# The quadratic action of the canonical one-seven subgroup

For a faithful elementary two-group action satisfying the Section One
hypotheses, the canonical subgroup J(V,S) fixes its action commutator.
No assumption on the E-fixed space, or on nontriviality of J, is required.
Together with the opposite fixed-space covering theorem this identifies
the fixed and commutator spaces when the E-fixed space is trivial, as
needed for the fixed-closure argument in Stellmacher (8.4).

The global identification expresses J as the join of its order-two Sylow
coordinates in the natural SL₂(2) factors. Action commutators distribute
over this join. Each coordinate fixes its own commutator by the elementary
involution calculation; every other coordinate fixes it because distinct
one-seven factors fix each other's supports. Thus J fixes each generating
commutator subgroup. The argument also handles the empty factor family.

Source: the factor decomposition in Stellmacher (1.7), journal p19, used
in (8.4), journal p39; refs/latex/stellmacher-n-group.tex.
-/

open scoped IsMulCommutative
open Stellmacher.SectionOne.RankOneThreeGroupAssembly
namespace Stellmacher.SectionOne
universe u

/-- The action of the canonical J on its elementary two-group is quadratic. -/
public theorem oneSeven_commutator_le_fixed
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G) :
    commutatorAction (oneJ (V := V) (S : Subgroup G)) V ≤
      FixedPoints.subgroup (oneJ (V := V) (S : Subgroup G)) V := by
  classical
  let E := oneSevenGenerated (G := G) (V := V)
  let F := oneSevenFactors (G := G) (V := V)
  let I := {D : Subgroup G // D ∈ F}
  let Q (i : I) : Subgroup G := (S : Subgroup G) ⊓ i.val
  let J := oneJ (V := V) (S : Subgroup G)
  obtain ⟨hEnormal, hprod, _⟩ := oneSeven_global_product h S
  obtain ⟨hJid, _⟩ := oneSeven_global_identification h S
  change J = (S : Subgroup G) ⊓ E at hJid
  change IsInternalDirectProduct E F at hprod
  have hF (i : I) : IsOneSevenFactor (V := V) i.val :=
    (mem_oneSevenFactors_iff i.val).mp i.property
  obtain ⟨_, hQgen, _, hQcard⟩ := sl2_product_sylow_coordinates S E hEnormal F hprod
    (fun D hD => ((mem_oneSevenFactors_iff D).mp hD).1)
  have hJgen : J = ⨆ i : I, Q i := hJid.trans hQgen
  rw [commutatorAction_eq_iSup_of_eq_iSup Q hJgen]
  refine iSup_le fun i => ?_
  have hown : commutatorAction (Q i) V ≤ FixedPoints.subgroup (Q i) V := by
    have hVcard : 4 ≤ Nat.card V := by
      rw [← (hF i).2.2.1]
      exact Nat.card_le_card_of_injective _ (commutatorAction i.val V).subtype_injective
    let _ : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    have hc : Nat.card (Q i) = 2 := hQcard i.val i.property
    obtain ⟨x, hxne, huniq⟩ := (Nat.card_eq_two_iff' (1 : Q i)).mp hc
    have hxinv : x⁻¹ = x := (huniq x⁻¹ (by simpa using hxne)).trans (huniq x hxne).symm
    have hxx : x ^ 2 = 1 := by
      calc
        x ^ 2 = x * x := pow_two x
        _ = x⁻¹ * x := by rw [hxinv]
        _ = 1 := inv_mul_cancel x
    exact (card_two_action_fixed_commutator_card_data (U := V) x ⟨hxne, hxx⟩ hc).2
  have hsupport : commutatorAction (Q i) V ≤ commutatorAction i.val V := by
    rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
    refine Subgroup.closure_mono ?_
    rintro z ⟨q, v, rfl⟩
    exact ⟨⟨q, q.property.2⟩, v, rfl⟩
  intro v hv
  have hfix : J ≤ fixingSubgroup G ({v} : Set V) := by
    rw [hJgen]
    refine iSup_le fun j => ?_
    intro q hq
    rw [mem_fixingSubgroup_iff]
    intro w hw
    obtain rfl := Set.mem_singleton_iff.mp hw
    by_cases hji : j = i
    · subst j
      exact hown hv ⟨q, hq⟩
    · have hh := oneSevenFactor_commutatorAction_le_fixedPoints h j.val i.val
        (hF j) (hF i) (fun he => hji (Subtype.ext he)) (hsupport hv)
      exact hh ⟨q, hq.2⟩
  intro j
  exact (mem_fixingSubgroup_iff (M := G)).mp (hfix j.property) v (Set.mem_singleton v)

end Stellmacher.SectionOne
