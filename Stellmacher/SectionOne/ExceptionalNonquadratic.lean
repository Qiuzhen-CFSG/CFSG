module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.ExceptionalFactor
public import Theory.Representation.NormalizedCThreeCardSixteen

/-!
# Failure of genericity gives a nonquadratic action on V*

For an elementary abelian Sylow-type subgroup S, failure of the exact local
generic predicate produces a normalized C3 subgroup F and an order-four
coordinate I≤S. The previously proved finite-action calculation shows that
I acts nonquadratically on U=[V,F]. Since F lies in the odd core, U≤V*.
Mapping the two successive generator closures into [V*,S,S] transports
nonvanishing to the ambient subgroup used in the source conclusion.

This proves the nonquadratic field of Stellmacher (1.6)(b), journal p.18,
without a minimal-m hypothesis or the bounded exceptional classification.
Source: `refs/latex/stellmacher-n-group.tex`.
-/

open scoped IsMulCommutative
namespace Stellmacher.SectionOne
open RankOneThreeGroupAssembly
universe u

public theorem vStarAction₂_ne_bot_of_nongeneric
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S : Subgroup G) (hS : IsElementaryAbelian 2 S)
    (hnongeneric : ¬ RankOneAssemblyGenericHypothesis (G := G) (V := V) S) :
    vStarAction₂ (G := G) (V := V) S ≠ ⊥ := by
  obtain ⟨A, F, hAmax, hAcard, hFWA, hFcard, hcoord, _hnot, hfixed, hUcard⟩ :=
    exists_exceptional_local_factor_fixed_card_data S hS hnongeneric
  have hnorm := hcoord.normalized S A F hS
  obtain ⟨I, hAI, hIS, hIcard, _hcomm, hfull⟩ := hcoord
  have hFA : ⁅F, A⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (hFWA.trans (local_commutator_le_centralizer S A hS hAmax.1))
  have hdata := Representation.normalizedCThree_cardSixteen_elementaryTwo_action
    F A I S hS hAI hIS hnorm hFcard hAcard hIcard hFA
    (fun b hb hba => (hfull b hb hba).1) hUcard hfixed
  let U := commutatorAction F V
  let _ : IsInvariant I V U :=
    _root_.commutatorAction_isInvariant_of_normalizing_actor I F (hIS.trans hnorm)
  have hnonquad : commutatorAction₂ I U ≠ ⊥ := hdata.2.2.1
  have hFW : F ≤ oddCore G := hFWA.trans (local_commutator_le_oddCore S A)
  have hUVstar : U ≤ commutatorAction (oddCore G) V := by
    change commutatorAction F V ≤ _
    rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
    apply Subgroup.closure_mono
    rintro v ⟨f, x, rfl⟩
    exact ⟨(⟨f, hFW f.property⟩ : oddCore G), x, rfl⟩
  let T := commutatorSubgroup S V (commutatorAction (oddCore G) V)
  have hfirst : (commutatorAction I U).map U.subtype ≤ T := by
    rw [Subgroup.map_le_iff_le_comap, commutatorAction_eq_closure]
    apply (Subgroup.closure_le (K := T.comap U.subtype)).mpr
    rintro v ⟨i, x, rfl⟩
    exact Subgroup.subset_closure ⟨(⟨i, hIS i.property⟩ : S),
      (x : V), hUVstar x.property, rfl⟩
  have hsecond : (commutatorAction₂ I U).map U.subtype ≤ vStarAction₂ (G := G) (V := V) S := by
    rw [Subgroup.map_le_iff_le_comap]
    apply (Subgroup.closure_le (K := (vStarAction₂ (G := G) (V := V) S).comap U.subtype)).mpr
    rintro v ⟨i, x, hx, rfl⟩
    have hxT : (x : V) ∈ T := hfirst (Subgroup.mem_map_of_mem U.subtype hx)
    exact Subgroup.subset_closure ⟨(⟨i, hIS i.property⟩ : S), (x : V), hxT, rfl⟩
  intro hbot
  have hm : (commutatorAction₂ I U).map U.subtype = ⊥ :=
    le_antisymm (hsecond.trans hbot.le) bot_le
  exact hnonquad ((Subgroup.map_eq_bot_iff_of_injective _ U.subtype_injective).mp hm)

end Stellmacher.SectionOne

