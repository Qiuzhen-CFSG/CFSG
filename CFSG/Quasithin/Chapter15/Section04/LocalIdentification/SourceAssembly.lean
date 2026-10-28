module

public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.AlternateE9
public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.AlternateObstruction
public import CFSG.Quasithin.Chapter15.Section04.Configuration.ModuleContradiction
public import Theory.GroupTheory.TwoPerfectCyclicQuotient

/-!
# Assembly of the source local alternatives in 15.4.23

This module connects the genuine earlier outputs of 15.4.21 and 15.4.22 to
the already proved E₉ obstruction and final pairwise module contradiction.
The two earlier source classification results remain explicit hypotheses.
No cross-commutator, E₉, factor identification or core-order conclusion is
assumed. The quotient in the exceptional output is literally I/C_T(K).

Proof: a two-perfect normalizing subgroup acts trivially on a quotient of
order three, because its automorphism group has order two. Thus relative
normality in the first branch supplies the cross-commutator. Apply the same
source alternatives to the other X-factor and the same Y-factor. Their
already proved E₉ construction contradicts the normalizer three-rank bound.
Both pairs therefore have exceptional supplements, and their recognized
commutator modules give the final contradiction inside V(M₁).

Source: Aschbacher–Smith 15.4.21–23 and the paragraph following 15.4.23,
printed pp.1164–1165 (combined manuscript, 1 March 2004).

-/

@[expose] public section

open Subgroup
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter15.Section04.Source

variable {G : Type*} [Group G] [Finite G] {d : Geometry G}

/-- This is the exact cross bound implicit in the first sentence of 15.4.23.
Its source input is relative normality from 15.4.21, not the bound itself. -/
theorem LocalData.cross_commutator_of_factor_normal (h : LocalData d) (i j : Bool)
    (hN : ((d.X i).subgroupOf (d.I i j)).Normal) :
    ⁅d.Y j, d.X i⁆ ≤ (d.X i).pCoreIn 2 := by
  have hI : d.I i j ≤ normalizer (d.X i : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (d.X_le_I i j)).mp hN
  exact commutator_le_pCoreIn_of_twoPerfect_of_normalizes_of_quotient_card_three
    (d.X i) (d.Y j) (h.Y_perfect j) ((d.Y_le_I i j).trans hI)
    (h.X_quotient_card i)

/-- The genuine earlier alternatives prove 15.4.23 uniformly for all four
pairs. Only relative normality and an actual A₆ subgroup are needed here.
The stronger normal-supplement and quotient conclusions are used afterwards. -/
theorem LocalData.generalizedFitting_ne_twoCore_of_source_alternatives
    (h : LocalData d)
    (h21 : ∀ i j, Theory.GroupTheory.generalizedFitting (d.I i j) =
      pCore 2 (d.I i j) → ((d.X i).subgroupOf (d.I i j)).Normal)
    (h22 : ∀ i j, Theory.GroupTheory.generalizedFitting (d.I i j) ≠
      pCore 2 (d.I i j) →
      ∃ K : Subgroup (d.I i j), Nonempty (K ≃* alternatingGroup (Fin 6)))
    (i j : Bool) :
    Theory.GroupTheory.generalizedFitting (d.I i j) ≠ pCore 2 (d.I i j) := by
  intro hF
  have hcross := h.cross_commutator_of_factor_normal i j (h21 i j hF)
  have hcases : ((d.X (!i)).subgroupOf (d.alternateI i j)).Normal ∨
      ∃ K : Subgroup G, K ≤ d.alternateI i j ∧
        Nonempty (K ≃* alternatingGroup (Fin 6)) := by
    by_cases hF' : Theory.GroupTheory.generalizedFitting (d.I (!i) j) =
        pCore 2 (d.I (!i) j)
    · exact Or.inl (h21 (!i) j hF')
    · obtain ⟨K, ⟨eK⟩⟩ := h22 (!i) j hF'
      refine Or.inr ⟨K.map (d.I (!i) j).subtype, map_subtype_le K, ?_⟩
      exact ⟨(K.equivMapOfInjective (d.I (!i) j).subtype
        (d.I (!i) j).subtype_injective).symm.trans eK⟩
  obtain ⟨P, hp, hc, hPI, hd⟩ :=
    h.alternate_E9_of_cross_commutator i j hcross hcases
  let _ := hp
  exact h.no_alternate_E9_of_cross_commutator i j P hc hPI hd hcross

/-- Conditional source assembly of the paragraph after 15.4.23. The only
remaining mathematical premises are the actual earlier 15.4.21 and 15.4.22
outputs, simultaneously for the two X-choices and the same Y-choice.
All embeddings and the centralizer quotient retain the source conventions. -/
theorem LocalData.false_of_source_local_alternatives
    (h : LocalData d)
    (h21 : ∀ i j, Theory.GroupTheory.generalizedFitting (d.I i j) =
      pCore 2 (d.I i j) → ((d.X i).subgroupOf (d.I i j)).Normal)
    (h22 : ∀ i j, Theory.GroupTheory.generalizedFitting (d.I i j) ≠
      pCore 2 (d.I i j) →
      ∃ K : Subgroup (d.I i j), K.Normal ∧
        K ⊔ (h.sylow i j : Subgroup (d.I i j)) = ⊤ ∧
        Nonempty (K ≃* alternatingGroup (Fin 6)) ∧
        ∃ hC : (((d.T : Subgroup G) ⊓
          centralizer (K.map (d.I i j).subtype : Set G)).subgroupOf (d.I i j)).Normal,
          let _ := hC
          Nonempty (((d.I i j) ⧸ (((d.T : Subgroup G) ⊓
            centralizer (K.map (d.I i j).subtype : Set G)).subgroupOf (d.I i j))) ≃*
              Equiv.Perm (Fin 6))) : False := by
  classical
  have h22' : ∀ i j, Theory.GroupTheory.generalizedFitting (d.I i j) ≠
      pCore 2 (d.I i j) →
      ∃ K : Subgroup (d.I i j), Nonempty (K ≃* alternatingGroup (Fin 6)) := by
    intro i j hF
    obtain ⟨K, _, _, hK, _⟩ := h22 i j hF
    exact ⟨K, hK⟩
  have hF (i j : Bool) :=
    h.generalizedFitting_ne_twoCore_of_source_alternatives h21 h22' i j
  have hex (i : Bool) := h22 i false (hF i false)
  choose K hKn hgen hKe hC hQe using hex
  let _ : ∀ i, (K i).Normal := hKn
  let _ : ∀ i, (((d.T : Subgroup G) ⊓
    centralizer ((K i).map (d.I i false).subtype : Set G)).subgroupOf
      (d.I i false)).Normal := hC
  let eK := fun i => Classical.choice (hKe i)
  let eT := fun i => Classical.choice (hQe i)
  exact h.false_of_pairwise_exceptional_recognition K hgen eK eT

end CFSG.Quasithin.Chapter15.Section04.Source
