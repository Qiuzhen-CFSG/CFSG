module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.SourceTheorems
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.Representation.BinaryOffender.MovedSpaceTransport


/-!
# A normally generating minimal offender selects one solvable factor

Restriction to an overgroup preserves the equal-weight minimality of a best
 offender. In a faithful solvable binary action with trivial two-core, B.1.8
places that minimal offender in a single factor's Sylow subgroup. If it
normally generates the whole group, first the offender subgroup and then
that factor must be the whole group. This gives an actual S₃ equivalence,
actor order two, and dimension two for the moved support.

This is the final use of B.1.8 in the first paragraph of B.1.9's proof,
Aschbacher–Smith, printed p.71 (PDF p.82). No assertion concerning the
false arbitrary-stable-family equality in B.1.8(5) is used.
-/

public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.FittingStructure.MinimalPlanes
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Equal-weight minimality is preserved inside any overgroup of the actor. -/
theorem minimal_subgroupOf {A H : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (hAH : A ≤ H) : IsMinimalBestOffender (ρ.comp H.subtype) (A.subgroupOf H) := by
  refine ⟨hA.1.subgroupOf ρ hAH, ?_⟩
  intro B hB hBA
  apply Subgroup.map_injective H.subtype_injective
  rw [map_subgroupOf_eq_of_le hAH]
  apply hA.2 _ (hB.map_subtype ρ)
  refine ⟨(map_mono hBA.1).trans_eq (map_subgroupOf_eq_of_le hAH), ?_⟩
  have hw := hBA.2
  rw [weight_comp_map ρ H.subtype H.subtype_injective,
    weight_comp_map ρ H.subtype H.subtype_injective,
    map_subgroupOf_eq_of_le hAH] at hw
  exact hw

variable [Finite G] [FiniteDimensional (ZMod 2) V]

/-- The genuine solvable structure theorem recognizes a single factor when
a minimal offender normally generates the group. -/
theorem solvable_minimal_normally_generating (hs : Group.IsSolvable G)
    (hc : pCore 2 G = ⊥) (hf : Function.Injective ρ)
    {A : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (hgen : normalClosure (A : Set G) = ⊤) :
    Nat.card A = 2 ∧ Nonempty (G ≃* Equiv.Perm (Fin 3)) ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ ⊤) = 2 := by
  obtain ⟨d, _, hm, _⟩ := source_lemma_B_1_8_corrected ρ hs hc hf
    ⟨A, hA.1.isOffender ρ⟩
  obtain ⟨i, S, he⟩ := (hm A).mp hA
  let : (offenderSubgroup ρ).Normal := offenderSubgroup_normal ρ
  have hJ : offenderSubgroup ρ = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact normalClosure_le_normal (hA.1.le_offenderSubgroup ρ)
  have hn : (d.factor i).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hJ]
    exact (normal_subgroupOf_iff_le_normalizer
      (d.toSolvableFFFactors.factor_le_offenderSubgroup i)).mp
      (d.toSolvableFFFactors.factor_normal_in_offenderSubgroup i)
  let := hn
  have hi : d.factor i = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact normalClosure_le_normal (he ▸ d.toSolvableFFFactors.factorSylow_le i S)
  obtain ⟨e⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  refine ⟨?_, ⟨((Subgroup.topEquiv.symm.trans
    (MulEquiv.subgroupCongr hi.symm)).trans (d.factorModel i)).trans e⟩, ?_⟩
  · rw [he]
    exact d.toSolvableFFFactors.factorSylow_card i S
  · rw [← hi]
    exact d.toSolvableFFFactors.support_finrank i

end CFSG.Quasithin.ChapterB.FittingStructure.MinimalPlanes
