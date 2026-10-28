module

public import CFSG.Quasithin.Chapter15.Section03.InitialSource.NaturalSplitting
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.SmallAction


/-!
# The small action with a central involution line

The |Ω₁Z(T)|=2 argument is independent of a distinguished unique local
overgroup. Nonzero fixed and moved summands, or two separately invariant
natural planes, would both contradict that central line. This gives the
full small action from the actual constructed factors. The solvable-local
consumer builds those factors using B.2.7 and proved B.1.8 and discharges
their count by quasithinness of the original maximal two-local.

This supplies the |Z|=2 subcase of 14.1.7 and the same small-action
calculation needed in 15.4.7, without an Mc or empty-family premise.

Source: Aschbacher–Smith, 14.1.7, printed p.977, and the natural
action boundary of 15.1.3/15.3, printed pp.1086 and 1121–1122.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource
variable {G : Type*} [Group G] [Finite G]

theorem small_action_of_central_order_two
    (T : Sylow 2 G) {M : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (hZ : Nat.card (centralInvolutions T) = 2)
    (U : Subgroup M) [U.Normal] [IsElementaryAbelian 2 U]
    (d : ChapterB.SolvableFFFactors (NormalElementaryQuotient.representation U
      (QuotientGroup.mk' (centralizer (U : Set M)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)))
    (hn : d.count = 1 ∨ d.count = 2) :
    let q := QuotientGroup.mk' (centralizer (U : Set M))
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    subspaceCommutator ρ ⊤ (offenderSubgroup ρ) = ⊤ ∧
    centralizer (offenderSubgroup ρ : Set (M ⧸ centralizer (U : Set M))) = ⊥ ∧
    Function.Surjective d.factorConjugation ∧
    Module.finrank (ZMod 2) (Additive U) = 2 * d.count ∧
    Nat.card (M ⧸ centralizer (U : Set M)) = 6 ^ d.count * d.count.factorial := by
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  have hF := fixed_eq_bot_of_factors_and_central_order_two T hTM hZ U d
  have hW : subspaceCommutator ρ ⊤ (offenderSubgroup ρ) = ⊤ := by
    have he := d.moved_complement.sup_eq_top
    rw [hF, sup_bot_eq] at he
    exact he
  have hcentral : centralizer (offenderSubgroup ρ : Set (M ⧸ centralizer (U : Set M))) = ⊥ := by
    apply bot_unique
    intro c hc
    apply Subgroup.mem_bot.mpr
    apply NormalElementaryQuotient.representation_injective U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    apply LinearMap.ext
    intro v
    change ρ c v = ρ 1 v
    rw [map_one, Module.End.one_apply]
    exact d.centralizer_fixes_moved c hc (hW.symm ▸ Submodule.mem_top)
  have honto : Function.Surjective d.factorConjugation := by
    rcases hn with h | h
    · let : Subsingleton (Fin d.count) := by rw [h]; infer_instance
      intro a
      exact ⟨1, Subsingleton.elim _ _⟩
    · have hne : ∃ g, d.factorConjugation g ≠ 1 := by
        by_contra hperm
        push Not at hperm
        have hnormal (i : Fin d.count) : (d.factor i).Normal := by
          constructor
          intro x hx g
          have hm := mem_map_of_mem (MulAut.conj g).toMonoidHom hx
          rw [d.factor_map_conj, hperm] at hm
          exact hm
        let : Nontrivial (Fin d.count) := by rw [h]; infer_instance
        let i : Fin d.count := ⟨0, d.count_pos⟩
        obtain ⟨j, hji⟩ := exists_ne i
        have hstab (k : Fin d.count) : ((T.subtype hTM : Sylow 2 M) : Subgroup M).map q ≤
            subspaceStabilizer ρ (subspaceCommutator ρ ⊤ (d.factor k)) := by
          let := hnormal k
          exact subspaceCommutator_invariant_normalizer ρ
            (le_subspaceStabilizer ρ ⊤ (fun _ _ _ _ => Submodule.mem_top)) le_normalizer_of_normal
        have hh := disjoint_stable_subspaces_of_central_order_two T hTM hZ U
          (subspaceCommutator ρ ⊤ (d.factor i)) (subspaceCommutator ρ ⊤ (d.factor j))
          (d.supports_independent.pairwiseDisjoint hji.symm) (hstab i) (hstab j)
        exact hh.elim (d.support_ne_bot i) (d.support_ne_bot j)
      obtain ⟨g, hg⟩ := hne
      have hc : Nat.card (Equiv.Perm (Fin d.count)) = 2 := by
        rw [Nat.card_perm, Nat.card_fin, h]
        decide
      let : Fact (Nat.card (Equiv.Perm (Fin d.count))).Prime := ⟨by rw [hc]; exact Nat.prime_two⟩
      apply MonoidHom.range_eq_top.mp
      apply d.factorConjugation.range.eq_bot_or_eq_top_of_prime_card.resolve_left
      intro he
      exact hg (Subgroup.mem_bot.mp (he ▸
        (show d.factorConjugation g ∈ d.factorConjugation.range from ⟨g, rfl⟩)))
  have hd := d.commutator_finrank
  rw [hW, finrank_top] at hd
  exact ⟨hW, hcentral, honto, hd, d.card_of_full_factorConjugation hcentral honto⟩

/-- Actual solvable maximal-local consumer, with no empty-family or Mc premise. -/
theorem solvable_small_action_of_central_order_two
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {M : Subgroup G}
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hZ : Nat.card (centralInvolutions T) = 2) (hsolv : Group.IsSolvable M)
    (U : Subgroup M) (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ ((T.subtype hM.2 : Sylow 2 M) : Subgroup M) ≤
      centralizer (U : Set M)) :
    letI := hU.normal
    letI := hU.elementary
    let q := QuotientGroup.mk' (centralizer (U : Set M))
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    ∃ d : ChapterB.ThreeConjugates.SolvableFFStructure ρ,
      (d.count = 1 ∨ d.count = 2) ∧
      subspaceCommutator ρ ⊤ (offenderSubgroup ρ) = ⊤ ∧
      centralizer (offenderSubgroup ρ : Set (M ⧸ centralizer (U : Set M))) = ⊥ ∧
      Function.Surjective d.toSolvableFFFactors.factorConjugation ∧
      Module.finrank (ZMod 2) (Additive U) = 2 * d.count ∧
      Nat.card (M ⧸ centralizer (U : Set M)) = 6 ^ d.count * d.count.factorial := by
  let := hU.normal
  let := hU.elementary
  let := hsolv
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  obtain ⟨d, _⟩ := ChapterB.thompson_factors_of_solvable_action U q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) (T.subtype hM.2) hJ
    (inferInstance : Group.IsSolvable (M ⧸ centralizer (U : Set M))) hU.quotient_pCore_eq_bot
  have hrank : primeRank 3 M ≤ 2 :=
    Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hG.quasithin M hM.1.1 3 (by decide) (by decide)
  have hn := d.toSolvableFFFactors.count_eq_one_or_two_of_surjective_threeRank q
    (QuotientGroup.mk'_surjective _) hrank
  exact ⟨d, hn, small_action_of_central_order_two T hM.2 hZ U d.toSolvableFFFactors hn⟩

end CFSG.Quasithin.Chapter15.Section03.InitialSource
