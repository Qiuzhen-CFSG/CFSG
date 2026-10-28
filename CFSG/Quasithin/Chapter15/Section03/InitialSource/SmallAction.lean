module

public import CFSG.Quasithin.Chapter15.Section03.InitialSource.NaturalSplitting
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.SmallAction


/-!
# The full small action from the original 14.1.7 hypotheses

If both natural planes were separately invariant, each factor would fix
the other plane. Uniqueness would put both factor preimages inside Mc,
forcing M = Mc. Under the other original alternative, the two invariant
planes would instead contradict the central involution line. Thus the
two-factor permutation image is full. The final producer retains the
actual reduced action, selected J(M) image and natural coordinates, and
derives its dimensions and orders, respectively 2 and 6 or 4 and 72.

Source: Aschbacher–Smith, 14.1.7, printed p.977; the binary quadratic
model is the one specified on printed pp.1121–1122.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource
variable {G : Type*} [Group G] [Finite G]

theorem factor_permutation_nontrivial_of_two
    (T : Sylow 2 G) {M Mc : Subgroup G}
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hcase : M ≠ Mc ∨ Nat.card (centralInvolutions T) = 2)
    (U : Subgroup M) [U.Normal] [IsElementaryAbelian 2 U]
    (d : ChapterB.SolvableFFFactors (NormalElementaryQuotient.representation U
      (QuotientGroup.mk' (centralizer (U : Set M)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _))) (hn : d.count = 2)
    (hcentral : centralizer (offenderSubgroup (NormalElementaryQuotient.representation U
      (QuotientGroup.mk' (centralizer (U : Set M)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) :
        Set (M ⧸ centralizer (U : Set M))) = ⊥) :
    ∃ g, d.factorConjugation g ≠ 1 := by
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  let ρ := NormalElementaryQuotient.representation U q (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _)
  let K := offenderSubgroup ρ
  by_contra hperm
  push Not at hperm
  have hnormal (i : Fin d.count) : (d.factor i).Normal := by
    constructor
    intro x hx g
    have hm := mem_map_of_mem (MulAut.conj g).toMonoidHom hx
    rw [d.factor_map_conj, hperm] at hm
    exact hm
  let : Nontrivial (Fin d.count) := by rw [hn]; infer_instance
  rcases hcase with hneq | hZ
  · have hKtop : K = ⊤ := by
      apply top_unique
      intro g _
      have hh := d.factorConjugation_kernel_le (show g ∈ d.factorConjugation.ker from hperm g)
      simpa only [hcentral, sup_bot_eq] using hh
    have hpre (i : Fin d.count) : (d.factor i |>.comap q).map M.subtype ≤ Mc := by
      let := hnormal i
      obtain ⟨j, hji⟩ := exists_ne i
      have hfix : fixedSpace ρ (d.factor i) ≠ ⊥ := by
        intro he
        exact d.support_ne_bot j (bot_unique
          (he ▸ d.support_le_fixedSpace_other hji.symm))
      exact normal_actor_preimage_le_partner_of_fixed_ne_bot T hM.2 hunique U (d.factor i) hfix
    let B := Mc.subgroupOf M
    have hBi (i : Fin d.count) : (d.factor i).comap q ≤ B := by
      intro x hx
      exact hpre i (mem_map_of_mem M.subtype hx)
    have hBm : B.map q = ⊤ := by
      apply top_unique
      rw [← hKtop]
      apply d.iSup_factor.ge.trans
      apply iSup_le
      intro i
      rw [← map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) (H := d.factor i)]
      exact map_mono (hBi i)
    have hker : q.ker ≤ B := by
      intro x hx
      apply hBi ⟨0, d.count_pos⟩
      change q x ∈ d.factor ⟨0, d.count_pos⟩
      rw [show q x = 1 from hx]
      exact (d.factor ⟨0, d.count_pos⟩).one_mem
    have hBtop : B = ⊤ := by
      rw [← comap_map_eq_self hker, hBm, comap_top]
    have hMMc : M ≤ Mc := by
      intro x hx
      exact (show (⟨x, hx⟩ : M) ∈ B by rw [hBtop]; trivial)
    have hMc : IsMaximalTwoLocal Mc :=
      (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
        hunique ▸ Set.mem_singleton Mc).1
    exact hneq (hM.1.eq_of_le hMc.1 hMMc)
  · let i : Fin d.count := ⟨0, d.count_pos⟩
    obtain ⟨j, hji⟩ := exists_ne i
    have hstab (k : Fin d.count) : ((T.subtype hM.2 : Sylow 2 M) : Subgroup M).map q ≤
        subspaceStabilizer ρ (subspaceCommutator ρ ⊤ (d.factor k)) := by
      let := hnormal k
      exact subspaceCommutator_invariant_normalizer ρ
        (le_subspaceStabilizer ρ ⊤ (fun _ _ _ _ => Submodule.mem_top)) le_normalizer_of_normal
    have hh := disjoint_stable_subspaces_of_central_order_two T hM.2 hZ U
      (subspaceCommutator ρ ⊤ (d.factor i)) (subspaceCommutator ρ ⊤ (d.factor j))
      (d.supports_independent.pairwiseDisjoint hji.symm) (hstab i) (hstab j)
    exact hh.elim (d.support_ne_bot i) (d.support_ne_bot j)

universe u

/-- The source action fills the permutation group of its actual natural factors. -/
theorem reduced_small_action_from_source
    {G : Type u} [Group G] [Finite G]
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hcase : M ≠ Mc ∨ Nat.card (centralInvolutions T) = 2)
    (U : Subgroup M) (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ ((T.subtype hM.2 : Sylow 2 M) : Subgroup M) ≤
      centralizer (U : Set M)) :
    letI := hU.normal
    letI := hU.elementary
    let q := QuotientGroup.mk' (centralizer (U : Set M))
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    let P := ChapterB.maxOffenderImages (⊤ : Subgroup M) U q
    ∃ d : ChapterB.ThreeConjugates.SolvableFFStructure ρ,
      (d.count = 1 ∨ d.count = 2) ∧ IsStable (V := Additive U) ρ P ∧
      (elementaryAbelianMaxJ (⊤ : Subgroup M)).map q = generatedBy P ⊤ ∧
      (d.toSolvableFFFactors.stableFactorSet P).Nonempty ∧
      (elementaryAbelianMaxJ (⊤ : Subgroup M)).map q =
        ⨆ i ∈ d.toSolvableFFFactors.stableFactorSet P, d.factor i ∧
      fixedSpace ρ (offenderSubgroup ρ) = ⊥ ∧
      subspaceCommutator ρ ⊤ (offenderSubgroup ρ) = ⊤ ∧
      centralizer (offenderSubgroup ρ : Set (M ⧸ centralizer (U : Set M))) = ⊥ ∧
      Function.Surjective d.toSolvableFFFactors.factorConjugation ∧
      Module.finrank (ZMod 2) (Additive U) = 2 * d.count ∧
      Nat.card (M ⧸ centralizer (U : Set M)) = 6 ^ d.count * d.count.factorial := by
  let := hU.normal
  let := hU.elementary
  obtain ⟨d, hn, hstable, hgen, hselected, hJprod, hF, hW, hcentral⟩ :=
    reduced_natural_sum_from_source hA hC hG T hempty hM hunique hcase U hU hJ
  have honto : Function.Surjective d.toSolvableFFFactors.factorConjugation := by
    rcases hn with h | h
    · let : Subsingleton (Fin d.count) := by rw [h]; infer_instance
      intro a
      exact ⟨1, Subsingleton.elim _ _⟩
    · obtain ⟨g, hg⟩ := factor_permutation_nontrivial_of_two T hM hunique hcase U
        d.toSolvableFFFactors h hcentral
      have hc : Nat.card (Equiv.Perm (Fin d.count)) = 2 := by
        rw [Nat.card_perm, Nat.card_fin, h]
        decide
      let : Fact (Nat.card (Equiv.Perm (Fin d.count))).Prime := ⟨by rw [hc]; exact Nat.prime_two⟩
      apply MonoidHom.range_eq_top.mp
      apply d.toSolvableFFFactors.factorConjugation.range.eq_bot_or_eq_top_of_prime_card.resolve_left
      intro he
      exact hg (Subgroup.mem_bot.mp (he ▸
        (show d.toSolvableFFFactors.factorConjugation g ∈
          d.toSolvableFFFactors.factorConjugation.range from ⟨g, rfl⟩)))
  have hd := d.toSolvableFFFactors.commutator_finrank
  rw [hW, finrank_top] at hd
  exact ⟨d, hn, hstable, hgen, hselected, hJprod, hF, hW, hcentral, honto, hd,
    d.toSolvableFFFactors.card_of_full_factorConjugation hcentral honto⟩


end CFSG.Quasithin.Chapter15.Section03.InitialSource
