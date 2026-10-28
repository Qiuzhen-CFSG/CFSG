module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.ParabolicApplication
public import CFSG.Quasithin.Chapter13.Section05.A5Source.ChiefCount
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.SymmetricSixSource.Count

/-!
# The original A₅ symmetric-six exclusion

The marked syntheme residual makes every actual cubic subgroup contribute
length two on U_H, and its A₄ star image contributes one further noncentral
binary chief factor. The same original residual has even count by13.5.22.
Their incompatible counts exclude the S₆ natural central quotient.
Source: Aschbacher–Smith13.5.24, printed p.925.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open ComponentReduction Section08.Source Recognition Recognition.Configuration
open Recognition.MarkedModule Recognition.MarkedModule.AlternatingParabolics
open ChiefCount.SymmetricSixSource ChiefCount.SymmetricSixModel
universe u
variable {G : Type u} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ : Subgroup G} [IsElementaryAbelian 2 D.V]
  (d : Context D.T D.L D.V D.V₁ V₂ D.Vplus) (h : D.Hypothesis)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : D.H ∈ Section08.Source.Hz D.L₁ D.T
    (centralizer (D.V₁ : Set G)) (normalizer (D.L : Set G)))
  (hU : ¬ IsMulCommutative D.UH)
include d hA312 hH hU

/-- Cauchy's theorem supplies an actual cubic subgroup of the original residual. -/
theorem source_exists_cubic : ∃ A : Subgroup G, A ≤ D.L₁ ∧ Nat.card A = 3 := by
  have hc : Nat.card (D.L₁ ⧸ pCore 2 D.L₁) = 3 := residual_quotient_card d hA312 hH hU
  have hd : 3 ∣ Nat.card D.L₁ := hc ▸ card_quotient_dvd_card (pCore 2 D.L₁)
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := D.L₁) 3 hd
  refine ⟨(zpowers a).map D.L₁.subtype,map_subtype_le _,?_⟩
  rw [card_map_of_injective D.L₁.subtype_injective,Nat.card_zpowers,ha]

variable [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]
  (hnot : ¬ ModelConclusion G 5)
include h hnot

/-- Three noncentral binary chief factors on the same original residual. -/
theorem symmetric_six_source_count_three
    (K : Subgroup G) (s : Selected D K) (hLK : D.L₁ ≤ K)
    (f : Catalogue.actor D K ≃* Equiv.Perm (Fin 6))
    (fV : CentralQuotient.Space D h K ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (hfV : ∀ b : Catalogue.actor D K, ∀ u,
      centralProjection D h fV (Action.starRepresentation D h b.val u) =
        BinaryPermutation.naturalRepresentation (Fin 6) (f b) (centralProjection D h fV u))
    (A : Subgroup G) (hAL : A ≤ D.L₁) (hA : Nat.card A = 3)
    (t : NoncentralChiefRefinement.ChiefSeries D.L₁) (h0 : t.head = ⊥) (h1 : t.last = ⊤) :
    t.noncentralTwoCount = 3 := by
  have hSQ := (Chapter1.Section02.uniqueness_local_quotient_sqtk
    d.hypothesis.qtke hH.1.1).stronglyQuasithin
  have hm := source_local_component_commutator d h hA312 hH hnot K s
  obtain ⟨S,hS,hirr⟩ := source_local_seed_irreducible d h hU
  let := hirr
  have hmodule := local_seed_module_conditions d h hU
  obtain ⟨c,hc,g,hg⟩ := symmetric_six_residual_marking D h s hSQ hLK hm S hS
    hmodule.2.2 hmodule.2.1.symm f fV hfV
  have hLC : starImage D.H D.L₁ ≤ starImage D.H K := map_mono (comap_mono hLK)
  let eL : starImage D.H D.L₁ ≃* alternatingGroup (Fin 4) :=
    ((subgroupOfEquivOfLe hLC).symm.trans
      (c.subgroupMap ((starImage D.H D.L₁).subgroupOf (starImage D.H K)))).trans
      ((MulEquiv.subgroupCongr hg).trans (conjugateResidualEquiv g))
  have hgroup := group_conclusions s h hSQ d.third_index hU hLK d.third_eq_commutator hm
    (selected_actor_normalization s h d.third_index hU).2
  have htilde := symmetric_six_tilde_generation D h s d.hypothesis.qtke.properK hSQ
    hLK d.third_eq_commutator hm S hS hmodule.2.2 hmodule.2.1.symm f fV hfV
  have hUL : D.UH ≤ D.L₁ :=
    (closure_reduction_of_tilde d hA312 hH htilde).2.1.trans (pCoreIn_le 2 D.L₁)
  rw [count_eq_kernel_length_add_one D h eL A hAL hA t h0 h1,
    kernel_length_eq_closure D h A hAL hLK hA hgroup.2.2.2 hUL,
    marked_closure_length_two D h s.le_H hLK f fV hfV c hc g hg A hAL hA]

/-- The S₆ natural central quotient contradicts the original A₅ source count. -/
theorem symmetric_six_source_false
    (K : Subgroup G) (s : Selected D K) (hLK : D.L₁ ≤ K)
    (f : Catalogue.actor D K ≃* Equiv.Perm (Fin 6))
    (fV : CentralQuotient.Space D h K ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (hfV : ∀ b : Catalogue.actor D K, ∀ u,
      centralProjection D h fV (Action.starRepresentation D h b.val u) =
        BinaryPermutation.naturalRepresentation (Fin 6) (f b) (centralProjection D h fV u)) :
    False := by
  obtain ⟨A,hAL,hA⟩ := source_exists_cubic d hA312 hH hU
  obtain ⟨t,h0,h1⟩ := NoncentralChiefRefinement.exists_chiefSeries
    (⊥ : NoncentralChiefRefinement.NormalNode D.L₁) ⊤ bot_le
  have htilde := (symmetric_six_source_conclusions d h hA312 hH hnot hU K s hLK f fV hfV).2.2.2
  obtain ⟨g,hg,hg₁⟩ := d.exists_block_conjugator
  exact source_three_factor_exclusion d hA312 hH hU hg hg₁ htilde t h0 h1
    (symmetric_six_source_count_three d h hA312 hH hU hnot K s hLK f fV hfV A hAL hA t h0 h1)
end CFSG.Quasithin.Chapter13.Section05.A5Source
