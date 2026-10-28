module
public import CFSG.Quasithin.Chapter10.SourceA5OffenderContainment
public import CFSG.Quasithin.Chapter10.SourceA5WeakClosureCommutation

/-!
# Small-corank commutation for the chosen A₅ module

The actual offender centralization estimates and rank-kernel containment
supply the moved-factor input to the four-conjugator commutation argument.
Thus every corank-one conjugate commutes with the full module, and the
deleted alternative permits corank two. The chosen irreducibility and
point-centralizer hypotheses remain the genuine earlier source inputs.

Source: Aschbacher--Smith, quasithin 10.2.12, printed pp.754–755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
local instance (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

theorem source_a5_small_conjugates_commute_of_centralizing_intersections
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hcent : ∀ u ∈ ⁅D.fullModule,L⁆, u ≠ 1 → centralizer ({u} : Set G) ≤ D.maximalLocal)
    {k : ℕ} (hk : k ≤ 2)
    (hcentral : ∀ g ∉ D.maximalLocal,
      subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
        (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ k →
      (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal ≤
        centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    {g : G}
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ k) :
    ⁅D.fullModule,D.fullModule.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  apply source_a5_small_conjugates_commute_of_moved_factor D hn ht hcross k ?_ g hsmall
  intro x hx hxs
  have hc := hcentral x hx hxs
  have hm := source_a5_conjugate_moved_le_of_intersection_centralizes D e hi hn ht htn
    hcross hcent (hxs.trans hk) hc
  exact ⟨hm, by rwa [inf_eq_left.mpr hm] at hc⟩

theorem source_a5_corank_one_conjugates_commute
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hcent : ∀ u ∈ ⁅D.fullModule,L⁆, u ≠ 1 → centralizer ({u} : Set G) ≤ D.maximalLocal)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    {g : G}
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 1) :
    ⁅D.fullModule,D.fullModule.map (MulAut.conj g).toMonoidHom⁆ = ⊥ :=
  source_a5_small_conjugates_commute_of_centralizing_intersections D e hi hn ht htn
    hcross hcent (by decide : 1 ≤ 2)
    (fun _ hx hs => source_a5_corank_one_offender_centralizes_moved D e hi hn ht htn
      hcross hcent hNL hx hs) hsmall

theorem source_a5_deleted_corank_two_conjugates_commute
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (f : alternatingGroup (Fin 5) ≃* alternatingGroup (Fin 5))
    (c : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      (Representation.OrthogonalFourMinus.AlternatingFive.alternatingRepresentation.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hcent : ∀ u ∈ ⁅D.fullModule,L⁆, u ≠ 1 → centralizer ({u} : Set G) ≤ D.maximalLocal)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    {g : G}
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 2) :
    ⁅D.fullModule,D.fullModule.map (MulAut.conj g).toMonoidHom⁆ = ⊥ :=
  source_a5_small_conjugates_commute_of_centralizing_intersections D e hi hn ht htn
    hcross hcent (le_refl 2)
    (fun _ hx hs => source_a5_deleted_corank_two_offender_centralizes_moved D e hi f c hn ht htn
      hcross hcent hNL hx hs) hsmall

end CFSG.Quasithin.Chapter10
