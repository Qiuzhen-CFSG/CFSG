module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentNormality
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CyclicComponent
public import CFSG.Quasithin.ChapterA.Section02.Statements
/-!
# F.6.10 on the actual SQTK quotient and the cyclic component reduction

Theorem A transfers the covering group's odd-rank bounds to the semisimple
section E(G). The layer-rank orbit theorem and the Goldschmidt Sylow-span
argument make each component normal. F.6.7–8 then place one of the two
original local residuals in it, and residual generation supplies G=KGᵢ.
The literal O₃′ quotient automatically has trivial two-core.

The final consumer combines this with the constructed component in the
cyclic-three-core branch, choosing both the component and the orientation
needed by F.6.17. The only earlier source premise is Theorem A for the
original SQTK cover; its discharge remains with the A.2 assembly.

Source: Aschbacher–Smith, F.6.10 and F.6.17, printed pp.306 and 309.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
universe u
variable {G : Type u} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

/-- A normal component contains one original local residual and supplements the other vertex. -/
theorem normal_component_contains_residual
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    {K : Subgroup G} (hK : IsComponent G K) [K.Normal] :
    ((pResidual 2 G₁).map G₁.subtype ≤ K ∧ K ⊔ G₂ = ⊤) ∨
    ((pResidual 2 G₂).map G₂.subtype ≤ K ∧ K ⊔ G₁ = ⊤) := by
  by_cases h₁ : (pResidual 2 G₁).map G₁.subtype ≤ K
  · exact Or.inl ⟨h₁, top_unique (h.left_residual_sup_right.symm ▸ sup_le_sup_right h₁ G₂)⟩
  by_cases h₂ : (pResidual 2 G₂).map G₂.subtype ≤ K
  · exact Or.inr ⟨h₂, top_unique (h.symm.left_residual_sup_right.symm ▸ sup_le_sup_right h₂ G₁)⟩
  have hI : (G₁ ⊓ G₂) ⊓ K = ⊥ := le_bot_iff.mp
    ((h.normal_intersection_le_twoCore K
      ((h.left_subnormal_core_iff_not_residual_le K hK.1).mpr h₁)
      ((h.right_subnormal_core_iff_not_residual_le K hK.1).mpr h₂)).trans hcore.le)
  obtain ⟨P, hP⟩ := h.subnormal_intersection_sylow K hK.1
  have hPbot : (P : Subgroup K) = ⊥ := by
    apply map_injective K.subtype_injective
    rw [hP, subgroupOf_map_subtype, Subgroup.map_bot]
    exact hI
  have hodd : Odd (Nat.card K) := by
    have hind := P.not_dvd_index
    rw [hPbot, index_bot] at hind
    exact Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using hind)
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  exact (Group.IsPerfect.not_isSolvable K (odd_order_theorem K hodd)).elim

variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

/-- Theorem A transfers the covering group's rank bounds to the actual layer of its quotient. -/
theorem quotient_layer_strongly_quasithin
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (f : H →* G) (hf : Function.Surjective f) :
    IsStronglyQuasithin (componentLayer G) :=
  hA.stronglyQuasithin_section hH.stronglyQuasithin hH.isKGroup
    ((ChapterA.Section02.IsSectionOf.subgroup (componentLayer G)).ambient_surjective f hf)
    componentLayer_idempotent

/-- The source component normality, local containment and generation in the
core-free SQTK quotient. The only earlier theorem retained is Theorem A. -/
theorem source_component_reduction
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (f : H →* G) (hf : Function.Surjective f)
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    {K : Subgroup G} (hK : IsComponent G K) :
    K.Normal ∧
      (((pResidual 2 G₁).map G₁.subtype ≤ K ∧ K ⊔ G₂ = ⊤) ∨
       ((pResidual 2 G₂).map G₂.subtype ≤ K ∧ K ⊔ G₁ = ⊤)) := by
  have horbit := hK.normal_or_index_two_of_layer_odd_rank_le_two
    (quotient_layer_strongly_quasithin hA hH f hf)
  have hnormal := component_normal_of_orbit_two h hcore hK horbit
  let : K.Normal := hnormal
  exact ⟨hnormal, normal_component_contains_residual h hcore hK⟩

/-- The literal O₃′ quotient supplies the core-free hypothesis; no orbit or
component-containment output is assumed at this consumer. -/
theorem source_lemma_F_6_10_sqtk_quotient
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (e : G ≃* (H ⧸ pPrimeCore 3 H)) (h : IsGoldschmidtTriple G₁ G₂)
    {K : Subgroup G} (hK : IsComponent G K) :
    K.Normal ∧
      (((pResidual 2 G₁).map G₁.subtype ≤ K ∧ K ⊔ G₂ = ⊤) ∨
       ((pResidual 2 G₂).map G₂.subtype ≤ K ∧ K ⊔ G₁ = ⊤)) := by
  let f := e.symm.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 3 H))
  exact source_component_reduction hA hH f
    (e.symm.surjective.comp (QuotientGroup.mk'_surjective _)) h
    (le_bot_iff.mp (twoCore_le_primeToThreeCore.trans
      (Noncyclic.primeToThreeCore_eq_bot_of_quotient e).le)) hK

/-- The first reduction of F.6.17 constructs a normal component and chooses
the local residual it contains, from the literal original quotient. -/
theorem cyclic_component_reduction
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (e : G ≃* (H ⧸ pPrimeCore 3 H)) (h : IsGoldschmidtTriple G₁ G₂)
    (hc : IsCyclic (pCore 3 G)) :
    ∃ K : Subgroup G, IsComponent G K ∧ K.Normal ∧ ¬ K ≤ pCore 3 G ∧
      (((pResidual 2 G₁).map G₁.subtype ≤ K ∧ K ⊔ G₂ = ⊤) ∨
       ((pResidual 2 G₂).map G₂.subtype ≤ K ∧ K ⊔ G₁ = ⊤)) := by
  obtain ⟨K, hK, hnot⟩ := Cyclic.exists_component_of_cyclic_three_core_quotient e h hc
  obtain ⟨hn, hg⟩ := source_lemma_F_6_10_sqtk_quotient hA hH e h hK
  exact ⟨K, hK, hn, hnot, hg⟩

end CFSG.Quasithin.ChapterF.SourceAssembly
