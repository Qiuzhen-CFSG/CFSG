module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.NaturalCentralizer
public import Theory.GroupAction.SymmetricSixChiefBudget.Centralization
public import Theory.GroupAction.SymmetricSixChiefBudget.SmallCommutators
public import Theory.GroupTheory.SubgroupTransport

/-!
# Centralization and chief-factor bounds in the nonabelian case-one branch

The constructed conjugate U_Hˡ maps to the marked even radical D₀ in S₆.
It centralizes an index-at-most-two subgroup of H_C modulo V_H. Each
noncentral binary chief factor costs at least four under an even
involution, so O²(H) centralizes the entire actual H_C/V_H section.
No abelianness of this quotient is assumed.

On V_H/U_H, the source commutator lies in the line VU_H/U_H. Its
restriction to the index-at-most-two intersection with Hˡ therefore
has fixed index at most two for each chosen element of U_Hˡ, and at
most four on the whole quotient. Two noncentral H-chief factors would
cost at least sixteen. The actual quotient has at most one such factor.
The remaining factor is a natural four-space by the actual S₆ catalogue,
so coprime additivity bounds every cubic action on V_H/U_H by two.
Normality is relative to H throughout; V_H itself need not be abelian.

Both applications construct their marked actor from the nonabelian
source branch. The total L₁-factor comparison, the later
Steinberg/permutation comparisons and 13.4.1
application remain with qt-d-138-a6-endgame-source. The earlier ordinary
setup remains with qt-d-138-six-g2-source. These results do not assert
the complete 13.8.33 exclusion or strict denominators.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
Lemma 13.8.33, printed pp.966--967.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionRecognition.Component.ModelExtension A6Endgame.IntersectionBalance
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The original H_C/V_H section is centralized by O²(H). The proof
uses the actual conjugate span above the even radical, with relative
normality only inside H. -/
theorem centralizer_residual_commutator_le_span
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (l : L) (hlH : (Source.UH H V₃).conjBy (l : G) ≤ H)
    (hk : (Source.UH H V₃).conjBy (l : G) ⊓ Source.QH H = V₃.conjBy (l : G))
    (hm : (Source.starImage H ((Source.UH H V₃).conjBy (l : G))).map e.toMonoidHom = D0) :
    ⁅Source.HC H V₃, (pResidual 2 H).map H.subtype⁆ ≤ Source.VH H V := by
  let C := (Source.HC H V₃).subgroupOf H
  let Z := (Source.VH H V).subgroupOf H
  let B := ((Source.UH H V₃).conjBy (l : G)).subgroupOf H
  let J := (H.conjBy (l : G)).subgroupOf H
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = pCore 2 H := by
    ext x
    change e (QuotientGroup.mk' (pCore 2 H) x) = 1 ↔ x ∈ pCore 2 H
    rw [← map_one e, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hp : IsPGroup 2 q.ker := by rw [hker]; exact pCore_isPGroup
  have hCn : H ≤ normalizer (Source.HC H V₃ : Set G) :=
    (le_inf H.le_normalizer ((le_normalizer_conjugateSpanBy V₃ H).trans
      (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  let : C.Normal := normal_subgroupOf_of_le_normalizer hCn
  let : Z.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy V H)
  have hZC : Z ≤ C := subgroupOf_mono H
    (Section07.VH_centralizes_UH (localNaturalSetup d) h
      (show IsMulCommutative (Source.UH H V₃) from inferInstance))
  have hCQ : Source.HC H V₃ ≤ Source.QH H := by
    apply le_trans _ h.kernel_UH_eq_QH.le
    intro x hx
    exact (h.mem_kernel_iff h.UH_le_H).mpr ⟨hx.1, fun u hu => by
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hx.2 u hu)]
      exact V₁.one_mem⟩
  have hCker : C ≤ q.ker := by
    rw [hker]
    intro x hx
    obtain ⟨y, hy, he⟩ := hCQ hx
    exact (show y = x from Subtype.ext he) ▸ hy
  have hB : B.map q = D0 := by
    change B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))) = _
    rw [← map_map]
    exact hm
  have hc : ⁅C ⊓ J, B⁆ ≤ Z := by
    change ⁅(Source.HC H V₃ ⊓ H.conjBy (l : G)).subgroupOf H,
      ((Source.UH H V₃).conjBy (l : G)).subgroupOf H⁆ ≤ (Source.VH H V).subgroupOf H
    rw [← Theory.GroupTheory.SubgroupTransport.subgroupOf_commutator _ _
      (show Source.HC H V₃ ⊓ H.conjBy (l : G) ≤ H from inf_le_left.trans inf_le_left) hlH]
    apply subgroupOf_mono H
    rw [commutator_comm]
    exact (conjugate_seed_commutator_bounds d h l hlH hk).2.1
  have hi : J.relIndex C ≤ 2 := by
    rw [relIndex_subgroupOf (show Source.HC H V₃ ≤ H from inf_le_left)]
    have hh := (centralizer_conjugate_indices d h l).1
    rwa [inf_relIndex_left] at hh
  have ha : orderOf (swap01 * swap45) = 2 := orderOf_eq_prime (by decide) (by decide)
  have heven : swap01 * swap45 ∈ alternatingGroup (Fin 6) := swap01_swap45_mem_D0.2
  have haB : swap01 * swap45 ∈ B.map q := hB.symm ▸ swap01_swap45_mem_D0
  have hh := NoncentralChiefRefinement.SymmetricSixBudget.residual_commutator_le_of_index_two
    q hq hp C Z hZC hCker B (swap01 * swap45) ha heven haB J hc hi
  have hg := map_mono (f := H.subtype) hh
  rw [map_commutator, map_subgroupOf_eq_of_le (show Source.HC H V₃ ≤ H from inf_le_left),
    map_subgroupOf_eq_of_le (show Source.VH H V ≤ H from h.VH_le_H)] at hg
  exact hg

/-- In the actual contrary nonabelian branch, the previously constructed
marked conjugator discharges all actor hypotheses of centralization. -/
theorem nonabelian_centralizer_residual_commutator
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : CompatibleModel H V₃ V₁ a e)
    (hn : ¬ IsMulCommutative (Source.UL L H V₃)) :
    ⁅Source.HC H V₃, (pResidual 2 H).map H.subtype⁆ ≤ Source.VH H V := by
  obtain ⟨l, _, _, hlH, hk, _, _, hm⟩ :=
    exists_nonabelian_marked_kernel d h c hH hDH hDg hcentral a e model hn
  exact centralizer_residual_commutator_le_span d h e l hlH hk hm


/-- The literal V_H/U_H section has at most one noncentral H-chief
factor in the contrary nonabelian branch; any such factor has order
sixteen. Every three-subgroup has cubic movement length at most two.
Normality and the index bound come from the original source subgroups. -/
theorem nonabelian_span_quotient_chief_structure
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : CompatibleModel H V₃ V₁ a e)
    (hn : ¬ IsMulCommutative (Source.UL L H V₃)) :
    letI : ((Source.UH H V₃).subgroupOf H).Normal :=
      normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy V₃ H)
    letI : ((Source.VH H V).subgroupOf H).Normal :=
      normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy V H)
    let π := QuotientGroup.mk' ((Source.UH H V₃).subgroupOf H)
    letI : (((Source.VH H V).subgroupOf H).map π).Normal :=
      Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
    ∀ s : NoncentralChiefRefinement.SeriesOn (((Source.VH H V).subgroupOf H).map π),
      s.noncentralCount ≤ 1 ∧
      (∀ i, ¬ s.Central i → Nat.card (s.Factor i) = 16) ∧
      ∀ B : Subgroup (H ⧸ (Source.UH H V₃).subgroupOf H), IsPGroup 3 B →
        conjugationCubicLength B (((Source.VH H V).subgroupOf H).map π) ≤ 2 := by
  obtain ⟨l, _, _, hlH, hk, _, _, hm⟩ :=
    exists_nonabelian_marked_kernel d h c hH hDH hDg hcentral a e model hn
  let A := (Source.VH H V).subgroupOf H
  let Z := (Source.UH H V₃).subgroupOf H
  let X := (Source.VH H V ⊓ H.conjBy (l : G)).subgroupOf H
  let W := V.subgroupOf H
  let B := ((Source.UH H V₃).conjBy (l : G)).subgroupOf H
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = pCore 2 H := by
    ext x
    change e (QuotientGroup.mk' (pCore 2 H) x) = 1 ↔ x ∈ pCore 2 H
    rw [← map_one e, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hp : IsPGroup 2 q.ker := by rw [hker]; exact pCore_isPGroup
  let : A.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy V H)
  let : Z.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy V₃ H)
  have hZA : Z ≤ A := subgroupOf_mono H (conjugateSpanBy_mono d.seed_le le_rfl)
  have hAker : A ≤ q.ker := by
    rw [hker]
    intro x hx
    have hvq := Section07.VH_le_core (localNaturalSetup d) h
      (show IsMulCommutative (Source.UH H V₃) from inferInstance)
    obtain ⟨y, hy, he⟩ := hvq hx
    exact (show y = x from Subtype.ext he) ▸ hy
  have hXA : X ≤ A := subgroupOf_mono H inf_le_left
  have hAabelian : ⁅A,A⁆ ≤ Z := by
    change ⁅(Source.VH H V).subgroupOf H,(Source.VH H V).subgroupOf H⁆ ≤ _
    rw [← Theory.GroupTheory.SubgroupTransport.subgroupOf_commutator _ _
      (show Source.VH H V ≤ H from h.VH_le_H) (show Source.VH H V ≤ H from h.VH_le_H)]
    exact subgroupOf_mono H ((Section07.commutator_VH_le_point (localNaturalSetup d) h
      (show IsMulCommutative (Source.UH H V₃) from inferInstance)).trans
        ((d.line_le_plane.trans d.plane_le_seed).trans (le_conjugateSpanBy V₃ H)))
  have hB : B.map q = D0 := by
    change B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))) = _
    rw [← map_map]
    exact hm
  obtain ⟨y, hy, hqy⟩ := show swap01 * swap45 ∈ B.map q from hB.symm ▸ swap01_swap45_mem_D0
  have ha : orderOf (q y) = 2 := by
    rw [hqy]
    exact orderOf_eq_prime (by decide) (by decide)
  have heven : q y ∈ alternatingGroup (Fin 6) := hqy.symm ▸ swap01_swap45_mem_D0.2
  have hc : ⁅X,zpowers y⁆ ≤ W := by
    apply le_trans (commutator_mono le_rfl (zpowers_le.mpr hy))
    change ⁅(Source.VH H V ⊓ H.conjBy (l : G)).subgroupOf H,
      ((Source.UH H V₃).conjBy (l : G)).subgroupOf H⁆ ≤ V.subgroupOf H
    rw [← Theory.GroupTheory.SubgroupTransport.subgroupOf_commutator _ _
      (show Source.VH H V ⊓ H.conjBy (l : G) ≤ H from inf_le_left.trans h.VH_le_H) hlH]
    apply subgroupOf_mono H
    rw [commutator_comm]
    exact (conjugate_seed_commutator_bounds d h l hlH hk).2.2
  have hW : Z.relIndex W ≤ 2 := by
    have hi := relIndex_sup_left W Z
    rw [← subgroupOf_sup (show Source.UH H V₃ ≤ H from h.UH_le_H)
      (show V ≤ H from h.V_le_H),
      relIndex_subgroupOf (sup_le (show Source.UH H V₃ ≤ H from h.UH_le_H)
        (show V ≤ H from h.V_le_H))] at hi
    rw [← hi, case_one_quotient_line d h c hDH hDg]
  have hindex : X.relIndex A ≤ 2 := by
    rw [relIndex_subgroupOf (show Source.VH H V ≤ H from h.VH_le_H)]
    exact (centralizer_conjugate_indices d h l).2
  exact NoncentralChiefRefinement.SymmetricSixBudget.quotient_chief_structure_of_index_two
    q hq hp A Z X W hZA hAker hXA hAabelian y ha heven hc hW hindex

/-- The original count-only interface follows from the constituent and
cubic-action calculation on the same literal quotient. -/
theorem nonabelian_span_quotient_chief_bound
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : CompatibleModel H V₃ V₁ a e)
    (hn : ¬ IsMulCommutative (Source.UL L H V₃)) :
    letI : ((Source.UH H V₃).subgroupOf H).Normal :=
      normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy V₃ H)
    letI : ((Source.VH H V).subgroupOf H).Normal :=
      normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy V H)
    let π := QuotientGroup.mk' ((Source.UH H V₃).subgroupOf H)
    letI : (((Source.VH H V).subgroupOf H).map π).Normal :=
      Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
    ∀ s : NoncentralChiefRefinement.SeriesOn (((Source.VH H V).subgroupOf H).map π),
      s.noncentralCount ≤ 1 := by
  exact fun s => (nonabelian_span_quotient_chief_structure
    d h c hH hDH hDg hcentral a e model hn s).1
end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
