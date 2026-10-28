module
public import CFSG.Quasithin.Chapter3.Section01.SourceCoreAction
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.TwoChiefQuotientExclusions.FiveBorel

/-!
# Whole-span core action at the actual small parabolics

The SQTK equalities force O₂(H) to move the elementary orbit span U_H.
Consequently that core is nonabelian and properly contains U_H. The
faithful chief kernels put C_H(U_H) inside O₂(H), and the nontrivial core
action makes this containment strict. Thus the action on the whole span
does not descend through the common quotient of its chief factors.

In the S₅ branch, the two natural four-dimensional factors and proper
containment give |O₂(H)| ≥ 512. The final application transports the
nontrivial action, noncommutativity and order bound to the literal
radius-one kernel of the graph with full overlap H ∩ M. It preserves
Y₁Rc and H; mixed-pair recognition remains a separate source obligation.

Source: Aschbacher--Smith 15.1.12(1--2), 15.2.8 and F.1.12,
printed pp.1089--1090,1109--1110 and262--264.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor NoncentralChiefRefinement
variable {G : Type*} [Group G] [Finite G]

/-- The actual two-core acts nontrivially on the whole original span. -/
theorem ChosenSmallSource.HStar_core_not_centralizes_span
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    ¬ pCore 2 H ≤ centralizer ((conjugateSpan H V).subgroupOf H : Set H) := by
  let := h.prepared.elementary
  let hqrc := chosenNormalizer_qrcHypotheses T h.maximal.1.2
    h.prepared.le_selected h.prepared.normalized h.prepared.seed_span hH
  have hu := source_chosenNormalizer_unique h.ambient T h.empty h.maximal
    h.centralizing h.prepared.nontrivial h.prepared.normalized h.prepared.seed_span
  obtain ⟨hq,hdual⟩ := source_chosen_equality_inputs h.ambient T h.empty h.maximal
    hH h.centralizing h.prepared.le_selected h.prepared.nontrivial
    h.prepared.normalized h.prepared.seed_span h.prepared.le_local h.prepared.quadratic_ratio
  exact hqrc.sqtk_core_not_centralizes_span h.ambient h.maximal.1.1 hu
    (h.centralizing.trans (centralizer_le h.prepared.le_local))
    h.prepared.nontrivial (h.prepared.inside_core H hH) hdual hq

/-- The original H-star two-core is nonabelian, before choosing its quotient row. -/
theorem ChosenSmallSource.HStar_core_not_commutative
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    ¬ IsMulCommutative (pCore 2 H) := by
  intro hc
  exact h.HStar_core_not_centralizes_span hH
    ((le_centralizer_iff_isMulCommutative.mpr hc).trans
      (centralizer_le (h.HStar_span_le_core hH)))

/-- The elementary orbit span is properly contained in the actual two-core. -/
theorem ChosenSmallSource.HStar_span_lt_core
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    (conjugateSpan H V).subgroupOf H < pCore 2 H := by
  let := h.prepared.elementary
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let U := (conjugateSpan H V).subgroupOf H
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
  refine lt_of_le_of_ne (h.HStar_span_le_core hH) ?_
  intro he
  exact h.HStar_core_not_commutative hH
    (he ▸ (inferInstance : IsMulCommutative U))

private theorem centralizer_le_factor_kernel
    {D : Type*} [Group D] (U : Subgroup D) [U.Normal] [IsElementaryAbelian 2 U]
    (s : SeriesOn U) (i : Fin s.series.length) :
    centralizer (U : Set D) ≤ (actionHom (s.factorRepresentation i)).ker := by
  intro g hg
  apply (actionHom_eq_one_iff (s.factorRepresentation i) g).mpr
  intro v
  obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective ((s.lower i).val.subgroupOf (s.upper i).val) v.toMul
  apply Additive.toMul.injective
  change s.action i g v.toMul = v.toMul
  rw [←hx,s.action_mk]
  congr 1
  apply Subtype.ext
  change g * (x : D) * g⁻¹ = x
  rw [←hg x (s.upper_le i x.property),mul_inv_cancel_right]

/-- The whole-span centralizer is strictly smaller than the common noncentral
chief-factor kernel. Residual uniqueness supplies the containment. -/
theorem ChosenSmallSource.HStar_span_centralizer_lt_core
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    centralizer ((conjugateSpan H V).subgroupOf H : Set H) < pCore 2 H := by
  let := h.prepared.elementary
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let U := (conjugateSpan H V).subgroupOf H
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
  obtain ⟨s⟩ := SeriesOn.exists_series U
  obtain ⟨i,j,hij,⟨hi,hki,hai⟩,hj⟩ := h.two_faithful_chief_factors hprior hH s
  exact lt_of_le_of_ne ((centralizer_le_factor_kernel U s i).trans_eq hki)
    (fun he => h.HStar_core_not_centralizes_span hH he.ge)

/-- Both natural four-dimensional chief factors contribute to the elementary
span, which is a proper subgroup of the core. Thus the core has order at
least 512 in the single S₅ branch. -/
theorem ChosenSmallSource.symmetricFive_core_card_strict
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) :
    512 ≤ Nat.card (pCore 2 H) := by
  let U := (conjugateSpan H V).subgroupOf H
  have hlt := h.HStar_span_lt_core hH
  have hindex : 2 ≤ U.relIndex (pCore 2 H) := by
    have hp : 0 < U.relIndex (pCore 2 H) := Nat.card_pos
    have hn : U.relIndex (pCore 2 H) ≠ 1 := fun hi => hlt.not_ge (relIndex_eq_one.mp hi)
    omega
  have hcard := (U.subgroupOf (pCore 2 H)).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hlt.le).toEquiv] at hcard
  change U.relIndex (pCore 2 H) * Nat.card U = _ at hcard
  have hUH : conjugateSpan H V ≤ H := by
    rw [UniqueFactor.conjugateSpan_eq]
    exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H))
  have hb : 256 ≤ Nat.card U := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hUH).toEquiv]
    exact h.symmetricFive_span_card hprior hH he
  nlinarith

open Subgroup.CosetGeometry.RankTwo in
/-- The literal quintic radius-one kernel moves the original span, is
nonabelian and has order at least 512. This is a lower bound; it does
not supply a bound on any radius-two kernel. -/
theorem SmallResidualWitness.symmetricFive_graph_core_action
    {T : Sylow 2 G} {M Mc V Y₁ H : Subgroup G} {h : ChosenSmallSource T M Mc V}
    (hw : SmallResidualWitness h Y₁) (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) :
    let F : Bool → Subgroup G := fun i => if i then H else Y₁ ⊔ (H ⊓ M)
    ¬ ballKernel F (base F true) 1 ≤ Subgroup.centralizer (conjugateSpan H V : Set G) ∧
      ¬ IsMulCommutative (ballKernel F (base F true) 1) ∧
      512 ≤ Nat.card (ballKernel F (base F true) 1) := by
  dsimp only
  rw [(hw.symmetricFive_graph_kernel hH he).1]
  have heq := equivMapOfInjective (pCore 2 H) H.subtype H.subtype_injective
  refine ⟨?_,?_,?_⟩
  · intro hc
    apply h.HStar_core_not_centralizes_span hH
    intro x hx u hu
    apply Subtype.ext
    exact hc (mem_map_of_mem H.subtype hx) u hu
  · intro hc
    let : IsMulCommutative ((pCore 2 H).map H.subtype) := hc
    apply h.HStar_core_not_commutative hH
    exact ⟨⟨fun x y => heq.injective (by rw [map_mul,map_mul,mul_comm])⟩⟩
  · change 512 ≤ Nat.card ((pCore 2 H).map H.subtype)
    rw [←Nat.card_congr heq.toEquiv]
    exact h.symmetricFive_core_card_strict hprior hH he

end CFSG.Quasithin.Chapter15.Section02
