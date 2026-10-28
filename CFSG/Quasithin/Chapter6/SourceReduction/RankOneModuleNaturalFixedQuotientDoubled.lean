module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedWeakClosureRanksGlobal
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.SourceKnownSimple
public import Theory.GroupTheory.TINormalizerControl

/-!
# The hyperplane contradiction for two natural summands

Suppose V is the join of two natural L-modules and L is normal in M.
Each summand is TI under M by irreducibility. If the first summand satisfies
the original E.6.1 hypotheses, E.6.13 and natural hyperplane transitivity
give its global rank greater than one. A hyperplane of V intersects that
summand in corank at most one, so its centralizer lies in M. Its intersection
with the second summand is nontrivial, and TI then forces the centralizer
to normalize both summands and their join. Thus V also has global rank
greater than one.

This is the terminal contradiction in the doubled-natural case of 6.1.4.
The original Hypothesis 6.1.1 supplies E.6.1 for every Sylow-invariant
natural sublayer: natural faithfulness detects the local two-core, and
uniqueness over LT supplies the maximality condition. Construction of a
Sylow-invariant summand and the preceding rank-one conclusion remain
separate source steps. No disjointness or invariance of the second summand
under the Sylow subgroup is assumed.

Source: Aschbacher–Smith, 6.1.4, printed pp.664–665 of refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition

variable {G : Type*} [Group G] [Finite G]

/-- Any natural module for a normal subgroup is TI in the overgroup. -/
theorem natural_subgroup_ti {L M B : Subgroup G} {n : ℕ}
    (hML : M ≤ normalizer (L : Set G))
    (hnatural : IsNaturalModule L B n) {g : G} (hg : g ∈ M) :
    B ⊓ B.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      B.map (MulAut.conj g).toMonoidHom = B := by
  have hnL : L ≤ normalizer (B : Set G) := by
    obtain ⟨F, _, _, _, _, hm⟩ := hnatural
    exact hm.normalizes
  have hgL : L.map (MulAut.conj g).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp (hML hg)
  have hnLg : L ≤ normalizer (B.map (MulAut.conj g).toMonoidHom : Set G) := by
    have hm := map_mono (f := (MulAut.conj g).toMonoidHom) hnL
    rwa [hgL, map_equiv_normalizer_eq] at hm
  rcases hnatural.invariant_subgroup
      (B ⊓ B.map (MulAut.conj g).toMonoidHom) inf_le_left
      ((le_inf hnL hnLg).trans inf_normalizer_le_normalizer_inf) with he | he
  · exact Or.inl he
  · right
    symm
    apply eq_of_le_of_card_ge (he.symm.le.trans inf_le_right)
    rw [card_map_of_injective (MulAut.conj g).injective]

private theorem corank_inf_le {V B W : Subgroup G} (hBV : B ≤ V) :
    ChapterE.subgroupCorank B (W ⊓ B) ≤ ChapterE.subgroupCorank V W := by
  unfold ChapterE.subgroupCorank
  rw [inf_relIndex_right]
  exact Nat.log_mono_right (relIndex_le_of_le_right hBV index_ne_zero_of_finite)

/-- A natural summand satisfying E.6.1 excludes an escaping hyperplane of
the join of two natural summands. -/
theorem natural_pair_one_lt_globalR
    {T : Sylow 2 G} {L M V B₁ B₂ : Subgroup G} {n : ℕ}
    (hn : 1 < n) (hLM : L ≤ M) (hML : M ≤ normalizer (L : Set G))
    (h₁ : IsNaturalModule L B₁ n) (h₂ : IsNaturalModule L B₂ n)
    (hV : V = B₁ ⊔ B₂)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M B₁) :
    1 < ChapterE.globalR V := by
  let := hE.elementary
  have hr₁ : 1 < ChapterE.globalR B₁ :=
    natural_one_lt_globalR hn h₁ (hE.normalizer_le.trans hML) hLM hE
  apply lt_of_le_of_ne (ChapterE.one_le_globalR V)
  intro he
  obtain ⟨W, hWV, hescape, hcor⟩ := ChapterE.Section06.globalR_attained
    (by rw [← he]; exact ENat.one_ne_top)
  have hW : ChapterE.subgroupCorank V W = 1 := by
    exact_mod_cast hcor.trans he.symm
  have hB₁V : B₁ ≤ V := hV.symm ▸ le_sup_left
  have hB₂V : B₂ ≤ V := hV.symm ▸ le_sup_right
  have hcor₁ : ChapterE.subgroupCorank B₁ (W ⊓ B₁) ≤ 1 :=
    (corank_inf_le hB₁V).trans_eq hW
  have hC₁ : centralizer (W : Set G) ≤ normalizer (B₁ : Set G) :=
    (centralizer_le inf_le_left).trans
      (ChapterE.centralizer_le_normalizer_of_corank_lt_globalR inf_le_right
        (lt_of_le_of_lt (by exact_mod_cast hcor₁) hr₁))
  have hnonzero : W ⊓ B₂ ≠ ⊥ := by
    intro hz
    have hc := (corank_inf_le hB₂V).trans_eq hW
    rw [hz, ChapterE.subgroupCorank, relIndex_bot_left, h₂.card,
      Nat.log_pow Nat.one_lt_two] at hc
    omega
  have hC₂ : centralizer (W : Set G) ≤ normalizer (B₂ : Set G) :=
    (le_inf (hC₁.trans hE.normalizer_le) (centralizer_le inf_le_left)).trans
      (inf_centralizer_le_normalizer_of_trivial_intersections
        (fun g hg => natural_subgroup_ti hML h₂ hg) hnonzero inf_le_right)
  apply hescape
  rw [hV]
  exact (le_inf hC₁ hC₂).trans
    (normalizer_inf_normalizer_le_normalizer_sup B₁ B₂)

/-- The original source setup supplies E.6.1 for every Sylow-invariant
natural sublayer, without an A₅ exclusion on that individual summand. -/
theorem natural_sublayer_hypothesisE61
    {T : Sylow 2 G} {L M V B : Subgroup G} {n : ℕ}
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hB : B ≤ layer L V) (hnatural : IsNaturalModule L B n)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G)) :
    ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M B := by
  have hBL : B ≤ L := hB.trans h.layer_le_L
  have hBT : B ≤ (T : Subgroup G) := hB.trans h.layer_le_T
  have hBe : IsElementaryAbelian 2 B := by
    let := h.layer_elementary
    exact IsElementaryAbelian.of_le hB
  have hBne : B ≠ ⊥ := by
    intro he
    have hc := hnatural.card
    rw [he] at hc
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2)
      (show 2 ≤ n * 2 by have := h.n_gt_one; omega)
    norm_num at hc hp
    omega
  have hnL : L ≤ normalizer (B : Set G) := by
    obtain ⟨F, _, _, _, _, hm⟩ := hnatural
    exact hm.normalizes
  have hCL : L ⊓ centralizer (B : Set G) = L.pCoreIn 2 := by
    obtain ⟨F, _, _, _, _, hm⟩ := hnatural
    exact hm.centralizer_eq_core (Representation.specialLinearNatural_injective 2)
  have hcore : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ centralizer (B : Set G) :=
    (local_core_centralizes_layer h).trans (centralizer_le hB)
  have hlocal : (L ⊔ (T : Subgroup G)) ⊓ centralizer (B : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    Theory.GroupTheory.ambient_centralizer_eq_core_of_normal_supplement L B T
      h.sylow_normalizes_L (hBL.trans le_sup_left) (sup_le hnL hTB)
      T.isPGroup' hCL hcore
  have hQ : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    obtain ⟨S, hS⟩ := h.local_mem.1.prop.2.1
    exact (pCoreIn_le_sylow _ S).trans_eq hS
  have hCT : ChapterE.Section06.sylowCentralizer (T : Subgroup G) B =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    le_antisymm ((inf_le_inf_right _ le_sup_right).trans_eq hlocal) (le_inf hQ hcore)
  have hstar : L ∈ Chapter1.LStar G (T : Subgroup G) := by
    refine ⟨h.local_mem.1.prop, ?_⟩
    intro K hK hLK
    exact le_antisymm (h.local_mem.1.2 hK hLK) hLK
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.simpleQTKE T hstar
  have horbit : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L T L le_rfl
      h.sylow_normalizes_L) (le_componentOrbit L T)
  have hML : M ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal
  refine ⟨h.simpleQTKE, h.maximal, h.sylow_le, hBne, hBe, hBT,
    (normal_subgroupOf_iff_le_normalizer hBT).mpr hTB,
    fun g hg => natural_subgroup_ti hML hnatural hg, ?_⟩
  intro N hN hle
  have hLT : L ⊔ (T : Subgroup G) ≤ N := by
    apply le_trans ?_ hle
    refine le_inf (le_inf (sup_le h.L_le h.sylow_le) (sup_le hnL hTB)) ?_
    rw [hCT]
    exact (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have h₁ := hu.normalizer_unique N hN
  have h₂ := hu.normalizer_unique M h.maximal
  rw [horbit] at h₁ h₂
  exact (h₁ hLT).trans (h₂ (sup_le h.L_le h.sylow_le)).symm

/-- The doubled-natural terminal rank bound on the literal original moved
layer. Only the natural summands and first-summand Sylow invariance remain. -/
theorem original_natural_pair_one_lt_globalR
    {T : Sylow 2 G} {L M V B₁ B₂ : Subgroup G} {n : ℕ}
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (h₁ : IsNaturalModule L B₁ n) (h₂ : IsNaturalModule L B₂ n)
    (hjoin : layer L V = B₁ ⊔ B₂)
    (hTB₁ : (T : Subgroup G) ≤ normalizer (B₁ : Set G)) :
    1 < ChapterE.globalR (layer L V) :=
  natural_pair_one_lt_globalR h.n_gt_one h.L_le
    ((normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal) h₁ h₂ hjoin
    (natural_sublayer_hypothesisE61 h (hjoin.symm ▸ le_sup_left) h₁ hTB₁)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
