module

public import CFSG.Quasithin.Chapter16.Section01To02.CoverAndSylowElimination.SylowContainment
public import Theory.GroupTheory.TightlyEmbedded.CommutingProduct
public import Theory.GroupTheory.PerfectSylowTwo

/-!
# The two conjugate Sylow subgroups of Lemma 16.2.12

I.7.6 and the Sylow-centralizing innerness property of 16.1.6 put the
component of a distinct Sylow conjugate in H. The two residual identities
used in 16.2.9 then put it in L₀. A centerless quasisimple tightly embedded
subgroup of the commuting product L Lᵘ lies in a factor. Equality of Sylow
orders gives the required two alternatives. The final set equality also
supplies the conjugators 1 and u for the reverse inclusion.

This replaces the source's brief second-component containment step with
the general commuting-product lemma. The strict size bound |T_L| > 2 is
proved from perfection and even order by Burnside transfer. The residual
identities and the intrinsic 16.1.6 property remain explicit earlier inputs;
no elimination conclusion, Sylow size, or final normality is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemmas 16.2.9 and 16.2.12, printed pp.1175–1176.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16 CFSG.Quasithin.ChapterI.Section06To08
namespace CFSG.Quasithin.Chapter16.CoverAndSylowElimination
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z u : G} {L : Subgroup G}

omit [Finite G] in
/-- Triviality of the component center makes the two commuting factors disjoint. -/
theorem EarlierConclusions.factors_disjoint (h : EarlierConclusions T z u L)
    (hc : center L = ⊥) : Disjoint L (conjSubgroup L u) :=
  disjoint_iff.mpr (le_bot_iff.mp (h.intersection_le_center.trans_eq (componentCenter_eq_bot hc)))

omit [Finite G] in
/-- The actual product projection transfers p′-perfectness of L₀ to L. -/
theorem EarlierConclusions.component_residual_eq_top (h : EarlierConclusions T z u L)
    (hc : center L = ⊥) (p : ℕ)
    (hself : primeToResidual p (localComponentClosure z L) = ⊤) :
    primeToResidual p L = ⊤ := by
  obtain ⟨e, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting L (conjSubgroup L u)
    (h.factors_disjoint hc) h.commuting
  let e₀ : L × conjSubgroup L u ≃* localComponentClosure z L :=
    e.trans (MulEquiv.subgroupCongr h.closure_eq.symm)
  let f : localComponentClosure z L →* L := (MonoidHom.fst L (conjSubgroup L u)).comp e₀.symm.toMonoidHom
  have hf : Function.Surjective f := fun x => ⟨e₀ (x, 1), by simp [f]⟩
  have hh := map_primeToResidual_le (p := p) f hf
  rw [hself, map_top_of_surjective _ hf] at hh
  exact top_unique hh

/-- The source Sylow size comparison follows from perfection and even order. -/
theorem EarlierConclusions.component_sylow_card_gt_two (h : EarlierConclusions T z u L)
    (htight : IsTightlyEmbedded L) : 2 < Nat.card (componentSylow T L) := by
  let := h.localSetup.component.quasisimple
  obtain ⟨P, hP⟩ := h.localSetup.exists_component_sylow
  have hmap : (P : Subgroup L).map L.subtype = componentSylow T L := by
    rw [hP]
    ext x
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, x.property⟩
    · rintro ⟨hxT, hxL⟩
      exact ⟨⟨x, hxL⟩, hxT, rfl⟩
  have hh := perfect_sylow_two_card_gt_two P htight.1
  rwa [← Subgroup.card_map_of_injective L.subtype_injective, hmap] at hh

/-- The forward containment in 16.2.12, with exactly the two actual Sylow intersections. -/
theorem conjugate_sylow_dichotomy_of_inputs (h : EarlierConclusions T z u L)
    (htight : IsTightlyEmbedded L) (hc : center L = ⊥)
    (p : ℕ) (hself : primeToResidual p (localComponentClosure z L) = ⊤)
    (hres : (primeToResidual p (localComponentNormalizer z L)).map
      (localComponentNormalizer z L).subtype = localComponentClosure z L)
    (hinner : SylowCentralizingInner L)
    {g : G} (hgT : conjSubgroup (componentSylow T L) g ≤ T) :
    conjSubgroup (componentSylow T L) g = componentSylow T L ∨
      conjSubgroup (componentSylow T L) g = componentSylow T (conjSubgroup L u) := by
  by_cases he : conjSubgroup (componentSylow T L) g = componentSylow T L
  · exact Or.inl he
  let M := conjSubgroup L g
  let e : L ≃* M := (MulAut.conj g).subgroupMap L
  have hML₀ := third_component_le_closure h htight hc (h.component_sylow_card_gt_two htight)
    p (h.component_residual_eq_top hc p hself) hres hgT he (hinner.of_mulEquiv e)
  rw [h.closure_eq] at hML₀
  let : IsQuasisimple L := h.localSetup.component.quasisimple
  let : IsQuasisimple M := IsQuasisimple.of_mulEquiv e
  have hMc : center M = ⊥ := by
    apply (center M).eq_bot_iff_card.mpr
    rw [← Nat.card_congr (centerCongr e).toEquiv, hc]
    simp
  have hMt : IsTightlyEmbedded M := htight.map_equiv (MulAut.conj g)
  have hSM : conjSubgroup (componentSylow T L) g ≤ M := conjSubgroup_mono inf_le_right g
  rcases hMt.le_factor_of_commuting_product hMc h.commuting (h.factors_disjoint hc) hML₀ with hA | hB
  · exact Or.inl (eq_of_le_of_card_ge (le_inf hgT (hSM.trans hA))
      (by rw [card_conjSubgroup]))
  · exact Or.inr (eq_of_le_of_card_ge (le_inf hgT (hSM.trans hB))
      (by rw [← h.swapped_sylow, card_conjSubgroup, card_conjSubgroup]))

/-- Conditional 16.2.12, including both inclusions of the conjugacy-class equality. -/
theorem lemma_16_2_12_of_inputs (h : EarlierConclusions T z u L)
    (htight : IsTightlyEmbedded L) (hc : center L = ⊥)
    (p : ℕ) (hself : primeToResidual p (localComponentClosure z L) = ⊤)
    (hres : (primeToResidual p (localComponentNormalizer z L)).map
      (localComponentNormalizer z L).subtype = localComponentClosure z L)
    (hinner : SylowCentralizingInner L) :
    {S : Subgroup G | (∃ g : G, conjSubgroup (componentSylow T L) g = S) ∧ S ≤ T} =
      {componentSylow T L, componentSylow T (conjSubgroup L u)} := by
  ext S
  constructor
  · rintro ⟨⟨g, rfl⟩, hg⟩
    exact conjugate_sylow_dichotomy_of_inputs h htight hc p hself hres hinner hg
  · intro hS
    rcases hS with hS | hS
    · subst S
      exact ⟨⟨1, conjSubgroup_one _⟩, inf_le_left⟩
    · have hS' : S = componentSylow T (conjSubgroup L u) := hS
      subst S
      exact ⟨⟨u, h.swapped_sylow⟩, inf_le_left⟩

end CFSG.Quasithin.Chapter16.CoverAndSylowElimination
