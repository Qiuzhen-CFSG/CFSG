module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.Family
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.SplitFitting

/-!
# Finite ratio decomposition and the full Fitting source application

Strong induction on the order of the faithful acting group terminates the
literal D.2.16 splitting. The embeddings compose, so the resulting finite
family retains the original starred-subgroup partition, commutator supports,
independent support sum and internal direct product.

The Fitting variant applies the surjective factor projections at every split;
its terminal actions therefore retain full Fitting movement, the hypothesis
needed by D.2.17. The actual source application takes the proved Jhat and
Fitting-moved reduction explicitly. A cubic bound of two supplies nontriviality
from the original starred family.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, D.2.16–17,
printed pp.187–188 (1 March 2004 manuscript); applied in original 15.1.2 and
14.6.12.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.RatioDecomposition
universe u v
variable {G : Type u} {V : Type v} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

@[expose] def FactorData.embedding {H : Subgroup G} {U : Submodule (ZMod 2) V}
    (d : FactorData ρ H U) : Embedding d.representation ρ where
  groupMap := H.subtype
  spaceMap := U.subtype
  group_injective := H.subtype_injective
  space_injective := U.subtype_injective
  equivariant := d.equivariant
  fixed_complement := by simpa only [Submodule.range_subtype,Subgroup.range_subtype] using d.fixed_complement
  ratio := d.ratio
  stars := d.stars

omit [FiniteDimensional (ZMod 2) V] in
theorem Decomposition.actor_normal (d : Decomposition ρ) (hf : Function.Injective ρ)
    (i : d.Index) : (d.factor i).actor.Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  rw [← d.group_generation]
  apply iSup_le
  intro j
  by_cases hji : j = i
  · subst j
    exact Subgroup.le_normalizer
  · apply Subgroup.le_normalizer_iff.mpr
    intro x hx y hy
    rw [(d.actors_commute hf hji hx hy).eq,mul_inv_cancel_right]
    exact hy

variable [Finite G] [Nontrivial G]
theorem exists_decomposition (hf : Function.Injective ρ)
    (hgen : Jhat ρ = ⊤) (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤) :
    Nonempty (Decomposition ρ) := by
  classical
  induction hn : Nat.card G using Nat.strong_induction_on generalizing G V with
  | h n ih =>
    by_cases hi : IsRatioIndecomposable ρ
    · exact ⟨Decomposition.singleton hf hi hgen hfull⟩
    have hh : IsRatioDecomposable ρ := not_not.mp hi
    obtain ⟨G₁,G₂,V₁,V₂,hn₁,hn₂,h⟩ := hh
    obtain ⟨d₁,d₂,hlt₁,hlt₂,hd,hg,hcomm,hcompl,hQ⟩ := split ρ hf hfull h hn₁ hn₂
    let : Nontrivial G₁ := (Subgroup.nontrivial_iff_ne_bot G₁).mpr hn₁
    let : Nontrivial G₂ := (Subgroup.nontrivial_iff_ne_bot G₂).mpr hn₂
    obtain ⟨c₁⟩ := ih (Nat.card G₁) (hn ▸ hlt₁) d₁.representation d₁.faithful
      d₁.generated d₁.full rfl
    obtain ⟨c₂⟩ := ih (Nat.card G₂) (hn ▸ hlt₂) d₂.representation d₂.faithful
      d₂.generated d₂.full rfl
    have hc₁ : V₂ ≤ fixedSpace ρ G₁ := by
      obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,hc,_⟩ := h
      exact (subspaceCommutator_eq_bot_iff ρ V₂ G₁).mp hc
    have hc₂ : V₁ ≤ fixedSpace ρ G₂ := by
      obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hc⟩ := h
      exact (subspaceCommutator_eq_bot_iff ρ V₁ G₂).mp hc
    refine ⟨Decomposition.combine c₁ c₂ (d₁.embedding ρ) (d₂.embedding ρ)
      (by simpa only [FactorData.embedding,Subgroup.range_subtype] using hg)
      (by simpa only [FactorData.embedding,Submodule.range_subtype] using hcompl)
      (by simpa only [FactorData.embedding,Submodule.range_subtype,Subgroup.range_subtype] using hc₂)
      (by simpa only [FactorData.embedding,Submodule.range_subtype,Subgroup.range_subtype] using hc₁) ?_⟩
    intro A hA
    have hmem := hQ ▸ hA
    exact hmem

theorem exists_fitting_decomposition (hf : Function.Injective ρ)
    (hgen : Jhat ρ = ⊤) (hFfull : subspaceCommutator ρ ⊤ (fittingSubgroup G) = ⊤) :
    ∃ d : Decomposition ρ, d.FittingFull := by
  classical
  induction hn : Nat.card G using Nat.strong_induction_on generalizing G V with
  | h n ih =>
    have hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤ := by
      apply top_unique
      calc
        ⊤ = subspaceCommutator ρ ⊤ (fittingSubgroup G) := hFfull.symm
        _ ≤ subspaceCommutator ρ ⊤ ⊤ := ?_
      apply Submodule.span_mono
      rintro _ ⟨g,hg,v,hv,rfl⟩
      exact ⟨g,Subgroup.mem_top g,v,hv,rfl⟩
    by_cases hi : IsRatioIndecomposable ρ
    · exact ⟨Decomposition.singleton hf hi hgen hfull,
        Decomposition.singleton_fitting_full hf hi hgen hfull hFfull⟩
    have hh : IsRatioDecomposable ρ := not_not.mp hi
    obtain ⟨G₁,G₂,V₁,V₂,hn₁,hn₂,h⟩ := hh
    obtain ⟨d₁,d₂,hlt₁,hlt₂,hd,hg,hcomm,hcompl,hQ⟩ := split ρ hf hfull h hn₁ hn₂
    let : Nontrivial G₁ := (Subgroup.nontrivial_iff_ne_bot G₁).mpr hn₁
    let : Nontrivial G₂ := (Subgroup.nontrivial_iff_ne_bot G₂).mpr hn₂
    obtain ⟨hf₁,hf₂⟩ := fitting_full_of_split ρ d₁ d₂ h hd hg hcomm hFfull
    obtain ⟨c₁,hcfit₁⟩ := ih (Nat.card G₁) (hn ▸ hlt₁) d₁.representation d₁.faithful
      d₁.generated hf₁ rfl
    obtain ⟨c₂,hcfit₂⟩ := ih (Nat.card G₂) (hn ▸ hlt₂) d₂.representation d₂.faithful
      d₂.generated hf₂ rfl
    have hc₁ : V₂ ≤ fixedSpace ρ G₁ := by
      obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,hc,_⟩ := h
      exact (subspaceCommutator_eq_bot_iff ρ V₂ G₁).mp hc
    have hc₂ : V₁ ≤ fixedSpace ρ G₂ := by
      obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hc⟩ := h
      exact (subspaceCommutator_eq_bot_iff ρ V₁ G₂).mp hc
    have hgroup : (d₁.embedding ρ).groupMap.range ⊔ (d₂.embedding ρ).groupMap.range = ⊤ := by
      simpa only [FactorData.embedding,Subgroup.range_subtype] using hg
    have hspace : IsCompl (d₁.embedding ρ).spaceMap.range (d₂.embedding ρ).spaceMap.range := by
      simpa only [FactorData.embedding,Submodule.range_subtype] using hcompl
    have hcross₁ : (d₁.embedding ρ).spaceMap.range ≤ fixedSpace ρ (d₂.embedding ρ).groupMap.range := by
      simpa only [FactorData.embedding,Submodule.range_subtype,Subgroup.range_subtype] using hc₂
    have hcross₂ : (d₂.embedding ρ).spaceMap.range ≤ fixedSpace ρ (d₁.embedding ρ).groupMap.range := by
      simpa only [FactorData.embedding,Submodule.range_subtype,Subgroup.range_subtype] using hc₁
    have hstars : ∀ A ∈ QhatStar ρ,
        (∃ B ∈ QhatStar d₁.representation, B.map (d₁.embedding ρ).groupMap = A) ∨
        (∃ B ∈ QhatStar d₂.representation, B.map (d₂.embedding ρ).groupMap = A) := by
      intro A hA
      have hmem := hQ ▸ hA
      exact hmem
    refine ⟨Decomposition.combine c₁ c₂ (d₁.embedding ρ) (d₂.embedding ρ)
      hgroup hspace hcross₁ hcross₂ hstars,?_⟩
    exact Decomposition.combine_fitting_full c₁ c₂ (d₁.embedding ρ) (d₂.embedding ρ)
      hgroup hspace hcross₁ hcross₂ hstars hcfit₁ hcfit₂

omit [Nontrivial G] in
/-- The bounded-ratio source application constructs the nontriviality instance
from the original starred family. -/
theorem source_fitting_decomposition (hf : Function.Injective ρ)
    (hgen : Jhat ρ = ⊤) (hFfull : subspaceCommutator ρ ⊤ (fittingSubgroup G) = ⊤)
    (hratio : cubicRatio ρ ≤ 2) : ∃ d : Decomposition ρ, d.FittingFull := by
  obtain ⟨A,hA⟩ := (QhatStar_nonempty_iff ρ).mpr hratio
  let : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA.1.2.1.1
  let : Nontrivial G := Function.Injective.nontrivial A.subtype_injective
  exact exists_fitting_decomposition ρ hf hgen hFfull

end CFSG.Quasithin.ChapterD.RatioDecomposition
