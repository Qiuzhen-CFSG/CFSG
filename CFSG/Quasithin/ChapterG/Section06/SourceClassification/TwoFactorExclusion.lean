module

public import Theory.GroupTheory.NormalClosureProductCubic
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.RankOneFactorSelection
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.FFExtraction

/-!
# Excluding the literal two-factor B.5.6 branch in the original G.6 actor

The original rank-one element lies in one of the actual B.5.6 direct factors.
Their intrinsic group structure makes them permuted by every ambient
conjugation. Transporting through the normal closure's literal inclusion gives
commuting, disjoint factors whose join is that normal closure. The same
Sylow-normalized inverted cubic contradicts this product configuration.

Every factor-model and permutation premise is derived from the complete
source clause. No G.6 recognition or module-splitting conclusion is assumed.
Source: Aschbacher–Smith, G.6.4, pp.345–346, and C.5.12, p.163.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section06
open Subgroup Theory.GroupTheory
open ChapterB.SourceInduction
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {κ : GroupClass.{u}} {ρ : Representation (ZMod 2) G V} {a : G}
  {Cover : Type u} [Group Cover] {q : Cover →* G}

private theorem cubic_exclusion_of_marked_first
    (h : Hypotheses κ ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (d : SourceTwoFactorCase (ρ.comp (normalClosure ({a} : Set G)).subtype))
    (ha : (⟨a, subset_normalClosure (Set.mem_singleton a)⟩ : normalClosure ({a} : Set G)) ∈ d.first)
    (S : Sylow 2 G) (c : G) (hcne : c ≠ 1) (hi : a * c = c ^ 2 * a)
    (hn : (S : Subgroup G) ≤ normalizer (zpowers c : Set G)) : False := by
  let := h.finite_group
  let K := normalClosure ({a} : Set G)
  let A := d.first.map K.subtype
  let B := d.second.map K.subtype
  have haA : a ∈ A := mem_map_of_mem K.subtype ha
  have hjoin : A ⊔ B = K := by
    change d.first.map K.subtype ⊔ d.second.map K.subtype = K
    rw [← Subgroup.map_sup, d.product.sup_eq_top, ← MonoidHom.range_eq_map, range_subtype]
  have hcomm : ⁅A,B⁆ = ⊥ := by
    change ⁅d.first.map K.subtype,d.second.map K.subtype⁆ = ⊥
    rw [← Subgroup.map_commutator, d.product.commutator_eq_bot, Subgroup.map_bot]
  have hdis : Disjoint A B := Subgroup.disjoint_map K.subtype_injective d.product.disjoint
  have hB : B ≠ ⊥ := by
    intro he
    have hb : d.second = ⊥ := Subgroup.map_injective (f := K.subtype) K.subtype_injective
      (by simpa only [Subgroup.map_bot] using he)
    exact (Subgroup.nontrivial_iff_ne_bot d.second).mp d.secondCase.nontrivial hb
  have hperm (g : G) :
      (A.map (MulAut.conj g).toMonoidHom = A ∧ B.map (MulAut.conj g).toMonoidHom = B) ∨
      (A.map (MulAut.conj g).toMonoidHom = B ∧ B.map (MulAut.conj g).toMonoidHom = A) := by
    have hh := d.automorphism_permutation (h.normalClosure_ffHypothesis ht).twoCore
      (MulAut.conjNormal g)
    have hm (X : Subgroup K) :
        (X.map (MulAut.conjNormal g).toMonoidHom).map K.subtype =
          (X.map K.subtype).map (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
    rcases hh with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · exact Or.inl ⟨(hm d.first).symm.trans (congrArg (fun X : Subgroup K => X.map K.subtype) h₁),
        (hm d.second).symm.trans (congrArg (fun X : Subgroup K => X.map K.subtype) h₂)⟩
    · exact Or.inr ⟨(hm d.first).symm.trans (congrArg (fun X : Subgroup K => X.map K.subtype) h₁),
        (hm d.second).symm.trans (congrArg (fun X : Subgroup K => X.map K.subtype) h₂)⟩
  exact not_sylow_normalizes_cubic_of_normalClosure_product A B a c haA hjoin hcomm hdis hB hperm
    S hcne hi hn

theorem Hypotheses.not_two_factors_of_normalized_inverted_cubic
    (h : Hypotheses κ ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (d : SourceTwoFactorCase (ρ.comp (normalClosure ({a} : Set G)).subtype))
    (S : Sylow 2 G) (c : G) (hcne : c ≠ 1) (hi : a * c = c ^ 2 * a)
    (hn : (S : Subgroup G) ≤ normalizer (zpowers c : Set G)) : False := by
  let := h.finite_module
  let t : normalClosure ({a} : Set G) := ⟨a, subset_normalClosure (Set.mem_singleton a)⟩
  rcases d.rank_one_mem_factor t ht.le with ha | hb
  · exact cubic_exclusion_of_marked_first h ht d ha S c hcne hi hn
  · let d' : SourceTwoFactorCase (ρ.comp (normalClosure ({a} : Set G)).subtype) :=
      { first := d.second
        second := d.first
        product := d.product.swap
        firstSpace := d.secondSpace
        secondSpace := d.firstSpace
        decomposition := d.decomposition.symm
        firstCase := d.secondCase
        secondCase := d.firstCase }
    exact cubic_exclusion_of_marked_first h ht d' hb S c hcne hi hn
end CFSG.Quasithin.ChapterG.Section06
