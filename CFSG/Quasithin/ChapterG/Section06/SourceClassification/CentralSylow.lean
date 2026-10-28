module

public import Theory.GroupTheory.NormalClosurePairCentralSylow
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.EarlierSourceReduction
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.RankOneFactorSelection

/-!
# The original two-central source branch of G.6.4

Rank-one displacement puts the actual marked involution in one of the two
B.5.6 factors. Intrinsic factor permutation then shows that its centrality in
a full ambient Sylow is impossible. All group and action hypotheses come from
the actual G.6.1 input and complete B.5.6 source clause. The final theorem
removes this entire branch from the earlier-source dispatcher.

Source: Aschbacher–Smith G.6.4(4), printed p.346.
-/

public section
namespace CFSG.Quasithin.ChapterG.Section06
open Subgroup Theory.GroupTheory ChapterB.SourceInduction
open HighThreeRank.CoverCentralizer.SourceConstruction
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {κ : GroupClass.{u}} {ρ : Representation (ZMod 2) G V} {a : G}
  {Cover : Type u} [Group Cover] {q : Cover →* G}

private theorem central_exclusion_of_marked_first
    (h : Hypotheses κ ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (d : SourceTwoFactorCase (ρ.comp (normalClosure ({a} : Set G)).subtype))
    (ha : (⟨a, subset_normalClosure (Set.mem_singleton a)⟩ : normalClosure ({a} : Set G)) ∈ d.first)
    (S : Sylow 2 G) (hz : a ∈ (center S).map (S : Subgroup G).subtype) : False := by
  let := h.finite_group
  let K := normalClosure ({a} : Set G)
  let A := d.first.map K.subtype
  let B := d.second.map K.subtype
  have haA : a ∈ A := mem_map_of_mem K.subtype ha
  have hjoin : A ⊔ B = K := by
    change d.first.map K.subtype ⊔ d.second.map K.subtype = K
    rw [← Subgroup.map_sup, d.product.sup_eq_top, ← MonoidHom.range_eq_map, range_subtype]
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
  exact not_twoCentral_of_normalClosure_pair A B a haA h.nonidentity hjoin hdis hB hperm S hz

theorem Hypotheses.not_two_factors_of_twoCentral
    (h : Hypotheses κ ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (d : SourceTwoFactorCase (ρ.comp (normalClosure ({a} : Set G)).subtype))
    (S : Sylow 2 G) (hz : a ∈ (center S).map (S : Subgroup G).subtype) : False := by
  let := h.finite_module
  let t : normalClosure ({a} : Set G) := ⟨a, subset_normalClosure (Set.mem_singleton a)⟩
  rcases d.rank_one_mem_factor t ht.le with ha | hb
  · exact central_exclusion_of_marked_first h ht d ha S hz
  · let d' : SourceTwoFactorCase (ρ.comp (normalClosure ({a} : Set G)).subtype) :=
      { first := d.second
        second := d.first
        product := d.product.swap
        firstSpace := d.secondSpace
        secondSpace := d.firstSpace
        decomposition := d.decomposition.symm
        firstCase := d.secondCase
        secondCase := d.firstCase }
    exact central_exclusion_of_marked_first h ht d' hb S hz

/-- On the original two-central domain the sole unresolved B.5 source row is
quasisimple; no product-geometry premise remains. -/
theorem Hypotheses.rank_one_twoCentral_source_reduction
    (hA : SemisimpleInput.{u} KnownSimple.IsKnownSimple)
    (h36 : Chapter1.Section02.A36Input.{u} KnownSimple.IsKnownSimple)
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,v} KnownSimple.IsKnownSimple)
    (h : Hypotheses KnownSimple.IsKnownSimple ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (S : Sylow 2 G) (hz : a ∈ (center S).map (S : Subgroup G).subtype) :
    Conclusion ρ a ∨
      (IsQuasisimple (generalizedFitting (normalClosure ({a} : Set G))) ∧
        Nonempty (ProjectiveLine.QuasisimpleSourceConclusion
          (ρ.comp (normalClosure ({a} : Set G)).subtype)
          (generalizedFitting (normalClosure ({a} : Set G))))) := by
  rcases h.rank_one_source_reduction hA h36 h4 ht with hc | hh
  · exact Or.inl hc
  · rcases hh with hq | hd
    · exact Or.inr hq
    · obtain ⟨d⟩ := hd
      exact (h.not_two_factors_of_twoCentral ht d S hz).elim
end CFSG.Quasithin.ChapterG.Section06
