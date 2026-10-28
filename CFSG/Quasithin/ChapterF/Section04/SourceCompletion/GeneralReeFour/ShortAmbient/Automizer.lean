module
public import CFSG.Quasithin.ChapterI.Section06To08.UniqueFixedSource
public import Theory.ElementaryAbelian.Injective

/-!
# The I.8.5 obstruction on the actual actor quotient

Embed a nontrivial elementary plane in the local subgroup and retain its
relative normality. Unique fixed cosets in a proper overgroup make the
actor quotient solvable by I.8.5. A nonsolvable group acting faithfully on
the plane embeds in that quotient, giving a contradiction.

Source: Aschbacher--Smith F.4.42 and I.8.5, printed pp.295,430.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeFour.ShortAmbient

/-- The I.8.5 contradiction for a literal normal elementary plane and a
faithful nonsolvable subgroup of its induced automorphisms. -/
theorem eq_top_of_unique_fixed_nonsolvable_action
    {M K A : Type*} [Group M] [Finite M] [Group K] [Group A]
    [IsElementaryAbelian 2 A] [Nontrivial A]
    (X : Subgroup M) (j : A →* X) (hj : Function.Injective j)
    [j.range.Normal] (f : K →* X)
    (hfaith : ∀ k, f k ∈ centralizer (j.range : Set X) → k = 1)
    (hnonsolv : ¬ Group.IsSolvable K)
    (hfix : ∀ a : A, a ≠ 1 → ∃! q : M ⧸ X, (j a).val • q = q) :
    X = ⊤ := by
  classical
  by_contra hproper
  let W := j.range.map X.subtype
  have hWX : W ≤ X := map_subtype_le _
  have hWsub : W.subgroupOf X = j.range :=
    comap_map_eq_self_of_injective X.subtype_injective _
  let : IsElementaryAbelian 2 j.range :=
    IsElementaryAbelian.of_injective (MonoidHom.ofInjective hj).symm.toMonoidHom
      (MonoidHom.ofInjective hj).symm.injective
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map_subtype
  let : (W.subgroupOf X).Normal := hWsub.symm ▸ inferInstance
  have hWne : W ≠ ⊥ := by
    intro hW
    obtain ⟨a,ha⟩ := exists_ne (1 : A)
    have hjw : (j a).val ∈ W := mem_map_of_mem _ (show j a ∈ j.range from ⟨a,rfl⟩)
    rw [hW,mem_bot] at hjw
    exact ha (hj (Subtype.ext (hjw.trans (congrArg Subtype.val j.map_one).symm)))
  have hf : ∀ w : M, w ∈ W → w ≠ 1 → ∃! q : M ⧸ X, w • q = q := by
    rintro _ ⟨x,⟨a,rfl⟩,rfl⟩ hne
    apply hfix a
    intro ha
    apply hne
    rw [ha,map_one]
    rfl
  have hs := ChapterI.Section06To08.lemma_I_8_5_automizer W X hWX hWne hproper hf
  let : Group.IsSolvable (X ⧸ centralizer (W.subgroupOf X : Set X)) := hs
  let q := (QuotientGroup.mk' (centralizer (W.subgroupOf X : Set X))).comp f
  have hq : Function.Injective q := by
    apply (injective_iff_map_eq_one q).mpr
    intro k hk
    apply hfaith k
    simpa only [hWsub] using (QuotientGroup.eq_one_iff _).mp hk
  exact hnonsolv (Group.isSolvable_of_isSolvable_injective hq)

end CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeFour.ShortAmbient
