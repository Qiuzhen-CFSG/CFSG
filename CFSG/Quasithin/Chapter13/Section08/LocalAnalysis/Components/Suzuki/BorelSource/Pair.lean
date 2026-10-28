module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.BorelSource.Setup
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.ProductCoordinates
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.SuzukiExclusion.ConcreteAction


/-!
# Marked matrix coordinates on the swapped Suzuki orbit

The normalizer-index bound identifies K₀ with K Kᵗ for the specified
moving t ∈ T. The two literal star images remain distinct components,
hence commute. The actual Suzuki model makes their centers trivial, so
multiplication supplies a direct-product equivalence. Its two coordinates
are marked by the original component and its actual t-conjugate.

Both coordinate formulas use `starModelEquiv`, hence the proven kernel
O₂(K) and the source's original model. No final normality theorem for K
is used, and the one-component case remains a separate orbit alternative.

Source: Aschbacher–Smith, 13.8.16, printed pp.952–953 (combined manuscript
of 1 March 2004).
-/

@[expose] public section

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.BorelSource
variable {G : Type*} [Group G] [Finite G]
variable {H K L₁ T G₁ M : Subgroup G} {m : ℕ}

private theorem suzuki_star_center (d : Earlier H K L₁ T G₁ M m) :
    center (Source.starImage H K) = ⊥ := by
  let : IsSimpleGroup (SuzukiMatrixGroup m) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 m d.parameter_pos).1
  let : IsSimpleGroup (Source.starImage H K) :=
    (starModelEquiv H K d.component_le d.component m d.model).isSimpleGroup
  let := d.star_quasisimple
  rcases (inferInstance : (center (Source.starImage H K)).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative (Source.starImage H K)
      (center_eq_top_iff.mp h)).elim

private theorem moving_index (d : Earlier H K L₁ T G₁ M m)
    {t : G} (ht : t ∈ T) (hm : t ∉ normalizer (K : Set G)) :
    (normalizer (K.subgroupOf H : Set H)).index = 2 := by
  have hp := (normalizer (K.subgroupOf H : Set H)).index_ne_zero_of_finite
  have hne : (normalizer (K.subgroupOf H : Set H)).index ≠ 1 := by
    intro he
    have hn := index_eq_one.mp he
    have hh : (⟨t, (le_sup_right.trans d.base_le) ht⟩ : H) ∈
        normalizer (K.subgroupOf H : Set H) := by rw [hn]; trivial
    rw [← subgroupOf_normalizer_eq d.component_le] at hh
    exact hm hh
  have hb := d.component_index
  omega

theorem moving_orbit (d : Earlier H K L₁ T G₁ M m)
    {t : G} (ht : t ∈ T) (hm : t ∉ normalizer (K : Set G)) :
    conjugateSpanBy K T = K ⊔ K.conjBy t :=
  Swapped.orbit_eq_two_conjugates H K T d.component_le
    (le_sup_right.trans d.base_le) (moving_index d ht hm) ht hm

private theorem moving_product (d : Earlier H K L₁ T G₁ M m)
    {t : G} (ht : t ∈ T) (hm : t ∉ normalizer (K : Set G)) :
    ∃ f : Source.starImage H K × Source.starImage H K ≃*
        Source.starImage H (conjugateSpanBy K T),
      ∀ a b, (f (a, b) : Source.Hstar H) = (a : Source.Hstar H) *
        (Swapped.LinearTwo.starConjugateEquiv H K d.component_le
          ((le_sup_right.trans d.base_le) ht) b : Source.Hstar H) := by
  have htH : t ∈ H := (le_sup_right.trans d.base_le) ht
  let c := Swapped.LinearTwo.starConjugateEquiv H K d.component_le htH
  let := d.star_quasisimple
  have hqJ : IsQuasisimple (Source.starImage H (K.conjBy t)) := IsQuasisimple.of_mulEquiv c
  obtain ⟨hJH, hJ⟩ := Swapped.conjugate_isCComponent H K d.component_le d.component htH
  have hne : K ≠ K.conjBy t := fun h => hm (mem_normalizer_iff_map_conj_eq.mpr h.symm)
  have hc := Swapped.LinearTwo.starImages_commute H K (K.conjBy t)
    d.component_le hJH d.component hJ hne d.star_quasisimple hqJ
  have hd : Disjoint (Source.starImage H K) (Source.starImage H (K.conjBy t)) := by
    apply disjoint_def.mpr
    intro x hx hy
    have hz : (⟨x, hx⟩ : Source.starImage H K) ∈ center (Source.starImage H K) := by
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      exact (commutator_eq_bot_iff_le_centralizer.mp hc y.property x hy).symm
    rw [suzuki_star_center d, mem_bot] at hz
    exact congrArg Subtype.val hz
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting _ _ hd
    (commutator_eq_bot_iff_le_centralizer.mp hc)
  have hsup : Source.starImage H K ⊔ Source.starImage H (K.conjBy t) =
      Source.starImage H (conjugateSpanBy K T) := by
    rw [moving_orbit d ht hm]
    exact (Swapped.LinearTwo.starImage_sup H K (K.conjBy t) d.component_le hJH).symm
  refine ⟨((MulEquiv.prodCongr (MulEquiv.refl _) c).trans e).trans
    (MulEquiv.subgroupCongr hsup), ?_⟩
  intro a b
  exact he a (c b)

theorem moving_matrix_coordinates (d : Earlier H K L₁ T G₁ M m)
    {t : G} (ht : t ∈ T) (hm : t ∉ normalizer (K : Set G)) :
    ∃ e : Source.starImage H (conjugateSpanBy K T) ≃*
        SuzukiMatrixGroup m × SuzukiMatrixGroup m,
      (∀ a : Source.starImage H K, ∀ ha,
        e ⟨a, ha⟩ = (starModelEquiv H K d.component_le d.component m d.model a, 1)) ∧
      (∀ a : Source.starImage H K, ∀ ha,
        e ⟨Swapped.LinearTwo.starConjugateEquiv H K d.component_le
          ((le_sup_right.trans d.base_le) ht) a, ha⟩ =
          (1, starModelEquiv H K d.component_le d.component m d.model a)) := by
  obtain ⟨f, hf⟩ := moving_product d ht hm
  let c := Swapped.LinearTwo.starConjugateEquiv H K d.component_le
    ((le_sup_right.trans d.base_le) ht)
  let eK := starModelEquiv H K d.component_le d.component m d.model
  let e := f.symm.trans (MulEquiv.prodCongr eK eK)
  refine ⟨e, ?_, ?_⟩
  · intro a ha
    have he : (⟨(a : Source.Hstar H), ha⟩ : Source.starImage H (conjugateSpanBy K T)) = f (a, 1) := by
      apply Subtype.ext
      rw [hf, map_one]
      simp only [Subgroup.coe_one, mul_one]
    rw [he]
    change (MulEquiv.prodCongr eK eK) (f.symm (f (a, 1))) = _
    rw [f.symm_apply_apply]
    change (eK a, eK 1) = (eK a, 1)
    rw [map_one]
  · intro a ha
    have he : (⟨(c a : Source.Hstar H), ha⟩ : Source.starImage H (conjugateSpanBy K T)) = f (1, a) := by
      apply Subtype.ext
      rw [hf]
      simp [c]
    rw [he]
    change (MulEquiv.prodCongr eK eK) (f.symm (f (1, a))) = _
    rw [f.symm_apply_apply]
    change (eK 1, eK a) = (1, eK a)
    rw [map_one]

theorem orbit_cases (d : Earlier H K L₁ T G₁ M m) :
    conjugateSpanBy K T = K ∨
      ∃ t ∈ T, t ∉ normalizer (K : Set G) ∧ conjugateSpanBy K T = K ⊔ K.conjBy t := by
  by_cases h : conjugateSpanBy K T = K
  · exact Or.inl h
  · obtain ⟨t, ht, hm⟩ := Swapped.exists_moving_element K T h
    exact Or.inr ⟨t, ht, hm, moving_orbit d ht hm⟩

end CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.BorelSource
