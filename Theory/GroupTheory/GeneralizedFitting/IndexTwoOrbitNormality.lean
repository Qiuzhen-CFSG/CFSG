module

public import Theory.GroupTheory.GeneralizedFitting.NormalInnerInvolution
public import Theory.GroupTheory.GeneralizedFitting.ComponentImageNormalizer
public import Theory.GroupTheory.GeneralizedFitting.SylowNormalizedComponent

/-!
# Normality from the two-component orbit bound

In a group of odd-prime ranks at most two, a component has at most two
conjugates. A nonnormal centerless component and its commuting conjugate
therefore give twice the square of any divisor of its order. This divisibility
also holds in any quotient that embeds the component. Its failure forces
normality without requiring the stronger square obstruction in the ambient group.

Source: Aschbacher--Smith 1.2.4 and the component inspection in 14.3.22,
printed p.999. The actual application is OppositeCentralizer.RecognitionSmallModels.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

omit [Finite H] in
private theorem IsComponent.normal_of_index_two_square_bound
    {D : Subgroup H} (hD : IsComponent H D) (hz : center D = ⊥)
    (hi : D.Normal ∨ (normalizer (D : Set H)).index = 2)
    {n : ℕ} (hn : n ∣ Nat.card D) (hsmall : ¬ n*n*2 ∣ Nat.card H) : D.Normal := by
  rcases hi with h | hidx
  · exact h
  apply normal_iff_map_conj_eq.mpr
  intro g
  by_contra hne
  let E := D.map (MulAut.conj g).toMonoidHom
  have hc : E ≤ centralizer (D : Set H) :=
    commutator_eq_bot_iff_le_centralizer.mp ((hD.map_conj g).commutator_eq_bot_of_ne hD hne)
  have hd : Disjoint D E := by
    apply disjoint_iff.mpr
    apply (eq_bot_iff_forall _).mpr
    intro x hx
    have hxZ : (⟨x,hx.1⟩ : D) ∈ center D :=
      mem_center_iff.mpr fun y => Subtype.ext (hc hx.2 y y.property)
    exact congrArg D.subtype (mem_bot.mp (hz ▸ hxZ))
  have he : Nat.card E = Nat.card D := (Nat.card_congr ((MulAut.conj g).subgroupMap D).toEquiv).symm
  have hcard := card_dvd_of_le (show D ⊔ E ≤ normalizer (D : Set H) from
    sup_le D.le_normalizer (hc.trans (Subgroup.centralizer_le_normalizer _)))
  rw [card_sup_eq_mul_of_normalizes_of_disjoint D E
    (hc.trans (Subgroup.centralizer_le_normalizer _)) hd,he] at hcard
  have hh := Nat.mul_dvd_mul ((Nat.mul_dvd_mul hn hn).trans hcard) (dvd_refl 2)
  rw [←hidx,(normalizer (D : Set H)).card_mul_index] at hh
  exact hsmall (by simpa only [hidx] using hh)

omit [Finite H] in
/-- A faithful surviving component has normalizer index at most two in the
image. A missing twice-square divisor therefore forces the original component normal. -/
theorem IsComponent.normal_of_injective_image_twice_square_not_dvd
    {D : Subgroup G} (hD : IsComponent G D) (hz : center D = ⊥)
    (hrank : ∀ p : ℕ, p.Prime → Odd p → primeRank p G ≤ 2)
    (f : G →* H) (hf : Function.Surjective f)
    (hinj : Function.Injective (f.comp D.subtype))
    {n : ℕ} (hn : n ∣ Nat.card D) (hsmall : ¬ n*n*2 ∣ Nat.card H) : D.Normal := by
  let E := D.map f
  let e : D ≃* E := MulEquiv.ofBijective (f.subgroupMap D)
    ⟨fun x y hh => hinj (congrArg Subtype.val hh),f.subgroupMap_surjective D⟩
  have hEne : E ≠ ⊥ := by
    intro hb
    let := hD.2
    let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
    let : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
    have hh : Nat.card D = 1 := by rw [Nat.card_congr e.toEquiv,hb]; simp
    have hsub : Subsingleton D := Finite.card_le_one_iff_subsingleton.mp hh.le
    let := hsub
    have hcomm : IsMulCommutative D := ⟨⟨fun _ _ => Subsingleton.elim _ _⟩⟩
    exact Group.IsPerfect.not_isMulCommutative D hcomm
  have hE : IsComponent H E := (hD.map_surjective f hf).resolve_left hEne
  have hzE : center E = ⊥ := by
    apply (eq_bot_iff_forall _).mpr
    intro x hx
    have hh := (centerCongr e.symm ⟨x,hx⟩).property
    exact e.symm.map_eq_one_iff.mp (mem_bot.mp (hz ▸ hh))
  have hN : (normalizer (E : Set H)).comap f = normalizer (D : Set G) := by
    apply le_antisymm
    · intro x hx
      exact hD.mem_normalizer_of_mem_normalizer_map f hEne hx
    · intro x hx
      exact D.le_normalizer_map f (mem_map_of_mem f hx)
  have hi : E.Normal ∨ (normalizer (E : Set H)).index = 2 := by
    rcases hD.normal_or_index_two_of_odd_rank_le_two hrank with hn | hn
    · exact Or.inl (hn.map f hf)
    · right
      rwa [←(normalizer (E : Set H)).index_comap_of_surjective hf,hN]
  have hnE : n ∣ Nat.card E := (Nat.card_congr e.toEquiv) ▸ hn
  let := hE.normal_of_index_two_square_bound hzE hi hnE hsmall
  apply normalizer_eq_top_iff.mp
  rw [←hN,normalizer_eq_top,comap_top]

end Theory.GroupTheory
