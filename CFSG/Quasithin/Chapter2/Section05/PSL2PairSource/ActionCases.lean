module

public import CFSG.Quasithin.Chapter2.Section05.PSL2PairSource.OuterCases
public import CFSG.Quasithin.Chapter2.Section05.PSL2PairSource.Swapping
public import CFSG.Quasithin.Chapter2.Section05.PSL2PairSource.InnerActions

/-!
# Complete marked-conjugate action cases for the PSL₂ pair

The component permutation dichotomy and fixed-diagonal contradiction rule
out factor swapping. The outer-action arguments make the first action
inner. Conjugation by the original crossing element exchanges the factors,
so the same result makes the second action inner, using the literal
transport of normalizer actions. Faithfulness then puts the involution in
the pair product, and the original t/z nonfusion removes its diagonal.

Thus the marked-class exclusion has no remaining case-coverage or model
premise. Source: Aschbacher–Smith, proof of 2.5.21, printed pp.566–567.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16.CounterexampleGeometry
namespace CFSG.Quasithin.Chapter2.PSL2PairSource.Incoming
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
variable {p : ℕ} [Fact p.Prime]

private theorem crossing_twice_eq (d : Incoming κ G p) :
    conjugate (conjugate d.K d.x) d.x = d.K := by
  rw [conjugate_conjugate, ← pow_two]
  apply (mem_normalizer_iff_conjugate_eq _ _).mp
  apply d.j_normalizes_k
  have hSJ : d.S ≤ centralizer ({d.t} : Set G) := by
    rw [← d.sylow_eq]
    exact map_subtype_le _
  exact hSJ d.x_square

/-- Conjugating by the original crossing element transports the first-factor
innerness theorem to the second factor, with the literal actions preserved. -/
theorem inner_right_of_normalizing_factors (d : Incoming κ G p) (g : G)
    (hiK : g⁻¹ * d.t * g ∈ normalizer (d.K : Set G))
    (hiL : g⁻¹ * d.t * g ∈ normalizer (conjugate d.K d.x : Set G)) :
    (conjugate d.K d.x).normalizerMonoidHom ⟨g⁻¹ * d.t * g, hiL⟩ ∈
      (MulAut.conj : conjugate d.K d.x →* MulAut (conjugate d.K d.x)).range := by
  let L := conjugate d.K d.x
  let f := MulAut.conj d.x⁻¹
  let i := g⁻¹ * d.t * g
  let j := (g * d.x)⁻¹ * d.t * (g * d.x)
  have hj : j = f i := by dsimp [j, i, f, MulAut.conj_apply]; group
  have hLK : L.map f.toMonoidHom = d.K := crossing_twice_eq d
  have hKL : d.K.map f.toMonoidHom = L := rfl
  have hjK : j ∈ normalizer (d.K : Set G) := by
    rw [hj, ← hLK, ← map_equiv_normalizer_eq L f]
    exact mem_map_of_mem f.toMonoidHom hiL
  have hjL : j ∈ normalizer (L : Set G) := by
    rw [hj, ← hKL, ← map_equiv_normalizer_eq d.K f]
    exact mem_map_of_mem f.toMonoidHom hiK
  let e : L ≃* d.K := (f.subgroupMap L).trans (MulEquiv.subgroupCongr hLK)
  have hact : MulAut.congr e (L.normalizerMonoidHom ⟨i, hiL⟩) =
      d.K.normalizerMonoidHom ⟨j, hjK⟩ := by
    ext k
    have hback : f (e.symm k : G) = (k : G) :=
      congrArg Subtype.val (e.apply_symm_apply k)
    change f (i * (e.symm k : G) * i⁻¹) = j * (k : G) * j⁻¹
    rw [map_mul, map_mul, map_inv, hback, ← hj]
  obtain ⟨k, hk⟩ := d.inner_left_of_normalizing_factors (g * d.x) hjK hjL
  obtain ⟨l, hl⟩ := (MulAut.congr_inner_iff e (L.normalizerMonoidHom ⟨i, hiL⟩)).mp
    ⟨k, hact.trans hk.symm⟩
  exact ⟨l, hl.symm⟩

/-- The factor permutation dichotomy and diagonal contradiction force every
marked conjugate in M₊ to normalize both original factors. -/
theorem marked_normalizes_factors (d : Incoming κ G p) (g : G)
    (hiM : g⁻¹ * d.t * g ∈ normalizer ((d.K ⊔ conjugate d.K d.x : Subgroup G) : Set G)) :
    g⁻¹ * d.t * g ∈ normalizer (d.K : Set G) ∧
      g⁻¹ * d.t * g ∈ normalizer (conjugate d.K d.x : Set G) := by
  let L := conjugate d.K d.x
  let i := g⁻¹ * d.t * g
  let : IsQuasisimple d.K := d.factor_quasisimple
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv ((MulAut.conj d.x⁻¹).subgroupMap d.K)
  have hk : d.K.map (MulAut.conj i).toMonoidHom = d.K := by
    rcases conjugate_component_eq_of_mem_pair_normalizer d.commuting hiM with hh | hh
    · exact hh
    · exact (d.false_of_factor_swapping g hh).elim
  refine ⟨mem_normalizer_iff_map_conj_eq.mpr hk, ?_⟩
  have hcomm : ⁅L, d.K⁆ = ⊥ := by rw [commutator_comm]; exact d.commuting
  have hiM' : i ∈ normalizer ((L ⊔ d.K : Subgroup G) : Set G) := by rw [sup_comm]; exact hiM
  rcases conjugate_component_eq_of_mem_pair_normalizer hcomm hiM' with hh | hh
  · exact mem_normalizer_iff_map_conj_eq.mpr hh
  · have he : L = d.K := Subgroup.map_injective (MulAut.conj i).injective (hh.trans hk.symm)
    have hd := disjoint_iff.mp (disjoint_of_commuting_of_center_eq_bot d.commuting d.factor_center_eq_bot)
    have ht1 : d.t = 1 := mem_bot.mp (hd ▸
      (show d.t ∈ d.K ⊓ L from ⟨he ▸ d.mark_mem, d.mark_mem⟩))
    have := d.t_order
    simp [ht1] at this

/-- Complete action-case coverage: a marked conjugate in M₊ belongs to the
actual pair product. Swapping and all outer cases have been excluded. -/
theorem marked_conjugate_mem_pair (d : Incoming κ G p) (g : G)
    (hiM : g⁻¹ * d.t * g ∈ normalizer ((d.K ⊔ conjugate d.K d.x : Subgroup G) : Set G)) :
    g⁻¹ * d.t * g ∈ d.K ⊔ conjugate d.K d.x := by
  obtain ⟨hiK, hiL⟩ := d.marked_normalizes_factors g hiM
  exact d.inner_actions_mem_pair hiM hiK hiL
    (d.inner_left_of_normalizing_factors g hiK hiL)
    (d.inner_right_of_normalizing_factors g hiK hiL)

/-- The original nonfusion of t and z removes the diagonal elements, leaving
precisely one factor for every marked conjugate in the pair normalizer. -/
theorem marked_class_exclusion (d : Incoming κ G p) (a : G) (ha : IsConj d.t a)
    (haM : a ∈ normalizer ((d.K ⊔ conjugate d.K d.x : Subgroup G) : Set G)) :
    a ∈ (d.K : Set G) ∪ conjugate d.K d.x := by
  apply d.class_exclusion_in_pair ha
  obtain ⟨g, rfl⟩ := isConj_iff.mp ha
  simpa only [inv_inv] using d.marked_conjugate_mem_pair g⁻¹ (by simpa only [inv_inv] using haM)

end CFSG.Quasithin.Chapter2.PSL2PairSource.Incoming

end
