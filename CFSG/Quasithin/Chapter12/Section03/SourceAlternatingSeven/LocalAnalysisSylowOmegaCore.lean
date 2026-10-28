module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowModelsTransport
public import Theory.Representation.BinaryPermutation.SevenCommutant

/-!
# Residual control on the actual Sylow omega center

The marked weight-two and weight-six points lie in Ω₁Z(T). The natural
A₇ module has no nonidentity fixed point, so the weight-six residual is
strictly smaller than L. The two ambient prime-to-three residual identities
therefore distinguish the fixed subgroup from its weight-six coset.
A conjugator preserving the latter residual and T preserves their common
two-core, whose normalizer is controlled by source uniqueness.

The last lemma applies these facts to every nonidentity point transported
within the union of the two cosets. The companion geometry module uses it
on an intersection of conjugate slices. The omega-span dimension remains
an independent source obligation, not a field added to Setup.

Source: Aschbacher–Smith, 3.3.22, printed pp.597–598, refs/quasithin.pdf.
-/

@[expose] public noncomputable section

open Subgroup
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}
variable {E : S.NaturalCoordinates}
namespace SylowNormalizer
namespace Points
variable (P : Points E)

lemma two_mem_omega : (P.two : G) ∈ omegaCenterIn (T : Subgroup G) := by
  let := S.chosen.elementary
  exact (mem_omegaCenterIn_iff _ _).mpr ⟨S.chosen.le_sylow P.two.property,
    P.two_central, elemPow_eq_one_of_isElementaryAbelian _ P.two.property⟩

lemma six_mem_omega : (P.six : G) ∈ omegaCenterIn (T : Subgroup G) := by
  let := S.chosen.elementary
  exact (mem_omegaCenterIn_iff _ _).mpr ⟨S.chosen.le_sylow P.six.property,
    P.six_central, elemPow_eq_one_of_isElementaryAbelian _ P.six.property⟩

lemma two_ne_one : (P.two : G) ≠ 1 := by
  intro h
  have he : P.two = 1 := Subtype.ext h
  have hw := P.two_weight
  rw [he, map_one] at hw
  have hz : weight (0 : Word) = 0 := by decide
  exact (by decide : (0 : ℕ) ≠ 2) (hz.symm.trans hw)

lemma six_ne_one : (P.six : G) ≠ 1 := by
  intro h
  have he : P.six = 1 := Subtype.ext h
  have hw := P.six_weight
  rw [he, map_one] at hw
  have hz : weight (0 : Word) = 0 := by decide
  exact (by decide : (0 : ℕ) ≠ 6) (hz.symm.trans hw)

lemma two_ne_six : (P.two : G) ≠ P.six := by
  intro h
  have he : P.two = P.six := Subtype.ext h
  have hw := P.two_weight
  rw [he, P.six_weight] at hw
  omega

include E in
lemma natural_fixed_eq_one {v : V} (hv : (v : G) ∈ centralizer (L : Set G)) :
    v = 1 := by
  have hz := BinaryPermutation.SevenCommutant.fixed_eq_zero
    (evenWordsEquivNatural (E.coordinates v).toAdd) (fun a => ?_)
  · apply E.coordinates.injective
    apply Multiplicative.toAdd.injective
    apply evenWordsEquivNatural.injective
    simpa only [map_one, toAdd_one, map_zero] using hz
  · obtain ⟨l, rfl⟩ := S.projection_surjective a
    rw [← evenWordsEquivNatural_equivariant, ← E.equivariant]
    have hvv : V.normalizerMonoidHom ⟨l, S.chosen.normalizes l.property⟩ v = v := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hv l l.property)
    rw [hvv]

lemma sixGroup_lt_component : P.sixGroup < L := by
  refine lt_of_le_of_ne ((pointResidual_le L (P.six : G)).trans inf_le_left) ?_
  intro he
  have hc : L ≤ centralizer ({(P.six : G)} : Set G) :=
    he.ge.trans ((pointResidual_le L (P.six : G)).trans inf_le_right)
  have hv : (P.six : G) ∈ centralizer (L : Set G) := by
    intro l hl
    exact mem_centralizer_singleton_iff.mp (hc hl)
  exact P.six_ne_one (congrArg Subtype.val (natural_fixed_eq_one (E := E) hv))

include S in
lemma core_normalizer_le_component :
    normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) ≤ normalizer (L : Set G) := by
  apply S.chosen.normal_subgroup_normalizer_le S.hypothesis.toHypothesis1221
    (pCoreIn_le 2 _) _ ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  intro he
  exact S.chosen.ne_bot (bot_unique (S.chosen.le_core.trans_eq he))

lemma sixGroup_normalizer_le_component (M : P.Models) :
    normalizer (T : Set G) ⊓ normalizer (P.sixGroup : Set G) ≤
      normalizer (L : Set G) := by
  have hj : normalizer (T : Set G) ⊓ normalizer (P.sixGroup : Set G) ≤
      normalizer ((P.sixGroup ⊔ (T : Subgroup G) : Subgroup G) : Set G) := by
    rw [inf_comm]
    exact normalizer_inf_normalizer_le_normalizer_sup _ _
  have hc := hj.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  change _ ≤ normalizer ((P.sixGroup ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) at hc
  rw [M.core_eq] at hc
  exact hc.trans (core_normalizer_le_component (S := S))

lemma six_fixed_normalizes_component (M : P.Models) (R : P.AmbientResiduals)
    {g : G} (hg : g ∈ normalizer (T : Set G))
    (he : g * (P.six : G) * g⁻¹ = P.six) : g ∈ normalizer (L : Set G) := by
  have hr : pointThreeResidual (P.six : G) = P.sixGroup := by
    simpa only [one_mul] using R.six_residual 1 P.fixed.one_mem
  apply P.sixGroup_normalizer_le_component M ⟨hg, ?_⟩
  apply mem_normalizer_iff_map_conj_eq.mpr
  change P.sixGroup.map (MulAut.conj g).toMonoidHom = P.sixGroup
  rw [← hr, pointThreeResidual_conj, he]

lemma omega_centralizer_normalizer_le_component (M : P.Models) (R : P.AmbientResiduals) :
    normalizer (T : Set G) ⊓ centralizer (omegaCenterIn (T : Subgroup G) : Set G) ≤
      normalizer (L : Set G) := by
  intro g hg
  apply P.six_fixed_normalizes_component M R hg.1
  exact mul_inv_eq_iff_eq_mul.mpr (hg.2 _ P.six_mem_omega).symm

lemma sixGroup_card_lt : Nat.card P.sixGroup < Nat.card L := by
  refine lt_of_le_of_ne (card_le_of_le P.sixGroup_lt_component.le) ?_
  intro he
  exact P.sixGroup_lt_component.ne
    (eq_of_le_of_card_ge P.sixGroup_lt_component.le he.ge)

lemma conjugate_sixGroup_ne_component (g : G) :
    P.sixGroup.map (MulAut.conj g).toMonoidHom ≠ L := by
  intro he
  have hh := congrArg (fun H : Subgroup G => Nat.card H) he
  rw [card_map_of_injective (MulAut.conj g).injective] at hh
  exact P.sixGroup_card_lt.ne hh

lemma conjugate_component_ne_sixGroup (g : G) :
    L.map (MulAut.conj g).toMonoidHom ≠ P.sixGroup := by
  intro he
  have hh := congrArg (fun H : Subgroup G => Nat.card H) he
  rw [card_map_of_injective (MulAut.conj g).injective] at hh
  exact P.sixGroup_card_lt.ne hh.symm

/-- The two residual labels cannot be exchanged by conjugation. -/
lemma residual_slice_transport (M : P.Models) (R : P.AmbientResiduals)
    {g z : G} (hg : g ∈ normalizer (T : Set G)) (hz : z ≠ 1)
    (hzs : z ∈ P.fixed ∨ ∃ c ∈ P.fixed, z = c * (P.six : G))
    (hgs : g*z*g⁻¹ ∈ P.fixed ∨ ∃ c ∈ P.fixed, g*z*g⁻¹ = c * (P.six : G)) :
    g ∈ normalizer (L : Set G) := by
  have hgn : g*z*g⁻¹ ≠ 1 := by
    intro h
    apply hz
    exact (MulAut.conj g).injective (h.trans (map_one (MulAut.conj g)).symm)
  have ht := pointThreeResidual_conj z g
  rcases hzs with hzfix | ⟨c, hc, rfl⟩
  · rw [R.fixed_residual z hzfix hz] at ht
    rcases hgs with hgfix | ⟨d, hd, he⟩
    · rw [R.fixed_residual _ hgfix hgn] at ht
      exact mem_normalizer_iff_map_conj_eq.mpr ht
    · rw [he, R.six_residual d hd] at ht
      exact (P.conjugate_component_ne_sixGroup g ht).elim
  · rw [R.six_residual c hc] at ht
    rcases hgs with hgfix | ⟨d, hd, he⟩
    · rw [R.fixed_residual _ hgfix hgn] at ht
      exact (P.conjugate_sixGroup_ne_component g ht).elim
    · rw [he, R.six_residual d hd] at ht
      exact P.sixGroup_normalizer_le_component M
        ⟨hg, mem_normalizer_iff_map_conj_eq.mpr ht⟩

end Points
end SylowNormalizer
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
