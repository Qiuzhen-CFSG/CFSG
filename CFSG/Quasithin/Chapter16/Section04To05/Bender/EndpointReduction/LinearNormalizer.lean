module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.Contracts
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.Centralizer
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.SpecificGroups.PSL2.SylowFixedQuotients.Five
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# The normalizer equality at the linear Bender endpoint

The order-21 normalizer image forces T to centralize V. In PSL₂(4), every
two-subgroup has exponent two, so T_L lies in V and T fixes T_L pointwise.
A Sylow restriction inside N_G(L) makes T_L an actual Sylow subgroup of L.
The proved PSL₂(4) ≃ A₅ comparison and A₅ pointwise-fixer theorem therefore
make T act by inner automorphisms on L. The outer automorphism group of A₅
is a two-group. Its image under N_G(L) has odd order because the action
kernel contains T; hence this image is trivial. Factoring an inner actor
as a component element times a centralizer element proves N_G(L) = L C_G(L).

This derives the normalizer equality from the exceptional action and actual
model computations. It does not strengthen source 16.4.6, whose statement
only excludes certain outer involutions in R. The private outer-two calculation
is adapted from `Theory.SpecificGroups.AlternatingFiveInnerNormalizer`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1194–1195, Proposition 16.5.1; GLS III, Theorem 5.2.1, for Aut(A₅).
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter16.Intersections.Bender
variable {G : Type*} [Group G] [Finite G]

theorem componentSylow_isSylow {T : Sylow 2 G} {L : Subgroup G}
    (hT : (T : Subgroup G) ≤ normalizer (L : Set G)) : SylowIn (componentSylow T L) L := by
  let N := normalizer (L : Set G)
  let D := L.subgroupOf N
  let S := T.subtype hT
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_normal D
  let e := subgroupOfEquivOfLe L.le_normalizer
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change ((P : Subgroup D).map e.toMonoidHom).map L.subtype = _
  rw [hP, map_map]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.property⟩
  · intro hx
    exact ⟨⟨⟨x, L.le_normalizer hx.2⟩, hx.2⟩, hx.1, rfl⟩

private theorem outer_five_two : IsPGroup 2 (MulAut.Outer (alternatingGroup (Fin 5))) := by
  intro q
  obtain ⟨α, rfl⟩ :=
    QuotientGroup.mk'_surjective (MulAut.innerSubgroup (alternatingGroup (Fin 5))) q
  obtain ⟨σ, rfl⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide)
      (by decide)).surjective α
  refine ⟨1, ?_⟩
  simp only [pow_one, ← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  have hσ : σ ^ 2 ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_pow]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  exact ⟨⟨σ ^ 2, hσ⟩, MulAut.conjNormal_val.symm⟩

omit [Finite G] in
theorem Geometry.sylow_centralizes_space {T : Sylow 2 G} {L R : Subgroup G} {n : ℕ}
    (d : Geometry T L R n)
    (hA : Nat.card (ActionImage (benderSpace T L)) = 21) :
    (T : Subgroup G) ≤ centralizer (benderSpace T L : Set G) := by
  let V := benderSpace T L
  let f := V.normalizerMonoidHom.rangeRestrict.comp (inclusion d.sylow_normalizes)
  have hp : IsPGroup 2 f.range := T.isPGroup'.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hc : Nat.card f.range = 1 := by
    rcases hp.card_eq_or_dvd with h | h
    · exact h
    · have hd := f.range.card_subgroup_dvd_card
      rw [hA] at hd
      exact False.elim ((by decide : ¬ 2 ∣ 21) (h.trans hd))
  have hf : f = 1 := MonoidHom.range_eq_bot_iff.mp (Subgroup.card_eq_one.mp hc)
  intro t ht
  have hk : (⟨t, d.sylow_normalizes ht⟩ : normalizer (V : Set G)) ∈ V.normalizerMonoidHom.ker := by
    have he : f ⟨t, ht⟩ = 1 := by rw [hf]; rfl
    exact congrArg Subtype.val he
  rw [V.normalizerMonoidHom_ker] at hk
  exact hk

theorem normalizer_eq_join_of_pslFour_sylow_centralizes {T : Sylow 2 G} {L : Subgroup G}
    (e : L ≃* PSLFour) (hT : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hfix : (T : Subgroup G) ≤ centralizer (componentSylow T L : Set G)) :
    normalizer (L : Set G) = L ⊔ centralizer (L : Set G) := by
  obtain ⟨e₀⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K := GaloisField 2 2) (by rw [GaloisField.card 2 2 (by decide)]; decide)
  let e₁ := e.trans e₀
  let N := normalizer (L : Set G)
  let S := T.subtype hT
  obtain ⟨P, hP⟩ := componentSylow_isSylow hT
  let q := (QuotientGroup.mk' (MulAut.innerSubgroup L)).comp L.normalizerMonoidHom
  have hSk : (S : Subgroup N) ≤ q.ker := by
    intro s hs
    have hsf : ∀ x ∈ P, L.normalizerMonoidHom s x = x := by
      intro x hx
      have hxT : (x : G) ∈ componentSylow T L := hP ▸ mem_map_of_mem L.subtype hx
      apply Subtype.ext
      change (s : G) * (x : G) * (s : G)⁻¹ = x
      have hcomm : (x : G) * (s : G) = (s : G) * (x : G) := hfix hs x hxT
      rw [← hcomm, mul_inv_cancel_right]
    obtain ⟨a, _, ha⟩ := Theory.PSL2.SylowFixedQuotients.fixed_inner_transport e₁
      (P : Subgroup L)
      (Theory.PSL2.SylowFixedQuotients.alternating_sylow_fixed_inner
        (P.mapSurjective (f := e₁.toMonoidHom) e₁.surjective))
      (L.normalizerMonoidHom s) hsf
    change QuotientGroup.mk' (MulAut.innerSubgroup L) (L.normalizerMonoidHom s) = 1
    exact (QuotientGroup.eq_one_iff _).mpr ⟨a, ha.symm⟩
  have ht : IsPGroup 2 (MulAut.Outer L) :=
    outer_five_two.of_injective (MulAut.outerCongr e₁).toMonoidHom
      (MulAut.outerCongr e₁).injective
  have hcard : Nat.card q.range = 1 := by
    rcases (ht.to_subgroup q.range).card_eq_or_dvd with h | h
    · exact h
    · exfalso
      apply S.not_dvd_index
      apply h.trans
      rw [← index_ker]
      exact index_dvd_of_le hSk
  have hq : q = 1 := MonoidHom.range_eq_bot_iff.mp (Subgroup.card_eq_one.mp hcard)
  apply le_antisymm
  · intro g hg
    have hgq : q ⟨g, hg⟩ = 1 := by rw [hq]; rfl
    obtain ⟨a, ha⟩ := (QuotientGroup.eq_one_iff _).mp hgq
    have hc : (a : G)⁻¹ * g ∈ centralizer (L : Set G) := by
      intro x hx
      have he := congrArg (fun b : MulAut L => (b ⟨x, hx⟩ : G)) ha
      change (a : G) * x * (a : G)⁻¹ = g * x * g⁻¹ at he
      have hconj : ((a : G)⁻¹ * g) * x * ((a : G)⁻¹ * g)⁻¹ = x := by
        calc
          _ = (a : G)⁻¹ * (g * x * g⁻¹) * a := by group
          _ = x := by rw [← he]; group
      exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
    have hh := mul_mem_sup a.property hc
    simpa only [mul_inv_cancel_left] using hh
  · exact sup_le L.le_normalizer (centralizer_le_normalizer _)

theorem Geometry.normalizer_eq_join_of_pslFour {T : Sylow 2 G} {z : G}
    {L R : Subgroup G} {n : ℕ} (d : Geometry T L R n) (h : StandardSetup T z L)
    (e : L ≃* PSLFour)
    (hA : Nat.card (ActionImage (benderSpace T L)) = 21) :
    normalizer (L : Set G) = L ⊔ centralizer (L : Set G) := by
  apply normalizer_eq_join_of_pslFour_sylow_centralizes e h.sylow_normalizes
  apply (d.sylow_centralizes_space hA).trans
  apply centralizer_le
  apply le_trans _ (le_sup_right : omegaOneAmbient (componentSylow T L) ≤ benderSpace T L)
  intro x hx
  apply (omegaOneAmbient_le_iff _ _).mp le_rfl x hx
  let P := (componentSylow T L).subgroupOf L
  have hP₀ : IsPGroup 2 (componentSylow T L) := T.isPGroup'.of_injective
    (inclusion (show componentSylow T L ≤ (T : Subgroup G) from inf_le_left))
    (inclusion_injective _)
  have hP : IsPGroup 2 P := hP₀.of_equiv (subgroupOfEquivOfLe
    (show componentSylow T L ≤ L from inf_le_right)).symm
  have hsq := pslFour_two_subgroup_squares (P.map e.toMonoidHom)
    (hP.map e.toMonoidHom) ⟨e ⟨x, hx.2⟩, mem_map_of_mem _ hx⟩
  have he : e (⟨x, hx.2⟩ : L) ^ 2 = 1 := congrArg Subtype.val hsq
  have hxL : (⟨x, hx.2⟩ : L) ^ 2 = 1 :=
    e.injective (by simpa only [map_pow, map_one] using he)
  exact congrArg Subtype.val hxL

end CFSG.Quasithin.Chapter16.Intersections.Bender
