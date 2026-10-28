module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.WreathOvergroup.SourcePair.Factors
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelLift

/-!
# Source inputs for the moving PSL₃(2) pair

The input retains the ambient Sylow subgroup, the actual relative C-component
and its actual star-image isomorphism, and a specified moving conjugation.
The index-two orbit and prime-to-three residual identities are the earlier
Chapter 1 outputs used on printed p.952. The marked local subgroup is
2-perfect with quotient by its two-core of order three or nine, as in
Notation 13.2.1 and the A₆/Â₆ local calculations. Its join with T is solvable.
These inputs contain no choice of parabolic and no compatibility assertion
about such a choice.

The residual identity proves L₁ ≤ K₀. Conjugation transports the second
component and its model, and the normalizer index proves the exact permutation
of both star factors. Sylow restriction gives the actual marking in H and H*,
while the two-core kernel preserves the non-two-group seed. These are the
inputs to projecting the solvable subgroup (L₁T)* into the two components.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.16(1), printed p.952 (PDF p.969), with the standing notation on
pp.946–947, 1.2.1(3), 1.2.2(a), 13.8.15 and F.9.18(5).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.WreathOvergroup.SourcePair
variable {G : Type*} [Group G]

/-- The extracted earlier source data; the parabolic selection is an output. -/
structure Input (H L₁ T K K₀ : Subgroup G) where
  ambientSylow : Sylow 2 G
  ambientSylow_eq : (ambientSylow : Subgroup G) = T
  base_le : L₁ ⊔ T ≤ H
  component_le : K ≤ H
  component : (K.subgroupOf H).IsCComponent
  quasisimple : IsQuasisimple (Source.starImage H K)
  model : Source.starImage H K ≃* Matrix.PSL3Two.PSL
  mover : G
  mover_mem : mover ∈ T
  mover_not_normalizes : mover ∉ normalizer (K : Set G)
  orbit_index : (normalizer (K.subgroupOf H : Set H)).index = 2
  orbit_eq : K₀ = K ⊔ K.conjBy mover
  generated : H = K₀ ⊔ L₁ ⊔ T
  residual : (primeToResidual 3 H).map H.subtype = K₀
  seed_twoPerfect : IsPPerfect 2 L₁
  seed_quotient_card : Nat.card (L₁ ⧸ pCore 2 L₁) = 3 ∨
    Nat.card (L₁ ⧸ pCore 2 L₁) = 9
  seed_normalized : T ≤ normalizer (L₁ : Set G)
  solvable_base : Group.IsSolvable (L₁ ⊔ T : Subgroup G)

namespace Input
variable {H L₁ T K K₀ : Subgroup G} (d : Input H L₁ T K K₀)
include d

theorem T_le : T ≤ H := le_sup_right.trans d.base_le

theorem seed_le_H : L₁ ≤ H := le_sup_left.trans d.base_le

theorem two : IsPGroup 2 T := d.ambientSylow_eq ▸ d.ambientSylow.isPGroup'

theorem orbit_le : K₀ ≤ H := by
  rw [← d.residual]
  exact map_subtype_le _

theorem orbit_normal : (K₀.subgroupOf H).Normal := by
  have he : K₀.subgroupOf H = primeToResidual 3 H := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le d.orbit_le, d.residual]
  rw [he]
  infer_instance

theorem seed_three_quotient : IsPGroup 3 (L₁ ⧸ pCore 2 L₁) := by
  rcases d.seed_quotient_card with h | h
  · exact IsPGroup.of_card (n := 1) (by simpa using h)
  · exact IsPGroup.of_card (n := 2) (by simpa using h)

theorem seed_not_two [Finite G] : ¬ IsPGroup 2 L₁ := by
  intro h
  obtain ⟨n, hn⟩ := (h.to_quotient (pCore 2 L₁)).exists_card_eq
  have hd : 3 ∣ Nat.card (L₁ ⧸ pCore 2 L₁) := by
    rcases d.seed_quotient_card with h | h <;> simp [h]
  rw [hn] at hd
  exact (by decide : ¬ 3 ∣ 2) ((by decide : Nat.Prime 3).dvd_of_dvd_pow hd)

theorem seed_le_orbit [Finite G] : L₁ ≤ K₀ :=
  LinearTwo.marked_le_orbit H K₀ L₁ d.seed_le_H d.seed_twoPerfect
    d.seed_three_quotient d.residual

theorem generated_by_orbit_T [Finite G] : H = K₀ ⊔ T := by
  rw [d.generated, sup_eq_left.mpr d.seed_le_orbit]

theorem orbit_eq_span : K₀ = conjugateSpanBy K T := by
  rw [d.orbit_eq]
  exact (orbit_eq_two_conjugates H K T d.component_le d.T_le d.orbit_index
    d.mover_mem d.mover_not_normalizes).symm

theorem sylow_marking [Finite G] : ∃ S : Sylow 2 H, (S : Subgroup H).map H.subtype = T := by
  have ht : (d.ambientSylow : Subgroup G) ≤ H := d.ambientSylow_eq.le.trans d.T_le
  refine ⟨d.ambientSylow.subtype ht, ?_⟩
  rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le ht, d.ambientSylow_eq]

theorem star_sylow_marking [Finite G] : ∃ S : Sylow 2 (Source.Hstar H),
    (S : Subgroup (Source.Hstar H)) = Source.starImage H T := by
  obtain ⟨S, hS⟩ := d.sylow_marking
  have he : (S : Subgroup H) = T.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hS, map_subgroupOf_eq_of_le d.T_le]
  refine ⟨S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H)), ?_⟩
  change (S : Subgroup H).map _ = _
  rw [he]
  rfl

theorem star_seed_not_two [Finite G] : ¬ IsPGroup 2 (Source.starImage H L₁) := by
  intro h
  let q := QuotientGroup.mk' (pCore 2 H)
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hp := h.comap_of_ker_isPGroup q hk
  have hl : L₁.subgroupOf H ≤ (Source.starImage H L₁).comap q := by
    intro x hx
    exact mem_map_of_mem q hx
  exact d.seed_not_two ((hp.to_le hl).of_equiv (subgroupOfEquivOfLe d.seed_le_H))


theorem component_ne_conjugate : K ≠ K.conjBy d.mover :=
  fun h => d.mover_not_normalizes (mem_normalizer_iff_map_conj_eq.mpr h.symm)

theorem conjugate_cases {s : G} (hs : s ∈ T) :
    K.conjBy s = K ∨ K.conjBy s = K.conjBy d.mover := by
  by_cases hn : s ∈ normalizer (K : Set G)
  · exact Or.inl (mem_normalizer_iff_map_conj_eq.mp hn)
  · have htH : (⟨d.mover, d.T_le d.mover_mem⟩ : H) ∉
        normalizer (K.subgroupOf H : Set H) := by
      rw [← subgroupOf_normalizer_eq d.component_le]
      exact d.mover_not_normalizes
    have hsH : (⟨s, d.T_le hs⟩ : H) ∉ normalizer (K.subgroupOf H : Set H) := by
      rw [← subgroupOf_normalizer_eq d.component_le]
      exact hn
    have he : (⟨d.mover, d.T_le d.mover_mem⟩ : H)⁻¹ * ⟨s, d.T_le hs⟩ ∈
        normalizer (K.subgroupOf H : Set H) :=
      (mul_mem_iff_of_index_two d.orbit_index).mpr (by simp [htH, hsH])
    rw [← subgroupOf_normalizer_eq d.component_le] at he
    have heq : K.conjBy (d.mover⁻¹ * s) = K := mem_normalizer_iff_map_conj_eq.mp he
    have hh := congrArg (fun B : Subgroup G => B.conjBy d.mover) heq
    rw [conjBy_mul, conjBy_inv'] at hh
    exact Or.inr hh

theorem factor_permutation {s : G} (hs : s ∈ T) :
    (K.conjBy s = K ∧ (K.conjBy d.mover).conjBy s = K.conjBy d.mover) ∨
    (K.conjBy s = K.conjBy d.mover ∧ (K.conjBy d.mover).conjBy s = K) := by
  have hcases : (K.conjBy d.mover).conjBy s = K ∨
      (K.conjBy d.mover).conjBy s = K.conjBy d.mover := by
    simpa only [conjBy_mul] using d.conjugate_cases (T.mul_mem hs d.mover_mem)
  have hne : K.conjBy s ≠ (K.conjBy d.mover).conjBy s := by
    intro h
    exact d.component_ne_conjugate
      (map_injective (MulAut.conj s).injective h)
  rcases d.conjugate_cases hs with h | h <;> rcases hcases with h' | h'
  · exact (hne (h.trans h'.symm)).elim
  · exact Or.inl ⟨h, h'⟩
  · exact Or.inr ⟨h, h'⟩
  · exact (hne (h.trans h'.symm)).elim

theorem star_factor_permutation (s : Source.Hstar H) (hs : s ∈ Source.starImage H T) :
    ((Source.starImage H K).map (MulAut.conj s).toMonoidHom = Source.starImage H K ∧
      (Source.starImage H (K.conjBy d.mover)).map (MulAut.conj s).toMonoidHom =
        Source.starImage H (K.conjBy d.mover)) ∨
    ((Source.starImage H K).map (MulAut.conj s).toMonoidHom =
        Source.starImage H (K.conjBy d.mover) ∧
      (Source.starImage H (K.conjBy d.mover)).map (MulAut.conj s).toMonoidHom =
        Source.starImage H K) := by
  obtain ⟨s, hs, rfl⟩ := hs
  have hJ := (conjugate_isCComponent H K d.component_le d.component
    (d.T_le d.mover_mem)).1
  rw [LinearTwo.starImage_conjBy H K d.component_le s.property,
    LinearTwo.starImage_conjBy H (K.conjBy d.mover) hJ s.property]
  rcases d.factor_permutation hs with h | h
  · exact Or.inl ⟨congrArg (Source.starImage H) h.1, congrArg (Source.starImage H) h.2⟩
  · exact Or.inr ⟨congrArg (Source.starImage H) h.1, congrArg (Source.starImage H) h.2⟩

theorem star_moves : ∃ s ∈ Source.starImage H T,
    (Source.starImage H K).map (MulAut.conj s).toMonoidHom =
      Source.starImage H (K.conjBy d.mover) := by
  refine ⟨QuotientGroup.mk' (pCore 2 H) ⟨d.mover, d.T_le d.mover_mem⟩,
    mem_map_of_mem _ d.mover_mem, ?_⟩
  exact LinearTwo.starImage_conjBy H K d.component_le (d.T_le d.mover_mem)

theorem star_seed_normalized : Source.starImage H T ≤
    normalizer (Source.starImage H L₁ : Set (Source.Hstar H)) := by
  rintro _ ⟨s, hs, rfl⟩
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (Source.starImage H L₁).map
    (MulAut.conj (QuotientGroup.mk' (pCore 2 H) s)).toMonoidHom = Source.starImage H L₁
  rw [LinearTwo.starImage_conjBy H L₁ d.seed_le_H s.property]
  exact congrArg (Source.starImage H)
    (mem_normalizer_iff_map_conj_eq.mp (d.seed_normalized hs))

theorem star_base_solvable : Group.IsSolvable
    (Source.starImage H L₁ ⊔ Source.starImage H T : Subgroup (Source.Hstar H)) := by
  rw [← LinearTwo.starImage_sup H L₁ T d.seed_le_H d.T_le]
  let := d.solvable_base
  let : Group.IsSolvable ((L₁ ⊔ T).subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe d.base_le).toMonoidHom)
      (subgroupOfEquivOfLe d.base_le).injective
  exact Group.isSolvable_of_surjective
    ((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective _)


theorem second_component : K.conjBy d.mover ≤ H ∧
    ((K.conjBy d.mover).subgroupOf H).IsCComponent :=
  conjugate_isCComponent H K d.component_le d.component (d.T_le d.mover_mem)

noncomputable def second_model :
    Source.starImage H (K.conjBy d.mover) ≃* Matrix.PSL3Two.PSL :=
  (LinearTwo.starConjugateEquiv H K d.component_le (d.T_le d.mover_mem)).symm.trans d.model

theorem second_quasisimple : IsQuasisimple (Source.starImage H (K.conjBy d.mover)) := by
  let := d.quasisimple
  exact IsQuasisimple.of_mulEquiv
    (LinearTwo.starConjugateEquiv H K d.component_le (d.T_le d.mover_mem))

theorem star_factor_disjoint [Finite G] :
    Disjoint (Source.starImage H K) (Source.starImage H (K.conjBy d.mover)) :=
  star_disjoint H K (K.conjBy d.mover) d.component_le d.second_component.1
    d.component d.second_component.2 d.component_ne_conjugate d.quasisimple
    d.second_quasisimple d.model

theorem star_factor_commute [Finite G] : ∀ x ∈ Source.starImage H K,
    ∀ y ∈ Source.starImage H (K.conjBy d.mover), Commute x y := by
  have h := LinearTwo.starImages_commute H K (K.conjBy d.mover) d.component_le
    d.second_component.1 d.component d.second_component.2 d.component_ne_conjugate
    d.quasisimple d.second_quasisimple
  intro x hx y hy
  exact (commutator_eq_bot_iff_le_centralizer.mp h hx y hy).symm


theorem star_seed_le [Finite G] : Source.starImage H L₁ ≤
    Source.starImage H K ⊔ Source.starImage H (K.conjBy d.mover) := by
  have h := map_mono (f := QuotientGroup.mk' (pCore 2 H))
    (subgroupOf_mono H d.seed_le_orbit)
  change Source.starImage H L₁ ≤ Source.starImage H K₀ at h
  rwa [d.orbit_eq, LinearTwo.starImage_sup H K (K.conjBy d.mover)
    d.component_le d.second_component.1] at h

theorem star_factors_subnormal [Finite G] : (Source.starImage H K).IsSubnormal ∧
    (Source.starImage H (K.conjBy d.mover)).IsSubnormal :=
  ⟨(starImage_isCComponent H K d.component).subnormal,
    (starImage_isCComponent H (K.conjBy d.mover) d.second_component.2).subnormal⟩

end Input
end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.WreathOvergroup.SourcePair

end
