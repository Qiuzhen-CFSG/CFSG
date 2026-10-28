module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.Orbit
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification

/-!
# Minimal parabolics with a solvable contained base

The index argument uses only the actual quotient Y₀/O₂(Y₀) of order three,
its normalization by T, and the genuine Sylow intersection T ∩ L. The
subgroup P = Y₀*(T ∩ L)* is solvable because it lies in (Y₀T)*. Thus none
of these arguments needs solvability of M ∩ H.

The elementary index helpers are adapted from
`BinaryModels.ParabolicIdentification.Local`, whose public assembly requires
the stronger `LocalControl` record. All geometric recognition below reuses
that development's intrinsic theorems under the same component equivalence.
Containment and closure equality are explicit intermediate premises here;
the final reduction must discharge them.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49(l), printed pp.1144–1145.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels
open Subgroup ComponentReduction ModelReduction BinaryModels
open CFSG.Quasithin.Chapter1
open scoped IsMulCommutative

universe u
variable {G : Type u} [Group G] [Finite G]

namespace Parabolic
private theorem sylow_index (H T : Subgroup G) (hT : IsSylowIn 2 T H) :
    ¬ 2 ∣ T.relIndex H := by
  obtain ⟨S, rfl⟩ := hT
  simpa only [relIndex, subgroupOf, comap_map_eq_self_of_injective H.subtype_injective]
    using S.not_dvd_index

private theorem normal_sup_index (Y S : Subgroup G) [Y.Normal] :
    S.relIndex (Y ⊔ S) = S.relIndex Y := by
  have hmul : Y.relIndex S * S.relIndex (Y ⊔ S) = Y.relIndex S * S.relIndex Y := by
    calc
      _ = (S ⊓ Y).relIndex (Y ⊔ S) := by
        rw [← inf_relIndex_left (H := S) (K := Y)]
        exact relIndex_mul_relIndex _ _ _ inf_le_left le_sup_right
      _ = (S ⊓ Y).relIndex Y * Y.relIndex (Y ⊔ S) :=
        (relIndex_mul_relIndex _ _ _ inf_le_right le_sup_left).symm
      _ = _ := by simp [inf_relIndex_right, Nat.mul_comm]
  exact Nat.eq_of_mul_eq_mul_left
    (Nat.pos_of_ne_zero (index_ne_zero_of_finite : Y.relIndex S ≠ 0)) hmul

private theorem normalized_sup_index (Y S : Subgroup G)
    (hn : S ≤ normalizer (Y : Set G)) : S.relIndex (Y ⊔ S) = S.relIndex Y := by
  let J := Y ⊔ S
  let _ : (Y.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le Y.le_normalizer hn)
  have hi := normal_sup_index (Y.subgroupOf J) (S.subgroupOf J)
  rw [← subgroupOf_sup le_sup_left le_sup_right,
    relIndex_subgroupOf le_rfl, relIndex_subgroupOf le_sup_left] at hi
  exact hi

omit [Finite G] in
private theorem star_normalizes (H A B : Subgroup G)
    (hn : A ≤ normalizer (B : Set G)) :
    starImage H A ≤ normalizer (starImage H B : Set (H ⧸ pCore 2 H)) :=
  (map_mono ((comap_mono hn).trans (B.le_normalizer_comap H.subtype))).trans
    ((B.subgroupOf H).le_normalizer_map (QuotientGroup.mk' (pCore 2 H)))

private theorem star_cubic (H Y : Subgroup G) (hYH : Y ≤ H)
    (hY : Nat.card (Y ⧸ pCore 2 Y) = 3) :
    ∃ y : starImage H Y, orderOf y = 3 := by
  have hd : 3 ∣ Nat.card Y := hY ▸ (pCore 2 Y).index_dvd_card
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Y) 3 hd
  let f : Y →* H ⧸ pCore 2 H := (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hYH)
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 (((QuotientGroup.mk' (pCore 2 H)).comp (inclusion hYH)).ker)
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hYH)
  have ho : orderOf (f y) = 3 :=
    (f.orderOf_map_eq_of_coprime_of_isPGroup_ker hk y
      (hy ▸ (by decide : Nat.Coprime 2 3))).trans hy
  have hm : f y ∈ starImage H Y := ⟨⟨y, hYH y.property⟩, y.property, rfl⟩
  exact ⟨⟨f y, hm⟩, (Subgroup.orderOf_coe _).symm.trans ho⟩

private theorem normalized_sylow_index_three (H L Y T : Subgroup G)
    (hYH : Y ≤ H) (hYL : Y ≤ L)
    (hY : Nat.card (Y ⧸ pCore 2 Y) = 3)
    (hn : T ≤ normalizer (Y : Set G))
    (hs : IsSylowIn 2 (starImage H (T ⊓ L)) (starImage H L)) :
    (starImage H (T ⊓ L)).relIndex
      (ModelExclusions.componentParabolic H L Y T) = 3 := by
  let S := starImage H (T ⊓ L)
  let D := starImage H Y
  let P := ModelExclusions.componentParabolic H L Y T
  have hDP : D ≤ P := le_sup_left
  have hSP : S ≤ P := le_sup_right
  have hPL : P ≤ starImage H L :=
    sup_le (map_mono (comap_mono hYL)) (map_mono (comap_mono inf_le_right))
  have hS := hs.restrict hSP hPL
  have hi : S.relIndex P = S.relIndex D :=
    normalized_sup_index D S (star_normalizes H (T ⊓ L) Y (inf_le_left.trans hn))
  have hdiv : S.relIndex P ∣ Nat.card Y := by
    rw [hi]
    exact (relIndex_dvd_card S D).trans
      (((Y.subgroupOf H).card_map_dvd (QuotientGroup.mk' (pCore 2 H))).trans
        ((Nat.card_congr (subgroupOfEquivOfLe hYH).toEquiv).dvd))
  have hcard : Nat.card (pCore 2 Y) * 3 = Nat.card Y := by
    simpa only [Subgroup.index, hY] using (pCore 2 Y).card_mul_index
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := Y)).exists_card_eq
  rw [← hcard, hn] at hdiv
  have hc : (S.relIndex P).Coprime 2 :=
    ((Nat.prime_two.coprime_iff_not_dvd).mpr (sylow_index P S hS)).symm
  have hd3 : S.relIndex P ∣ 3 := (hc.pow_right n).dvd_of_dvd_mul_left hdiv
  rcases Nat.prime_three.eq_one_or_self_of_dvd _ hd3 with hone | hthree
  · have hDS : D ≤ S := hDP.trans (relIndex_eq_one.mp hone)
    obtain ⟨y, hy⟩ := star_cubic H Y hYH hY
    let x : S := ⟨y, hDS y.property⟩
    have hx : orderOf x = 3 := by
      rw [← Subgroup.orderOf_coe x, show (x : H ⧸ pCore 2 H) = y from rfl,
        Subgroup.orderOf_coe y, hy]
    have hc := (isSylowIn_iff.mp hS).1.orderOf_coprime (by decide : Nat.Coprime 2 3) x
    rw [hx] at hc
    exact (by decide : ¬ Nat.Coprime 3 3) hc |>.elim
  · exact hthree

omit [Finite G] in
private theorem minimal_of_index_three (S P : Subgroup G) (hSP : S ≤ P)
    (hi : S.relIndex P = 3) : S ⋖ P := by
  refine ⟨lt_of_le_of_ne hSP ?_, ?_⟩
  · intro he
    rw [he, relIndex_self] at hi
    contradiction
  · intro Q hSQ hQP
    have hm := relIndex_mul_relIndex S Q P hSQ.le hQP.le
    rw [hi] at hm
    have hp : (S.relIndex Q * Q.relIndex P).Prime := hm ▸ Nat.prime_three
    rcases (Nat.prime_mul_iff.mp hp) with h | h
    · exact hQP.not_ge (relIndex_eq_one.mp h.2)
    · exact hSQ.not_ge (relIndex_eq_one.mp h.2)

end Parabolic

namespace Input
variable {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E L upper : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : Input κ H M Y V Y0 T ZS Z E L upper)
include d

/-- The literal subgroup has index three above T₀*, is minimal there,
and is invariant under the original T*. -/
theorem parabolic_local (hclosed : localSpan L T = L) (hYL : Y0 ≤ L) :
    IsSylowIn 2 (starImage H (T ⊓ L)) (starImage H L) ∧
      ModelExclusions.componentParabolic H L Y0 T ≤ starImage H L ∧
      (starImage H (T ⊓ L)).relIndex (ModelExclusions.componentParabolic H L Y0 T) = 3 ∧
      starImage H (T ⊓ L) ⋖ ModelExclusions.componentParabolic H L Y0 T ∧
      starImage H T ≤ normalizer
        (ModelExclusions.componentParabolic H L Y0 T : Set (H ⧸ pCore 2 H)) := by
  have hs := (component_inter_sylow H T L d.sylowIn d.l_le d.component_in_H).2
  have hi := Parabolic.normalized_sylow_index_three H L Y0 T d.y_le hYL
    d.quotient_card d.normalizes hs
  exact ⟨hs, ParabolicIdentification.parabolic_le_component H L Y0 T hYL, hi,
    Parabolic.minimal_of_index_three _ _ le_sup_right hi,
    ParabolicIdentification.parabolic_invariant H L Y0 T d.normalizes hclosed⟩

/-- Solvability comes from Y₀T, without any assertion about M ∩ H. -/
theorem parabolic_solvable : Group.IsSolvable (ModelExclusions.componentParabolic H L Y0 T) := by
  let B := Y0 ⊔ T
  let := d.base_solvable
  let : Group.IsSolvable (B.subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe d.minimal.base_le).toMonoidHom)
      (subgroupOfEquivOfLe d.minimal.base_le).injective
  let : Group.IsSolvable (starImage H B) :=
    Group.isSolvable_of_surjective
      ((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective (B.subgroupOf H))
  exact Group.isSolvable_of_isSolvable_injective (inclusion_injective
    (show ModelExclusions.componentParabolic H L Y0 T ≤ starImage H B from
      sup_le (map_mono (comap_mono le_sup_left))
        (map_mono (comap_mono (inf_le_left.trans le_sup_right)))))

omit [Finite G] in
/-- Kernel containment justifies the image-intersection formula. -/
theorem parabolic_intersection (hYL : Y0 ≤ L) :
    ModelExclusions.componentParabolic H L Y0 T =
      (starImage H Y0 ⊔ starImage H T) ⊓ starImage H L :=
  ParabolicIdentification.parabolic_eq_intersection H L Y0 T d.sylowIn hYL d.normalizes

/-- The same projective component equivalence identifies P with a flag
stabilizer omitting precisely one proper dimension. -/
theorem linear_position (hclosed : localSpan L T = L) (hYL : Y0 ≤ L)
    (n : ℕ) [NeZero n] (lo : 3 ≤ n) (hi : n ≤ 5)
    (e : starImage H L ≃*
      Chapter2.ComponentRefinement.LieType.Binary.PSL n) :
    ∃ pos : ModelExclusions.BinaryGeometry.Position (starImage H L)
      (ModelExclusions.componentParabolic H L Y0 T) n, pos.model = e := by
  obtain ⟨hs, hPL, hindex, _, _⟩ := d.parabolic_local hclosed hYL
  exact ParabolicIdentification.Linear.exists_position _ _ _ n lo hi e hs
    le_sup_right hPL hindex

/-- The polar stabilizer in Sp₄(2), intersected with its derived subgroup. -/
theorem six_position (hclosed : localSpan L T = L) (hYL : Y0 ≤ L)
    (e : starImage H L ≃* Theory.SpecificGroups.SymmetricSix.A6) :
    ∃ (g : Theory.SpecificGroups.SymmetricSix.A6) (i : Bool),
      ((ModelExclusions.componentParabolic H L Y0 T).subgroupOf (starImage H L)).map
        (e.trans ParabolicIdentification.Six.alternatingEquivDerived).toMonoidHom =
      ((Theory.SpecificGroups.SymplecticFour.stabilizer
        (ParabolicIdentification.Six.markedSpace i)).map
          (MulAut.conj (Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv
            g.val)).toMonoidHom).subgroupOf
              (commutator (Theory.SpecificGroups.SymplecticFour.Sp (ZMod 2))) := by
  obtain ⟨hs, hPL, hindex, _, _⟩ := d.parabolic_local hclosed hYL
  exact ParabolicIdentification.Six.derived_position_intrinsic (starImage H L)
    (starImage H (T ⊓ L)) (ModelExclusions.componentParabolic H L Y0 T)
    e hs le_sup_right hPL hindex

/-- The root parabolic in G₂(2), intersected with its actual derived group. -/
theorem g2_position (hclosed : localSpan L T = L) (hYL : Y0 ≤ L)
    (e : starImage H L ≃* Atlas.G2.BinaryParabolicPair.DerivedModel) :
    ∃ (g : Atlas.G2.Model (ZMod 2)) (i : Fin 2),
      ((ModelExclusions.componentParabolic H L Y0 T).subgroupOf (starImage H L)).map
        e.toMonoidHom =
      ((if i = 0 then Atlas.G2.LieParabolicSetup.parabolic₁ else
        Atlas.G2.LieParabolicSetup.parabolic₂).map
          (MulAut.conj g).toMonoidHom).subgroupOf
            Atlas.G2.BinaryParabolicPair.DerivedModel := by
  obtain ⟨hs, hPL, hindex, _, _⟩ := d.parabolic_local hclosed hYL
  obtain ⟨S, _, hSP, hSPindex⟩ := ParabolicIdentification.model_inputs _ _ _ e
    hs le_sup_right hPL hindex
  let := d.parabolic_solvable
  let : Group.IsSolvable
      ((ModelExclusions.componentParabolic H L Y0 T).subgroupOf (starImage H L)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe hPL).toMonoidHom) (subgroupOfEquivOfLe hPL).injective
  exact ParabolicIdentification.g2_parabolic_identification S _ hSP hSPindex
    (Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective _))

end Input
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels
