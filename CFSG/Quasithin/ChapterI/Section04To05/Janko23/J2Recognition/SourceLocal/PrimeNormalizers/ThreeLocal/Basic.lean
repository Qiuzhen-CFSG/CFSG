module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.ConjugateGraph
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms
public import Theory.GroupTheory.PrimeOrderLift
public import Mathlib.GroupTheory.Complement

/-!
# Central-cover input to the source three-local calculation

The subgroups and quotients are the literal centralizer and normalizer of
the chosen order-three seed. Normality is relative to these overgroups.
`CentralizerCalculation` is a remaining source calculation, not an assertion
that a seed supplies it. It records the perfect central cover and two small
normalizer witnesses needed to repair the extension identification in
Aschbacher, *Sporadic Groups* (1994), 47.3, pp.261–262.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
variable {G : Type*} [Group G] [Finite G]

abbrev C (D : Seed G) := centralizer (D.X : Set G)
abbrev M (D : Seed G) := normalizer (D.X : Set G)
abbrev XC (D : Seed G) := D.X.subgroupOf (C D)
abbrev XM (D : Seed G) := D.X.subgroupOf (M D)
abbrev CM (D : Seed G) := (C D).subgroupOf (M D)

variable (D : Seed G)

theorem X_le_C : D.X ≤ C D := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : IsCyclic D.X := isCyclic_of_prime_card D.card_X
  intro x hx y hy
  exact Subtype.ext_iff.mp (mul_comm (⟨y, hy⟩ : D.X) ⟨x, hx⟩)

theorem C_le_M : C D ≤ M D := centralizer_le_normalizer _

theorem XC_le_center : XC D ≤ center (C D) := by
  intro x hx
  apply mem_center_iff.mpr
  intro c
  exact Subtype.ext (c.property x.val hx).symm

instance : (XC D).Normal where
  conj_mem x hx g := by
    have he := mem_center_iff.mp (XC_le_center D hx) g
    simpa only [he, mul_inv_cancel_right] using hx
instance : (XM D).Normal :=
  (normal_subgroupOf_iff_le_normalizer D.X.le_normalizer).mpr le_rfl

/-- The perfect cover and actual actors still to be constructed by the source
centralizer calculation. The field of order nine and its projective group do
not occur among these assumptions. -/
structure CentralizerCalculation (D : Seed G) where
  perfect : Group.IsPerfect (C D)
  alternatingQuotient : Nonempty ((C D ⧸ XC D) ≃* alternatingGroup (Fin 6))
  inverter : M D
  inverter_order : orderOf inverter = 2
  inverts_X : ∀ x : D.X, (inverter : G) * x * (inverter : G)⁻¹ = (x : G)⁻¹
  eight : ∃ s : M D, orderOf s = 8


namespace CentralizerCalculation
variable {D} (H : CentralizerCalculation D)

/-- The actual central quotient, followed by the chosen A₆ coordinates. -/
noncomputable def coverMap : C D →* alternatingGroup (Fin 6) :=
  H.alternatingQuotient.some.toMonoidHom.comp (QuotientGroup.mk' (XC D))

theorem coverMap_surjective : Function.Surjective H.coverMap :=
  H.alternatingQuotient.some.surjective.comp (QuotientGroup.mk'_surjective _)

theorem coverMap_ker : H.coverMap.ker = XC D := by
  ext x
  change H.alternatingQuotient.some (QuotientGroup.mk' (XC D) x) = 1 ↔ x ∈ XC D
  rw [MulEquiv.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff x

include H in
/-- The center is the literal copy of the seed, not an abstract cyclic factor. -/
theorem center_eq : center (C D) = XC D := by
  apply le_antisymm ?_ (XC_le_center D)
  intro x hx
  have he : H.coverMap x ∈ center (alternatingGroup (Fin 6)) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨c, rfl⟩ := H.coverMap_surjective y
    rw [← map_mul, ← map_mul, mem_center_iff.mp hx c]
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at he
  rw [← H.coverMap_ker]
  exact he

/-- The quotient by the intrinsic center is genuinely A₆. -/
noncomputable def centerQuotientEquiv :
    (C D ⧸ center (C D)) ≃* alternatingGroup (Fin 6) :=
  (QuotientGroup.quotientMulEquivOfEq H.center_eq).trans H.alternatingQuotient.some

include H in
theorem quasisimple : IsQuasisimple (C D) := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  exact { toIsPerfect := H.perfect
          simple := (MulEquiv.isSimpleGroup_congr H.centerQuotientEquiv).mpr inferInstance }

/-- The cover keeps the original quotient map in its definition. -/
noncomputable def cover : PerfectCentralCovering.Cover (C D) (alternatingGroup (Fin 6)) where
  toMonoidHom := H.coverMap
  surjective := H.coverMap_surjective
  isPerfect := H.perfect
  ker_le_center := by rw [H.coverMap_ker]; exact XC_le_center D

theorem cover_ker_center : H.cover.toMonoidHom.ker = center (C D) :=
  H.coverMap_ker.trans H.center_eq.symm

/-- Conjugation on the literal centralizer by elements of the literal normalizer. -/
def centralizerAction : M D →* MulAut (C D) :=
  (C D).normalizerMonoidHom.comp
    (inclusion ((normal_subgroupOf_iff_le_normalizer (C_le_M D)).mp inferInstance))

/-- Faithful descent through the perfect central cover, expressed in A₆ coordinates. -/
noncomputable def quotientAction : M D →* MulAut (alternatingGroup (Fin 6)) :=
  (H.cover.autMap H.cover_ker_center).comp (centralizerAction (D := D))

theorem quotientAction_apply (m : M D) (c : C D) :
    H.quotientAction m (H.coverMap c) =
      H.coverMap (centralizerAction (D := D) m c) :=
  H.cover.autMap_apply H.cover_ker_center _ _

theorem card_XC : Nat.card (XC D) = 3 := by
  rw [Nat.card_congr (subgroupOfEquivOfLe (X_le_C D)).toEquiv, D.card_X]

theorem card_XM : Nat.card (XM D) = 3 := by
  rw [Nat.card_congr (subgroupOfEquivOfLe D.X.le_normalizer).toEquiv, D.card_X]

/-- The centralizer of C inside M is precisely X, so descent loses only X. -/
theorem quotientAction_ker : H.quotientAction.ker = XM D := by
  ext m
  change H.cover.autMap H.cover_ker_center (centralizerAction (D := D) m) = 1 ↔
    (m : G) ∈ D.X
  rw [← map_one (H.cover.autMap H.cover_ker_center),
    (H.cover.autMap_injective H.cover_ker_center).eq_iff]
  constructor
  · intro hm
    have hcomm (c : C D) : (m : G) * (c : G) = (c : G) * m := by
      have he := congrArg (fun a : MulAut (C D) => ((a c : C D) : G)) hm
      change (m : G) * c * (m : G)⁻¹ = c at he
      exact mul_inv_eq_iff_eq_mul.mp he
    have hmC : (m : G) ∈ C D := by
      intro x hx
      exact (hcomm ⟨x, X_le_C D hx⟩).symm
    have hmZ : (⟨m, hmC⟩ : C D) ∈ center (C D) := by
      apply mem_center_iff.mpr
      intro c
      exact Subtype.ext (hcomm c).symm
    rw [H.center_eq] at hmZ
    exact hmZ
  · intro hm
    apply MulEquiv.ext
    intro c
    apply Subtype.ext
    change (m : G) * c * (m : G)⁻¹ = c
    rw [c.property m hm, mul_inv_cancel_right]

/-- The embedded centralizer acts by the actual inner automorphism of its
image under the central covering map. -/
theorem quotientAction_on_C (c : C D) :
    H.quotientAction ⟨c, C_le_M D c.property⟩ = MulAut.conj (H.coverMap c) := by
  apply MulEquiv.ext
  intro a
  obtain ⟨x, rfl⟩ := H.coverMap_surjective a
  rw [H.quotientAction_apply]
  change H.coverMap (c * x * c⁻¹) = _
  simp only [map_mul, map_inv, MulAut.conj_apply]


/-- The recorded involution is genuinely outside the centralizer. -/
theorem inverter_not_C : (H.inverter : G) ∉ C D := by
  intro hc
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : IsCyclic D.X := isCyclic_of_prime_card D.card_X
  obtain ⟨x, hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := D.X)
  have hfix : (H.inverter : G) * x * (H.inverter : G)⁻¹ = x := by
    rw [← hc x x.property, mul_inv_cancel_right]
  have he : x = x⁻¹ := Subtype.ext (hfix.symm.trans (H.inverts_X x))
  have hp : x ^ 2 = 1 := by
    calc
      x ^ 2 = x * x := pow_two x
      _ = x⁻¹ * x := congrArg (· * x) he
      _ = 1 := inv_mul_cancel x
  have hd := orderOf_dvd_of_pow_eq_one hp
  rw [hx, D.card_X] at hd
  norm_num at hd

/-- The action on X has order two, and the inverting actor makes it nontrivial. -/
theorem centralizer_index (H : CentralizerCalculation D) : (CM D).index = 2 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : IsCyclic D.X := isCyclic_of_prime_card D.card_X
  have hd := card_dvd_of_injective _
    (QuotientGroup.kerLift_injective D.X.normalizerMonoidHom)
  rw [normalizerMonoidHom_ker, ← index, IsCyclic.card_mulAut, D.card_X] at hd
  have hd' : (CM D).index ∣ 2 := by
    simpa only [Nat.totient_prime (by decide : Nat.Prime 3)] using hd
  rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd' with h | h
  · have hle : M D ≤ C D := relIndex_eq_one.mp h
    exact (H.inverter_not_C (hle H.inverter.property)).elim
  · exact h

/-- The actual source centralizer has order 1080. -/
theorem centralizer_card (H : CentralizerCalculation D) : Nat.card (C D) = 1080 := by
  have he := (XC D).index_mul_card
  change Nat.card (C D ⧸ XC D) * Nat.card (XC D) = Nat.card (C D) at he
  rw [Nat.card_congr H.alternatingQuotient.some.toEquiv, card_XC,
    nat_card_alternatingGroup] at he
  norm_num at he
  exact he.symm

/-- The normalizer order follows from its literal centralizer index. -/
theorem normalizer_card (H : CentralizerCalculation D) : Nat.card (M D) = 2160 := by
  have he := (CM D).index_mul_card
  rw [H.centralizer_index,
    Nat.card_congr (subgroupOfEquivOfLe (C_le_M D)).toEquiv,
    H.centralizer_card] at he
  omega

/-- The recorded involution generates a complement to the embedded centralizer. -/
theorem split : (CM D).IsComplement' (zpowers H.inverter) := by
  classical
  apply isComplement'_of_card_mul_and_disjoint
  · rw [Nat.card_congr (subgroupOfEquivOfLe (C_le_M D)).toEquiv,
      H.centralizer_card, Nat.card_zpowers, H.inverter_order, H.normalizer_card]
  · apply disjoint_iff.mpr
    apply bot_unique
    intro m hm
    obtain ⟨hmC, hmr⟩ := hm
    change m ∈ zpowers H.inverter at hmr
    rw [mem_zpowers_iff_mem_range_orderOf, H.inverter_order] at hmr
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hmr
    have hi' : i < 2 := Finset.mem_range.mp hi
    interval_cases i
    · simp
    · have hmC' : H.inverter ∈ CM D := by simpa using hmC
      exact (H.inverter_not_C hmC').elim

/-- Intrinsic components of M all centralize X; the perfect A₆ cover itself
is a component. Mapping back to G therefore gives exactly C. -/
theorem layer_image (H : CentralizerCalculation D) : (componentLayer (M D)).map (M D).subtype = C D := by
  have hinside : componentLayer (M D) = CM D := by
    apply le_antisymm
    · apply sSup_le
      intro K hK
      let : Group.IsPerfect K := hK.2.toIsPerfect
      let : Fact (Nat.Prime 3) := ⟨by decide⟩
      let : IsCyclic D.X := isCyclic_of_prime_card D.card_X
      have hcard : Nat.card (MulAut D.X) = 2 := by
        rw [IsCyclic.card_mulAut, D.card_X]; decide
      let : Fact (Nat.Prime 2) := ⟨by decide⟩
      let : IsCyclic (MulAut D.X) := isCyclic_of_prime_card hcard
      let f : K →* MulAut D.X := D.X.normalizerMonoidHom.comp K.subtype
      let : Group.IsPerfect f.range := Group.IsPerfect.range f
      intro k hk
      have he : f ⟨k, hk⟩ = 1 := congrArg Subtype.val
        (Subsingleton.elim (⟨f ⟨k, hk⟩, ⟨⟨k, hk⟩, rfl⟩⟩ : f.range) 1)
      have hker : k ∈ D.X.normalizerMonoidHom.ker := he
      rwa [normalizerMonoidHom_ker] at hker
    · apply le_sSup
      refine ⟨(inferInstance : (CM D).Normal).isSubnormal, ?_⟩
      let : IsQuasisimple (C D) := H.quasisimple
      exact IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe (C_le_M D)).symm
  rw [hinside, map_subgroupOf_eq_of_le (C_le_M D)]

end CentralizerCalculation
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
