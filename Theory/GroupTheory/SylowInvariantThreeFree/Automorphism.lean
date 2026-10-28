module
public import Theory.GroupTheory.SylowInvariantThreeFree
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.SylowNormalizedResidual
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Three-free subgroups in a characteristic quotient action

Suppose an actual action contains the inner automorphisms of a centerless
finite group Q, whose outer group is a two-group. If Q has no nontrivial
three-free subgroup normalized by a full Sylow except two-groups, then a
two-perfect three-free invariant subgroup acts trivially. Two-perfection
first kills the outer action; restriction of the image Sylow to Inn(Q)
then supplies the literal Sylow needed by the model theorem.

Taking the two-residual gives containment of every three-free invariant
subgroup in the action kernel times the original Sylow. No surjectivity
onto all automorphisms and no splitting of the action kernel is assumed.
Source application: the Held branch needed in Aschbacher--Smith 8.3.8,
printed p.725, with the adequate 1.3.4 component catalogue.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
variable {G Q M : Type*} [Group G] [Finite G] [Group Q] [Finite Q] [Group M]

/-- A two-perfect three-free invariant subgroup acts trivially on the
actual centerless section, including its possible outer action. -/
theorem map_eq_bot_of_three_free_automorphism_model
    (T : Sylow 2 G) (f : G →* MulAut Q)
    (hi : MulAut.innerSubgroup Q ≤ f.range) (hz : center Q = ⊥)
    (ho : IsPGroup 2 (MulAut.Outer Q))
    (U : Subgroup G) (hn : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hp : IsPPerfect 2 U) (hthree : ¬ 3 ∣ Nat.card U)
    (e : Q ≃* M)
    (hmodel : ∀ (S : Sylow 2 M) (V : Subgroup M),
      (S : Subgroup M) ≤ normalizer (V : Set M) →
      ¬ 3 ∣ Nat.card V → IsPGroup 2 V) : U.map f = ⊥ := by
  let A := f.range
  let B := (MulAut.innerSubgroup Q).subgroupOf A
  let a := f.rangeRestrict
  let Y := U.map a
  let S := T.mapSurjective (f := a) f.rangeRestrict_surjective
  have hnY : (S : Subgroup A) ≤ normalizer (Y : Set A) :=
    (map_mono hn).trans (U.le_normalizer_map a)
  have hpY : IsPPerfect 2 Y := hp.of_surjective (a.subgroupMap U) (a.subgroupMap_surjective U)
  have hthreeY : ¬ 3 ∣ Nat.card Y := fun h =>
    hthree (h.trans (card_dvd_of_surjective (a.subgroupMap U) (a.subgroupMap_surjective U)))
  let o : Y →* MulAut.Outer Q :=
    ((QuotientGroup.mk' (MulAut.innerSubgroup Q)).comp A.subtype).comp Y.subtype
  have hoY : o = 1 := hpY.hom_eq_one_of_isPGroup ho o
  have hYB : Y ≤ B := by
    intro y hy
    exact (QuotientGroup.eq_one_iff (N := MulAut.innerSubgroup Q) y.val).mp
      (DFunLike.congr_fun hoY ⟨y,hy⟩)
  let b : Q ≃* B :=
    (MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot hz)).trans
      (subgroupOfEquivOfLe hi).symm
  have hY : Y = ⊥ := eq_bot_of_three_free_model S
    (inferInstance : B.Normal).isSubnormal hYB hnY hpY hthreeY (b.symm.trans e) hmodel
  have hm := congrArg (Subgroup.map A.subtype) hY
  rw [map_map,Subgroup.map_bot] at hm
  exact hm

/-- The original Sylow supplements the full action kernel on every
three-free invariant subgroup. -/
theorem le_ker_sup_sylow_of_three_free_automorphism_model
    (T : Sylow 2 G) (f : G →* MulAut Q)
    (hi : MulAut.innerSubgroup Q ≤ f.range) (hz : center Q = ⊥)
    (ho : IsPGroup 2 (MulAut.Outer Q))
    (U : Subgroup G) (hn : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hthree : ¬ 3 ∣ Nat.card U) (e : Q ≃* M)
    (hmodel : ∀ (S : Sylow 2 M) (V : Subgroup M),
      (S : Subgroup M) ≤ normalizer (V : Set M) →
      ¬ 3 ∣ Nat.card V → IsPGroup 2 V) : U ≤ f.ker ⊔ (T : Subgroup G) := by
  let R := (pResidual 2 U).map U.subtype
  have hnR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    hn.trans (normalizer_le_normalizer_characteristic_image U (pResidual 2 U))
  have hr3 : ¬ 3 ∣ Nat.card R := fun h =>
    hthree (h.trans (card_dvd_of_le (map_subtype_le _)))
  have hr := map_eq_bot_of_three_free_automorphism_model T f hi hz ho R hnR
    (isPPerfect_embedded_pResidual 2 U) hr3 e hmodel
  have hk : R ≤ f.ker := by
    intro r hrR
    exact mem_bot.mp (hr ▸ mem_map_of_mem f hrR)
  exact (le_embedded_pResidual_sup_sylow_of_normalizes T U hn).trans
    (sup_le_sup_right hk _)
end Theory.GroupTheory
