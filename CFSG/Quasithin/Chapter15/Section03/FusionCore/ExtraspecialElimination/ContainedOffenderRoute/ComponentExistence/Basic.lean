module
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.Inputs
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationCases.SymmetricThree

/-!
# Lifting and placing a component of the contained-offender span

A C-component of the star image lifts through the actual two-group kernel
inside J = localSpan A H. A noncentral cubic element in its quasisimple
star image then yields L = [L,Y₀]; containment in M would put this perfect
subgroup inside the solvable Y₀, a contradiction. Only Y₀ is assumed solvable.

The single quasisimple and two-quasisimple-factor cases construct such a
lift, transport the cubic witness through the actual model isomorphism,
and derive the H-star orbit bound from the existing component calculus.
The pure S₃ case is eliminated using its rank-two moved space. These are
conditional case lemmas, not an exhaustive B.5.6 classification or a proof
that J equals its component product. Cubic witnesses remain explicit here.

Adapted from the saved ContainedComponent probe in the preceding attempt.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.6,
printed p.105, and proof of 15.3.49(i), printed pp.1143–1144.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence
open ComponentReduction FactorGeneration ClassificationCases
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem lift_surjection {D : Type*} [Group D]
    (f : G →* D) (hf : Function.Surjective f) [Group.IsSolvable f.ker]
    (B : Subgroup D) (hB : B.IsCComponent) :
    ∃ K : Subgroup G, K.IsCComponent ∧ K.map f = B := by
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  obtain ⟨K, hK, he⟩ := (hB.map_equiv e.symm).exists_map_quotient_eq f.ker
  refine ⟨K, hK, ?_⟩
  have hm := congrArg (map e.toMonoidHom) he
  rw [map_map, map_map] at hm
  have hcomp : e.toMonoidHom.comp (QuotientGroup.mk' f.ker) = f := by
    ext x
    rfl
  have hinv : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id D := by
    ext x
    exact e.apply_symm_apply x
  rw [hcomp, hinv, map_id] at hm
  exact hm

/-- Lift inside the actual conjugate span, with exactly the specified star image. -/
theorem exists_lift (H A : Subgroup G) (hAH : A ≤ H)
    (B : Subgroup (starImage H (localSpan A H))) (hB : B.IsCComponent) :
    ∃ L : Subgroup G, L ≤ localSpan A H ∧
      (L.subgroupOf (localSpan A H)).IsCComponent ∧
      starImage H L = B.map (starImage H (localSpan A H)).subtype := by
  let J := localSpan A H
  have hJH : J ≤ H := conjugateSpanBy_le_self hAH
  let eJ := subgroupOfEquivOfLe hJH
  let f := spanStarProjection H A
  let : Group.IsNilpotent f.ker := (spanStarProjection_kernel_twoGroup H A).isNilpotent
  obtain ⟨K, hK, hmap⟩ := lift_surjection f (spanStarProjection_surjective H A) B hB
  let KJ := K.map eJ.toMonoidHom
  let L := KJ.map J.subtype
  have hLJ : L ≤ J := map_subtype_le KJ
  have hL : (L.subgroupOf J).IsCComponent := by
    change ((KJ.map J.subtype).comap J.subtype).IsCComponent
    rw [comap_map_eq_self_of_injective J.subtype_injective]
    exact hK.map_equiv eJ
  refine ⟨L, hLJ, hL, ?_⟩
  have hLH : L.subgroupOf H = K.map ((J.subgroupOf H).subtype) := by
    ext x
    constructor
    · rintro ⟨j, ⟨k, hk, rfl⟩, he⟩
      exact ⟨k, hk, Subtype.ext he⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨eJ k, ⟨k, hk, rfl⟩, rfl⟩
  change (L.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) = _
  rw [hLH, map_map, ← hmap, map_map]
  rfl

variable {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : PlacedInput κ H M Y V Y0 T ZS Z E)

/-- The cubic argument gives commutator generation; this excludes placement in M
because a perfect subgroup contained in the solvable Y₀ would be trivial. -/
theorem outside_of_cubic (L : Subgroup G)
    (hLJ : L ≤ localSpan d.selected.carrier H)
    (hL : (L.subgroupOf (localSpan d.selected.carrier H)).IsCComponent)
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (ho : (Set.range fun h : H ⧸ pCore 2 H =>
      (starImage H L).map (MulAut.conj h).toMonoidHom).ncard ≤ 2)
    (x : starImage H L) (hx : orderOf x = 3) (hn : x ∉ center (starImage H L)) :
    OutsideComponent H M Y0 d.selected.carrier L := by
  have hLH := hLJ.trans (conjugateSpanBy_le_self d.selected.le_local)
  have hlocal := localSpan_component_isCComponent d.selected.carrier H L
    d.selected.le_local hLJ hL
  have hYH : Y0 ≤ H := le_sup_left.trans d.base_le
  let : Group.IsSolvable Y0 := d.toLocalInput.residual_solvable
  have he := PerfectLifting.component_commutator_of_noncentral_cubic H M Y0 L
    hLH hYH hlocal d.toLocalInput.twoPerfect d.normalizer_eq d.core_le_m d.theta_eq
    hq ho x hx hn
  refine ⟨hLJ, hL, hq, ho, ?_, he⟩
  intro hLM
  have hLY : L ≤ Y0 := by
    rw [he]
    exact le_normalizer_iff_commutator_le_right.mp (d.normalizer_eq.symm ▸ hLM)
  have hsol : Group.IsSolvable (L.subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (inclusion hLY).comp (subgroupOfEquivOfLe hLH).toMonoidHom)
      ((inclusion_injective hLY).comp (subgroupOfEquivOfLe hLH).injective)
  exact hlocal.not_isSolvable hsol

/-- The pure symmetric-three alternative is impossible for the placed actor. -/
theorem not_symmetricThree
    (e : starImage H (localSpan d.selected.carrier H) ≃* Equiv.Perm (Fin 3))
    (hrank : Module.finrank (ZMod 2) (Representation.Coinvariants.ker
      (d.action.representation.comp (starImage H (localSpan d.selected.carrier H)).subtype)) = 2) :
    False :=
  d.no_solvableStarFactor (solvableStarFactorOfSymmetricThree H ZS Z
    d.selected.carrier d.action d.selected.le_local d.selected.best e hrank)

private theorem noncentral_cubic_transport {D F : Type*} [Group D] [Group F]
    (e : D ≃* F) (x : F) (hx : orderOf x = 3) (hn : x ∉ center F) :
    ∃ y : D, orderOf y = 3 ∧ y ∉ center D := by
  refine ⟨e.symm x, (e.symm.orderOf_eq x).trans hx, ?_⟩
  intro hc
  have hh := ((centerCongr e) ⟨e.symm x, hc⟩).property
  change e (e.symm x) ∈ center F at hh
  exact hn (by simpa only [MulEquiv.apply_symm_apply] using hh)

private theorem quasisimple_not_solvable {D : Type*} [Group D]
    [Theory.GroupTheory.IsQuasisimple D] : ¬ Group.IsSolvable D := by
  let : IsSimpleGroup (D ⧸ center D) := Theory.GroupTheory.IsQuasisimple.simple
  let : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
  exact Group.IsPerfect.not_isSolvable D

/-- A specified quotient component is lifted and placed using only its
intrinsic cubic witness and its orbit in the original H-star group. -/
theorem exists_of_star_component
    (B : Subgroup (starImage H (localSpan d.selected.carrier H)))
    (hB : B.IsCComponent) [Theory.GroupTheory.IsQuasisimple B]
    (ho : (Set.range fun h : H ⧸ pCore 2 H =>
      (B.map (starImage H (localSpan d.selected.carrier H)).subtype).map
        (MulAut.conj h).toMonoidHom).ncard ≤ 2)
    (x : B) (hx : orderOf x = 3) (hn : x ∉ center B) :
    ∃ L : Subgroup G, OutsideComponent H M Y0 d.selected.carrier L := by
  obtain ⟨L, hLJ, hL, he⟩ := exists_lift H d.selected.carrier d.selected.le_local B hB
  let e : starImage H L ≃* B := (MulEquiv.subgroupCongr he).trans
    (B.equivMapOfInjective (starImage H (localSpan d.selected.carrier H)).subtype
      (starImage H (localSpan d.selected.carrier H)).subtype_injective).symm
  have hq := Theory.GroupTheory.IsQuasisimple.of_mulEquiv e.symm
  obtain ⟨y, hy, hyn⟩ := noncentral_cubic_transport e x hx hn
  exact ⟨L, outside_of_cubic d L hLJ hL hq (he.symm ▸ ho) y hy hyn⟩

/-- In the single perfect-actor branch, construct a component inside J and
transport the model's cubic witness to its exact star image. -/
theorem exists_of_quasisimple_model {D : Type*} [Group D]
    [Theory.GroupTheory.IsQuasisimple D]
    (e : starImage H (localSpan d.selected.carrier H) ≃* D)
    (x : D) (hx : orderOf x = 3) (hn : x ∉ center D) :
    ∃ L : Subgroup G, OutsideComponent H M Y0 d.selected.carrier L := by
  let := Theory.GroupTheory.IsQuasisimple.of_mulEquiv e.symm
  obtain ⟨B, hB⟩ := exists_isCComponent_of_not_isSolvable
    (quasisimple_not_solvable (D := starImage H (localSpan d.selected.carrier H)))
  obtain ⟨L, hLJ, hL, _⟩ := exists_lift H d.selected.carrier d.selected.le_local B hB
  obtain ⟨f⟩ := PerfectLifting.starModel_of_quasisimple_model H d.selected.carrier L
    d.selected.le_local hLJ hL e
  obtain ⟨y, hy, hyn⟩ := noncentral_cubic_transport f x hx hn
  obtain ⟨hq, ho⟩ := PerfectLifting.starFactors_of_quasisimple_model H d.selected.carrier
    d.selected.le_local e L hLJ hL
  exact ⟨L, outside_of_cubic d L hLJ hL hq ho y hy hyn⟩

/-- Two perfect factors supply a component even when the module has an
indecomposable extension or a hyperplane. No assertion that J is perfect is used. -/
theorem exists_of_product_model {D F : Type*} [Group D] [Group F]
    [Theory.GroupTheory.IsQuasisimple D] [Theory.GroupTheory.IsQuasisimple F]
    (e : starImage H (localSpan d.selected.carrier H) ≃* D × F)
    (x : D) (hx : orderOf x = 3) (hn : x ∉ center D)
    (z : F) (hz : orderOf z = 3) (hzn : z ∉ center F) :
    ∃ L : Subgroup G, OutsideComponent H M Y0 d.selected.carrier L := by
  have hns : ¬ Group.IsSolvable (starImage H (localSpan d.selected.carrier H)) := by
    intro hs
    let := hs
    let : Group.IsSolvable (D × F) :=
      Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    exact quasisimple_not_solvable (D := D)
      (Group.isSolvable_of_surjective (f := MonoidHom.fst D F) Prod.fst_surjective)
  obtain ⟨B, hB⟩ := exists_isCComponent_of_not_isSolvable hns
  obtain ⟨L, hLJ, hL, _⟩ := exists_lift H d.selected.carrier d.selected.le_local B hB
  have hw : ∃ y : starImage H L, orderOf y = 3 ∧ y ∉ center (starImage H L) := by
    rcases PerfectLifting.starModel_of_product_model H d.selected.carrier L
        d.selected.le_local hLJ hL e with hf | hf
    · obtain ⟨f⟩ := hf
      exact noncentral_cubic_transport f x hx hn
    · obtain ⟨f⟩ := hf
      exact noncentral_cubic_transport f z hz hzn
  obtain ⟨y, hy, hyn⟩ := hw
  obtain ⟨hq, ho⟩ := PerfectLifting.starFactors_of_product_model H d.selected.carrier
    d.selected.le_local e L hLJ hL
  exact ⟨L, outside_of_cubic d L hLJ hL hq ho y hy hyn⟩

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence
