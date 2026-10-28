module
public import Theory.Representation.SL3.SmallCentralQuotient
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryRadicalBounds

/-!
# The full normalizer of the original secondary radical

The second center of R₂ is exactly U=Z(Q). Its elements centralize the
original dual quotient, so the faithful KS-action kernel puts them in Q.
A noncentral dual-axis element has a commutator row of order |F|², while
the original root has order at most |F|. Splitting over the two elementary
lifts therefore rules out any further central elements modulo the root.
Conversely the point radical acts trivially on U modulo that root.

Since U is characteristic in R₂ and H=N_G(U) by maximal two-locality,
N_G(R₂)≤H. This proves 4.3.14(1), and the checked Sylow/core argument now
gives relative radicality and O₂(K_Z T)≤R₂ without a normalizer premise.
NonblockSecondaryNormalizerApplications supplies their literal use in the
corrected source constructor and the linear-four reduction.

Strict enlargement by O₂(K_Z), the original MS witness and simultaneous
markings, the earlier A₅ application and the final representation
contradiction remain with qt-d-1222-rankone-uniqueness-nonblock.
Source: Aschbacher--Smith, original 4.3.14(1)--(3), pp.617--618;
C.1.35(2), pp.137--138, for the dual-axis centralizer calculation.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open Matrix.PSL3.LinearThree
open Representation.SL3ParabolicNatural
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ} {d : MSData c n}
namespace RootCoordinates
variable (m : RootCoordinates d)
include m

omit [Finite G] in
/-- The literal source root has at most one defining-field dimension. -/
theorem root_card_le : Nat.card (root c) ≤ Nat.card d.field.Carrier := by
  let f : root c → d.field.Carrier := fun z =>
    (m.coordinates ⟨z,d.root_le_center z.property⟩).toAdd 0
  apply Nat.card_le_card_of_injective f
  intro x y he
  apply Subtype.ext
  have hxy : (⟨x,d.root_le_center x.property⟩ : U c) = ⟨y,d.root_le_center y.property⟩ := by
    apply m.coordinates.injective
    apply Multiplicative.toAdd.injective
    obtain ⟨a,ha⟩ := (m.root_coordinates ⟨x,d.root_le_center x.property⟩).mp x.property
    obtain ⟨b,hb⟩ := (m.root_coordinates ⟨y,d.root_le_center y.property⟩).mp y.property
    have hab : a = b := by
      change (m.coordinates ⟨x,d.root_le_center x.property⟩).toAdd 0 =
        (m.coordinates ⟨y,d.root_le_center y.property⟩).toAdd 0 at he
      simpa only [ha,hb,Pi.smul_apply,smul_eq_mul,Matrix.cons_val_zero,mul_one] using he
    rw [ha,hb,hab]
  exact congrArg (fun z : U c => (z : G)) hxy

/-- No new central elements of Q arise after killing the original root. -/
theorem core_central_mod_root (hn : 1 < n) (q : Q c)
    (hq : ∀ x : Q c, ⁅(q : G),(x : G)⁆ ∈ root c) : (q : G) ∈ U c := by
  obtain ⟨p,hp,hk,he,hel⟩ := d.exists_elementary_dual_lifts
  let := conjMulDistribMulActionOfLeNormalizer (K c) (Q c) d.doubleDual.2.1
  have hc : p.ker = center (Q c) := hk.trans
    ((center (Q c)).comap_map_eq_self_of_injective (Q c).subtype_injective)
  have hsmall : Nat.card ((root c).subgroupOf (Q c)) < (Nat.card d.field.Carrier)^2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (d.root_le_center.trans (map_subtype_le _))).toEquiv]
    apply m.root_card_le.trans_lt
    have hF : 1 < Nat.card d.field.Carrier := by
      rw [d.field.card_eq,d.degree_eq]
      exact one_lt_pow₀ (by decide) (by omega)
    simpa only [pow_one] using (Nat.pow_lt_pow_right hF (show 1 < 2 by decide))
  have h := dual_small_central_quotient (linearThreeActor d.model)
    (d.model.surjective.comp (QuotientGroup.mk'_surjective _)) p hp hc
    (fun k x => he k x (k • x) rfl)
    (fun a b => by
      let A := (dualDiagonal a b).range.comap p
      let : IsElementaryAbelian 2 (A.map (Q c).subtype) := (hel a b).1
      exact IsElementaryAbelian.of_injective
        (A.equivMapOfInjective (Q c).subtype (Q c).subtype_injective).toMonoidHom
        (A.equivMapOfInjective (Q c).subtype (Q c).subtype_injective).injective)
    ((root c).subgroupOf (Q c)) hsmall q hq
  exact mem_map_of_mem _ h

/-- The point radical acts trivially on U modulo the original root. -/
theorem center_radical_commutator_le_root (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V) : ⁅U c,R₂ c⁆ ≤ root c := by
  apply commutator_le.mpr
  intro u hu r hr
  let x : U c := ⟨u,hu⟩
  let rH : (K c ⊔ S c : Subgroup G) := ⟨r,(radical_le_sylow c).trans le_sup_right hr⟩
  have hnorm : K c ⊔ S c ≤ normalizer (U c : Set G) :=
    ((sup_le (map_subtype_le _) inf_le_right).trans (core_normalized c)).trans
      (normalizer_le_normalizer_characteristic_image (Q c) (center (Q c)))
  let y := (U c).normalizerMonoidHom (inclusion hnorm rH) x
  have hy : (y : G) = r*u*r⁻¹ := normalizerMonoidHom_apply_apply_coe _ _ _
  have he : m.coordinates y = m.naturalAction rH (m.coordinates x) := by
    change m.coordinates y = m.coordinates ((U c).normalizerMonoidHom
      (inclusion hnorm rH) (m.coordinates.symm (m.coordinates x)))
    rw [m.coordinates.symm_apply_apply]
  obtain ⟨g,⟨z,hz,rfl⟩,hg⟩ := m.naturalAction_radical_le_rootPlane hn D
    (mem_map_of_mem m.naturalAction (show rH ∈ (R₂ c).subgroupOf (K c ⊔ S c) from hr))
  have hv : (m.coordinates y).toAdd = z.val.val.mulVec (m.coordinates x).toAdd := by
    rw [he,←hg]
    rfl
  have hz0 := (mem_pointLocalSL_iff d.field.Carrier z.val).mp z.property
  obtain ⟨h11,h12,h21,h22⟩ := (mem_pointRadicalSL_iff d.field.Carrier z).mp hz
  have hxroot : ((x*y⁻¹ : U c) : G) ∈ root c := by
    apply (m.root_coordinates _).mpr
    refine ⟨(m.coordinates (x*y⁻¹)).toAdd 0,?_⟩
    rw [map_mul,map_inv]
    simp only [toAdd_mul,toAdd_inv,←sub_eq_add_neg]
    rw [hv]
    ext i
    fin_cases i <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_three,
      hz0.2.1,hz0.2.2,h11,h12,h21,h22]
  simpa only [Subgroup.coe_mul,Subgroup.coe_inv,hy,commutatorElement_def,
    mul_inv_rev,inv_inv,mul_assoc] using hxroot

/-- A second-central element of R₂ acts trivially on an original invariant
dual quotient; its exact KS-action kernel puts it inside Q. -/
theorem second_center_le_core (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V) :
    (Subgroup.upperCentralSeries (R₂ c) 2).map (R₂ c).subtype ≤ Q c := by
  obtain ⟨A,hUA,hAQ,_,_,hA,_,_⟩ := d.exists_sylow_invariant_elementary_lift
  let a : invariantCoreLifts c := ⟨A,hUA,hAQ,le_sup_left.trans hA⟩
  obtain ⟨e,p,β,_,hp,hk,hβ,haction,_⟩ := d.exists_join_lift_quotient_action a hA
  rintro r ⟨z,hz,rfl⟩
  have hcomm (x : G) (hx : x ∈ R₂ c) : ⁅(z : G),x⁆ ∈ root c := by
    have hh := Subgroup.mem_upperCentralSeries_succ_iff.mp hz (⟨x,hx⟩ : R₂ c)
    rw [Subgroup.upperCentralSeries_one] at hh
    have hm := mem_map_of_mem (R₂ c).subtype hh
    rwa [m.radical_center_eq_root hn D] at hm
  let zH : (K c ⊔ S c : Subgroup G) := ⟨z,(radical_le_sylow c).trans le_sup_right z.property⟩
  have hβz : β zH = 1 := by
    apply MulEquiv.ext
    intro v
    obtain ⟨x,rfl⟩ := hp v
    rw [haction]
    change p (A.normalizerMonoidHom (inclusion hA zH) x) = p x
    apply p.div_mem_ker_iff.mp
    rw [hk]
    have hh := d.root_le_center (hcomm x (hAQ.le.trans (core_le_radical c) x.property))
    change ((A.normalizerMonoidHom (inclusion hA zH) x : A) : G) / (x : G) ∈ U c
    rw [normalizerMonoidHom_apply_apply_coe]
    change (z : G) * (x : G) * (z : G)⁻¹ / (x : G) ∈ U c
    simpa only [div_eq_mul_inv,commutatorElement_def] using hh
  have hzcore : zH ∈ pCore 2 (K c ⊔ S c : Subgroup G) := hβ ▸ hβz
  have hm := mem_map_of_mem (K c ⊔ S c).subtype hzcore
  exact (d.joinCore_eq hn).le hm

/-- The second center of the actual radical is exactly the original U=Z(Q).
Thus it is an intrinsic characteristic subgroup, not a selected module. -/
theorem radical_second_center_eq (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V) :
    (Subgroup.upperCentralSeries (R₂ c) 2).map (R₂ c).subtype = U c := by
  apply le_antisymm
  · rintro _ ⟨r,hr,rfl⟩
    have hrQ := m.second_center_le_core hn D (mem_map_of_mem _ hr)
    apply m.core_central_mod_root hn ⟨r,hrQ⟩
    intro q
    have hh := Subgroup.mem_upperCentralSeries_succ_iff.mp hr
      (⟨q,(core_le_radical c) q.property⟩ : R₂ c)
    rw [Subgroup.upperCentralSeries_one] at hh
    have hm := mem_map_of_mem (R₂ c).subtype hh
    rwa [m.radical_center_eq_root hn D] at hm
  · intro u hu
    refine ⟨⟨u,(map_subtype_le (center (Q c))).trans (core_le_radical c) hu⟩,?_,rfl⟩
    apply Subgroup.mem_upperCentralSeries_succ_iff.mpr
    intro r
    rw [Subgroup.upperCentralSeries_one]
    have hh := m.center_radical_commutator_le_root hn D
      (commutator_mem_commutator hu r.property)
    rw [←m.radical_center_eq_root hn D] at hh
    obtain ⟨x,hx,he⟩ := hh
    exact (show x = ⁅(⟨u,(map_subtype_le (center (Q c))).trans (core_le_radical c) hu⟩ : R₂ c),r⁆
      from Subtype.ext he) ▸ hx

omit m in
/-- Maximal two-locality identifies the normalizer of the original center. -/
theorem center_normalizer_eq (d : MSData c n)
    (D : Chapter12.Section02.ChosenModule T L V) : normalizer (U c : Set G) = c.H := by
  have hne : U c ≠ ⊥ := fun he => root_ne_bot c D (bot_unique (d.root_le_center.trans he.le))
  have hp : IsPGroup 2 (U c) := (T.isPGroup').to_le
    ((map_subtype_le _).trans ((core_le_sylow c).trans inf_le_left))
  exact (c.maximal.eq_of_le ⟨U c,hne,hp,rfl⟩
    ((core_normalized c).trans
      (normalizer_le_normalizer_characteristic_image (Q c) (center (Q c))))).symm

/-- Original 4.3.14(1): the second center forces radical normalizers into H. -/
theorem radical_normalizer_le_original (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V) : normalizer (R₂ c : Set G) ≤ c.H := by
  rw [←center_normalizer_eq d D,←m.radical_second_center_eq hn D]
  exact normalizer_le_normalizer_characteristic_image (R₂ c) (Subgroup.upperCentralSeries (R₂ c) 2)

/-- The full containment in 4.3.14(1), with the original secondary residual. -/
theorem radical_normalizer_source (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V) :
    normalizer (R₂ c : Set G) ≤ c.H ⊓ normalizer (secondary c : Set G) :=
  m.radical_normalizer_control hn D (m.radical_normalizer_le_original hn D)

/-- Original 4.3.14(2), valid in every overgroup of the same K₂S. -/
theorem radical_relative_core_source (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (J : Subgroup G) (hJ : secondary c ⊔ S c ≤ J) :
    (normalizer ((R₂ c).subgroupOf J : Set J)).pCoreIn 2 = (R₂ c).subgroupOf J :=
  radical_relative_core_of_normalizer_le (m.radical_normalizer_le_original hn D) J hJ

/-- Original 4.3.14(3)'s upper core bound, without a normalizer premise. -/
theorem enlarged_core_le_radical_source (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (J : Subgroup G) (hJ : secondary c ⊔ S c ≤ J) : J.pCoreIn 2 ≤ R₂ c :=
  enlarged_core_le_radical_of_normalizer_le (m.radical_normalizer_le_original hn D) J hJ

end RootCoordinates
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
