module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Inspection.HigherRankOne
public import Theory.SpecificGroups.PSL3.BinaryCubicRankParity
public import Theory.GroupTheory.PerfectCentralCoverRank
public import Theory.GroupTheory.SolvableResidual
public import Theory.GroupTheory.SimpleSubgroupSmallIndex
public import Theory.SpecificGroups.SL3.OddFieldRadicalNormalizer

/-!
# The binary linear-three endpoint on the original component

The genuine odd-degree star quotient also identifies J/O₂(J): the central
comparison kernel has order dividing three, and the cyclic cubic Sylow
subgroups exclude its three-part. The quotient comparison retains its
literal map on representatives.

The solvable residual of C_M(A) acts trivially on V, because the plane-action
quotient has order dividing six. Its order is therefore prime to three.
Transport this fact to the full radical normalizer in the star component.
The marked cubic survives in that normalizer, and the higher-field radical
calculation forces degree one. The final theorem applies this reduction to
both remaining C.2.7 moved-section rows and identifies the actual J/O₂(J)
with SL₃(2). No classification of the full two-core is asserted here.

Source: Aschbacher--Smith 13.3.12, printed pp.889--890.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

noncomputable def Context.odd_linearThree_coreEquiv (_s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J)
    (F : BinaryField) (ho : Odd F.degree)
    (e : starImage J ((L ⊔ T).pCoreIn 2) J ≃* SL(3,F.Carrier)) :
    (J ⧸ pCore 2 J) ≃* SL(3,F.Carrier) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let c : PerfectCentralCovering.Cover (J ⧸ pCore 2 J) SL(3,F.Carrier) :=
    { toMonoidHom := e.toMonoidHom.comp (coreToStar j.input.normalizes)
      surjective := e.surjective.comp (coreToStar_surjective j.input.normalizes)
      isPerfect := j.input.quasisimple.toIsPerfect
      ker_le_center := by
        rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
        exact ChapterC.C27Source.coreToStar_ker_central_from_source j.input }
  have hz : center SL(3,F.Carrier) = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rw [Atlas.ExceptionalSupport.card_sl_center,Fintype.card_fin,F.card_eq]
    exact Nat.BinaryTorusParity.coprime_three_sub_one ho
  let a : SL(3,F.Carrier) ≃* PSL(3,F.Carrier) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hz.symm)
  have hr : primeRank 3 SL(3,F.Carrier) ≤ 1 := by
    rw [primeRank_equiv 3 a]
    exact Matrix.PSL3.BinaryCubicRankParity.rank_le_one_of_odd F.card_eq ho
  have hn : ¬ 3 ∣ Nat.card c.toMonoidHom.ker :=
    c.not_dvd_card_multiplier_of_odd_of_primeRank_le_one (by decide) hr
  have hd : Nat.card c.toMonoidHom.ker ∣ 3 := by
    have hh := card_dvd_of_le c.ker_le_center
    rcases ChapterC.C27Source.coreQuotient_center_card_from_source j.input with hc | hc
    · rw [hc] at hh
      exact hh.trans (one_dvd _)
    · rwa [hc] at hh
  have hk : c.toMonoidHom.ker = ⊥ := Subgroup.card_eq_one.mp
    ((Nat.dvd_prime Nat.prime_three).mp hd |>.resolve_right (fun hh => hn (by rw [hh])))
  exact MulEquiv.ofBijective c.toMonoidHom ⟨c.toMonoidHom.ker_eq_bot_iff.mp hk,c.surjective⟩

theorem Context.odd_linearThree_coreEquiv_mk (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J)
    (F : BinaryField) (ho : Odd F.degree)
    (e : starImage J ((L ⊔ T).pCoreIn 2) J ≃* SL(3,F.Carrier)) (x : J) :
    s.odd_linearThree_coreEquiv d J j F ho e (QuotientGroup.mk' (pCore 2 J) x) =
      e (toStarImage J ((L ⊔ T).pCoreIn 2) x) := by rfl

theorem Context.plane_solvableResidual_centralizes (s : Context T L V) (d : MarkedPlane V) :
    (solvableResidual (centralizer (d.A : Set G) ⊓ normalizer (L : Set G) : Subgroup G)).map
      (centralizer (d.A : Set G) ⊓ normalizer (L : Set G)).subtype ≤
        centralizer (V : Set G) := by
  let M := centralizer (d.A : Set G) ⊓ normalizer (L : Set G)
  let f := s.planeCentralizerAction d
  let : Group.IsSolvable (M ⧸ f.ker) := Group.isSolvable_of_card_le_six
    (Nat.le_of_dvd (by decide) (s.planeCentralizerAction_quotient_card_dvd_six d))
  have h := solvableResidual_le_of_solvable_quotient f.ker
  rw [s.planeCentralizerAction_ker d] at h
  rintro _ ⟨x,hx,rfl⟩
  exact h hx

theorem Context.plane_solvableResidual_coprime_three (s : Context T L V) (d : MarkedPlane V) :
    Nat.Coprime 3 (Nat.card (solvableResidual
      (centralizer (d.A : Set G) ⊓ normalizer (L : Set G) : Subgroup G))) := by
  let M := centralizer (d.A : Set G) ⊓ normalizer (L : Set G)
  have hd := card_dvd_of_le (s.plane_solvableResidual_centralizes d)
  rw [card_map_of_injective M.subtype_injective] at hd
  exact s.module_centralizer_coprime_three.of_dvd_right hd

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers

namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open Subgroup Theory.GroupTheory
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

private theorem residual_coprime_of_injective {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Injective f)
    (hc : Nat.Coprime 3 (Nat.card (solvableResidual B))) :
    Nat.Coprime 3 (Nat.card (solvableResidual A)) := by
  have hd := card_dvd_of_le (map_solvableResidual_le f)
  rw [card_map_of_injective hf] at hd
  exact hc.of_dvd_right hd

private theorem residual_coprime_of_surjective {A B : Type*} [Group A] [Finite A] [Group B]
    (f : A →* B) (hf : Function.Surjective f)
    (hc : Nat.Coprime 3 (Nat.card (solvableResidual A))) :
    Nat.Coprime 3 (Nat.card (solvableResidual B)) := by
  rw [←map_solvableResidual_eq f hf]
  exact hc.of_dvd_right (card_map_dvd _ _)

theorem Context.plane_starM_solvableResidual_coprime_three (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) :
    Nat.Coprime 3 (Nat.card (solvableResidual (starM J ((L ⊔ T).pCoreIn 2)
      (centralizer (d.A : Set G) ⊓ normalizer (L : Set G))))) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let M := centralizer (d.A : Set G) ⊓ normalizer (L : Set G)
  let B := (M ⊓ J).subgroupOf (J ⊔ Q)
  let f : B →* M := {
    toFun x := ⟨x.val.val,x.property.1⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hi : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : M => (z : G)) h))
  have hc := residual_coprime_of_injective f hi (s.plane_solvableResidual_coprime_three d)
  let q := QuotientGroup.mk' (starKernel J Q)
  exact residual_coprime_of_surjective (q.subgroupMap B) (q.subgroupMap_surjective B) hc

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers

namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open Subgroup Theory.GroupTheory
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource Representation Representation.BinaryOffender
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

/-- Every surviving SL₃ field is binary on the original plane component. -/
theorem Context.linearThree_star_degree_one (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J) (F : BinaryField)
    (e : starImage J ((L ⊔ T).pCoreIn 2) J ≃* SL(3,F.Carrier)) : F.degree = 1 := by
  have ho := s.linearThree_star_odd d J j F e
  by_contra he
  have hn : 1 < F.degree := by have := F.degree_pos; omega
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let C := starImage J Q J
  let U := starImage J Q Q
  let M := centralizer (d.A : Set G) ⊓ normalizer (L : Set G)
  let P := starM J Q M
  let R := (U.subgroupOf C).map e.toMonoidHom
  let N := normalizer (U.subgroupOf C : Set C)
  have hcard : 4 ≤ Nat.card F.Carrier := by
    rw [F.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ F.degree)
  have hlarge : 40320 < Nat.card C := by
    rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear]
    have hh : 4^3*(4^3-1)*(4^2-1) ≤
        Nat.card F.Carrier ^ 3 * (Nat.card F.Carrier ^ 3 - 1) *
          (Nat.card F.Carrier ^ 2 - 1) := by gcongr
    norm_num at hh
    omega
  obtain ⟨hR,hNP⟩ := ChapterC.C27Source.star_intersection_placement_from_source_of_large_order
    j.input hlarge
  let a : N ≃* normalizer (R : Set SL(3,F.Carrier)) :=
    (e.subgroupMap N).trans (MulEquiv.subgroupCongr
      (map_equiv_normalizer_eq (U.subgroupOf C) e))
  have hc : Nat.Coprime 3 (Nat.card (solvableResidual N)) := by
    let f : N →* P := {
      toFun x := ⟨x.val.val,hNP x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    exact residual_coprime_of_injective f
      (fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : P => (z : StarQuotient J Q)) h)))
      (s.plane_starM_solvableResidual_coprime_three d J)
  have hc' := residual_coprime_of_surjective a.toMonoidHom a.surjective hc
  obtain ⟨n,hnJ,hnL,horder,hmark⟩ := s.component_marked_cubic_order_three d J j
  have hnQ : n.val ∈ normalizer (Q : Set G) :=
    normalizer_le_normalizer_characteristic_image (L ⊔ (T : Subgroup G))
      (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
        ((L ⊔ (T : Subgroup G)).le_normalizer (mem_sup_left hnL))
  let x : J := ⟨n.val,hnJ⟩
  let y := toStarImage J Q x
  have hyU : (y : StarQuotient J Q) ∈ normalizer (U : Set (StarQuotient J Q)) := by
    apply (Q.subgroupOf (J ⊔ Q)).le_normalizer_map (QuotientGroup.mk' (starKernel J Q))
    apply mem_map_of_mem
    rw [←subgroupOf_normalizer_eq (show Q ≤ J ⊔ Q from le_sup_right)]
    exact hnQ
  have hyN : y ∈ N := by
    rw [mem_normalizer_iff]
    intro z
    exact mem_normalizer_iff.mp hyU (z : StarQuotient J Q)
  have hyorder : orderOf y = 3 := by
    rw [←e.orderOf_eq]
    change orderOf (e (toStarImage J Q x)) = 3
    rw [←s.odd_linearThree_coreEquiv_mk d J j F ho e x,MulEquiv.orderOf_eq]
    let q := QuotientGroup.mk' (pCore 2 J)
    have hq : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
    have hx : orderOf x = 3 := (Subgroup.orderOf_coe x).symm.trans horder
    exact (q.orderOf_map_eq_of_coprime_of_isPGroup_ker hq x (by rw [hx]; decide)).trans hx
  have h3 : 3 ∣ Nat.card (normalizer (R : Set SL(3,F.Carrier))) := by
    rw [←Nat.card_congr a.toEquiv]
    exact hyorder ▸ Subgroup.orderOf_dvd_natCard N hyN
  exact he (Matrix.PSL3.LinearThree.RadicalNormalizer.degree_eq_one_of_cubic_and_residual_coprime
    R (hR.map_equiv e) F.degree_pos F.card_eq ho h3 hc')

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers

namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open Subgroup Theory.GroupTheory
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource Representation.BinaryOffender
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

/-- The actual intrinsic two-core quotient is the binary linear-three group. -/
theorem Context.binary_linearThree_core_model (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J) :
    Nonempty ((J ⧸ pCore 2 J) ≃* SL(3,ZMod 2)) := by
  have hmodel (F : BinaryField)
      (e : starImage J ((L ⊔ T).pCoreIn 2) J ≃* SL(3,F.Carrier)) :
      Nonempty ((J ⧸ pCore 2 J) ≃* SL(3,ZMod 2)) := by
    have hd := s.linearThree_star_degree_one d J j F e
    have hc : Nat.card F.Carrier = 2 := by rw [F.card_eq,hd,pow_one]
    let := Fintype.ofFinite F.Carrier
    let k : F.Carrier ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F.Carrier Nat.prime_two
      (by simpa only [Nat.card_eq_fintype_card] using hc)).symm
    exact ⟨(s.odd_linearThree_coreEquiv d J j F (hd ▸ (by decide : Odd 1)) e).trans
      (Atlas.fieldEquivSL 3 k)⟩
  obtain ⟨c,hc⟩ := s.odd_linearThree_moved_section d J j
  obtain ⟨hK,_⟩ := ChapterC.C27Source.star_moved_section_from_source j.input
  cases hc with
  | natural F _ a => exact hmodel F ((subgroupOfEquivOfLe hK).symm.trans a.groupEquiv)
  | double F _ a =>
    rcases a with ⟨a,_,_⟩
    exact hmodel F ((subgroupOfEquivOfLe hK).symm.trans a)

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
