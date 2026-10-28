module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerElementary
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerCentralizer
public import Theory.SpecificGroups.SymmetricFourWreath.NormalElementaryGeometry

/-!
# Transvections on the original exceptional elementary cores

Every elementary subgroup of order sixteen in the source Sylow transports to
one of the four products of elementary fours in D₈ wr C₂. A rotation in the
first dihedral factor normalizes each product and fixes exactly eight elements.
Injective transport supplies a literal normalizer element, including for A₁
and A₂, whose fixed subgroup has index two.

Source: Aschbacher–Smith F.5.4(2), printed p.301.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
namespace ElementaryTransvections
open SymmetricFourWreath
private instance : Fintype P := Fintype.ofEquiv _ (RegularWreathProduct.equivProd D8 C2).symm
private instance : DecidableEq P := (RegularWreathProduct.equivProd D8 C2).injective.decidableEq
private instance (b c : Bool) : DecidablePred (·∈elementaryInP b c) := fun x =>
  decidable_of_iff _ (mem_elementaryInP b c x).symm

private def actor : P := pair (DihedralGroup.r 1,1)

private theorem plane_normal (b : Bool) (x y : D8) (hy : y∈plane b) : x*y*x⁻¹∈plane b := by
  exact (by decide +kernel : ∀ (b : Bool) (x y : D8), y∈plane b → x*y*x⁻¹∈plane b) b x y hy

private theorem actor_normalizes (b c : Bool) : actor∈normalizer (elementaryInP b c : Set P) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply le_antisymm
  · rintro x ⟨y,⟨a,ha,rfl⟩,rfl⟩
    refine ⟨(DihedralGroup.r 1*a.1*(DihedralGroup.r 1)⁻¹,a.2),⟨plane_normal _ _ _ ha.1,ha.2⟩,?_⟩
    change pair _ = pair (DihedralGroup.r 1,1) * pair a * (pair (DihedralGroup.r 1,1))⁻¹
    rw [←map_inv,←map_mul,←map_mul]
    apply congrArg pair
    apply Prod.ext
    · rfl
    · exact (mul_one _).symm.trans (congrArg (fun x => x * (1 : D8)) (one_mul a.2)).symm
  · rintro x ⟨a,ha,rfl⟩
    let v : D8 × D8 := ((DihedralGroup.r 1)⁻¹*a.1*DihedralGroup.r 1,a.2)
    refine ⟨pair v,⟨v,⟨?_,ha.2⟩,rfl⟩,?_⟩
    · change (DihedralGroup.r 1)⁻¹*a.1*DihedralGroup.r 1 ∈ plane b
      exact inv_inv (DihedralGroup.r (1 : ZMod 4)) ▸ plane_normal b (DihedralGroup.r 1)⁻¹ a.1 ha.1
    · change pair (DihedralGroup.r 1,1) * pair v * (pair (DihedralGroup.r 1,1))⁻¹ = pair a
      rw [←map_inv,←map_mul,←map_mul]
      apply congrArg pair
      apply Prod.ext
      · change DihedralGroup.r 1 * ((DihedralGroup.r 1)⁻¹*a.1*DihedralGroup.r 1) * (DihedralGroup.r 1)⁻¹ = a.1
        exact (show ∀ x y : D8, x*(x⁻¹*y*x)*x⁻¹=y by intro x y; group) _ _
      · simp [v]

private theorem actor_fixed_card (b c : Bool) :
    Nat.card ((centralizer ({actor} : Set P)).subgroupOf (elementaryInP b c)) = 8 := by
  let : DecidablePred (·∈(plane b).prod (plane c)) := fun x =>
    inferInstanceAs (Decidable (x.1∈plane b ∧ x.2∈plane c))
  let : Fintype ((plane b).prod (plane c)) := Subtype.fintype _
  let e : (plane b).prod (plane c) ≃* elementaryInP b c :=
    ((plane b).prod (plane c)).equivMapOfInjective pair pair_injective
  let f : {a : (plane b).prod (plane c) // a.val.1*DihedralGroup.r 1=DihedralGroup.r 1*a.val.1} ≃
      ((centralizer ({actor} : Set P)).subgroupOf (elementaryInP b c)) :=
    e.toEquiv.subtypeEquiv (fun a => by
      change _ ↔ pair a.val∈centralizer ({pair (DihedralGroup.r 1,1)} : Set P)
      rw [mem_centralizer_singleton_iff,←map_mul,←map_mul,pair_injective.eq_iff]
      exact (Prod.ext_iff.trans (by simp)).symm)
  rw [←Nat.card_congr f,Nat.card_eq_fintype_card]
  cases b <;> cases c <;> decide +kernel

private theorem fixed_card_map {X Y : Type*} [Group X] [Group Y]
    (B : Subgroup X) (j : X →* Y) (hj : Function.Injective j) (g : X) :
    Nat.card ((centralizer ({j g} : Set Y)).subgroupOf (B.map j)) =
      Nat.card ((centralizer ({g} : Set X)).subgroupOf B) := by
  let e := B.equivMapOfInjective j hj
  let f : ((centralizer ({g} : Set X)).subgroupOf B) ≃
      ((centralizer ({j g} : Set Y)).subgroupOf (B.map j)) :=
    e.toEquiv.subtypeEquiv (fun a => by
      change a.val∈centralizer ({g} : Set X) ↔ j a.val∈centralizer ({j g} : Set Y)
      rw [mem_centralizer_singleton_iff,mem_centralizer_singleton_iff,←map_mul,←map_mul]
      exact hj.eq_iff.symm)
  exact (Nat.card_congr f).symm

end ElementaryTransvections
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
include h

/-- Every elementary subgroup of order sixteen in the original T admits a
transvection induced by an element of T. -/
theorem normalizer_elementary_transvection (B : Subgroup G)
    (hB : B ≤ Source.sylowImage c i) (he : IsElementaryAbelian 2 B)
    (hc : Nat.card B = 16) :
    ∃ g∈Source.sylowImage c i, g∈normalizer (B : Set G) ∧
      ((centralizer ({g} : Set G)).subgroupOf B).index = 2 := by
  classical
  obtain ⟨e⟩ := normalizer_T_wreath c i z h
  let j : SymmetricFourWreath.P →* G :=
    (Source.sylowImage c i).subtype.comp e.symm.toMonoidHom
  have hj : Function.Injective j :=
    (Source.sylowImage c i).subtype_injective.comp e.symm.injective
  have hcomp : j.comp e.toMonoidHom = (Source.sylowImage c i).subtype := by
    ext x
    change (e.symm (e x)).val = x.val
    rw [e.symm_apply_apply]
  let B0 := (B.subgroupOf (Source.sylowImage c i)).map e.toMonoidHom
  let := he
  have he0 : IsElementaryAbelian 2 B0 := by
    let : IsElementaryAbelian 2 (B.subgroupOf (Source.sylowImage c i)) :=
      IsElementaryAbelian.subgroupOf hB
    exact IsElementaryAbelian.map _
  have hc0 : Nat.card B0 = 16 := by
    rw [card_map_of_injective e.injective,
      Nat.card_congr (subgroupOfEquivOfLe hB).toEquiv,hc]
  have hmap : B0.map j = B := by
    rw [map_map,hcomp,map_subgroupOf_eq_of_le hB]
  obtain ⟨a,b,hab⟩ := (SymmetricFourWreath.maximum_elementaryInP B0).mp
    ⟨le_top,he0,fun U _ hU =>
      (SymmetricFourWreath.elementaryInP_card_bound U hU).trans_eq hc0.symm⟩
  rw [hab] at hmap
  refine ⟨j ElementaryTransvections.actor,(e.symm ElementaryTransvections.actor).property,?_,?_⟩
  · rw [←hmap]
    exact le_normalizer_map j ⟨_,ElementaryTransvections.actor_normalizes a b,rfl⟩
  · have hfix : Nat.card ((centralizer ({j ElementaryTransvections.actor} : Set G)).subgroupOf B) = 8 := by
      rw [←hmap,ElementaryTransvections.fixed_card_map _ _ hj,
        ElementaryTransvections.actor_fixed_card]
    have hi := ((centralizer ({j ElementaryTransvections.actor} : Set G)).subgroupOf B).card_mul_index
    rw [hfix,hc] at hi
    omega

/-- The transvection clause of F.5.4 for the literal two endpoint cores. -/
theorem normalizer_A_transvection (t : G) (hf : FusionFacts c i z t) (b : Bool) :
    ∃ g∈normalizer (A c i b : Set G),
      ((centralizer ({g} : Set G)).subgroupOf (A c i b)).index = 2 := by
  have hAT : A c i b ≤ Source.sylowImage c i := by
    exact (A_le_TfImage c i z t hf b).trans ((TfImage_eq c i) ▸ inf_le_left)
  obtain ⟨g,_,hg,hi⟩ := normalizer_elementary_transvection c i z h (A c i b)
    hAT (hf.A_elementary b) (hf.A_card b)
  exact ⟨g,hg,hi⟩

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
