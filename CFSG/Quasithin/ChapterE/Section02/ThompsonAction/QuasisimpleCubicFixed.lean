module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.QuasisimpleBaumann
public import Theory.SpecificGroups.SL2.CubicFixedVectors
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Tactic.Group
/-!
# Cubic fixed points from the actual single natural source

The marked quasisimple section supplies natural coordinates on [U,O²(G)].
A cubic with nontrivial original action has matrix order three, so it fixes
only the retained coordinate kernel. A seed lying in the moved group plus
the residual centralizer has exactly its residual-fixed cubic fixed points.
The central summand is retained and is never assumed trivial.

Source: Aschbacher--Smith E.2.3 and 10.2.3(4), pp.216--217 and746.
-/
public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
attribute [local instance] RankOneBaumann.semilinear_moved_elementary
set_option backward.isDefEq.respectTransparency false in
theorem quasisimple_linear_cubic_fixed_center
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (hqs : IsQuasisimple (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (s : MovedSection ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (F : BinaryField)
    (hnatural : IsLinearNatural (s.action.comp (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))).subtype) F 2)
    (Z : Subgroup G)
    (hseed : Z ≤ ⁅U,pResidual 2 G⁆ ⊔ centralizer (pResidual 2 G : Set G))
    (b : pResidual 2 G) (hb : b^3=1)
    (hmove : (b:G) ∉ centralizer (U : Set G)) :
    Z ⊓ centralizer ({(b:G)} : Set G) = Z ⊓ centralizer (pResidual 2 G : Set G) := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  let A := generalizedFitting Y
  let := offenderSubgroup_normal α
  let := hqs
  let : IsSimpleGroup (A ⧸ center A) := hqs.simple
  let : Nontrivial A := Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (center A))
  obtain ⟨e⟩ := hnatural
  have hF := perfect_linear_two_field_large F e.groupEquiv
  have hcore : pCore 2 H = ⊥ := by
    let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    rw [← pCore_map_iso 2 e,hU.quotient_pCore_eq_bot,Subgroup.map_bot]
  have hn : q.ker ≠ ⊤ := by
    intro he
    exact hJ (hker ▸ (he ▸ (le_top : elementaryAbelianMaxJ (T:Subgroup G) ≤ ⊤)))
  have hp := (minimalParabolic_reduced_image T hP q hq hcore hn).2
  have hff : IsFFModule α := by
    obtain hf | ⟨_,hff,_,_,_⟩ := lemma_B_2_7 U q hq hker T
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hf.1)).elim
    · exact hff
  have hL := (source_quasisimple_fitting_eq_residual (T.mapSurjective hq) hp Y
    (offender_generation (T.mapSurjective hq) hp α hff hcore).2 hqs).1
  have hX : A.map Y.subtype = (pResidual 2 G).map q := by
    rw [map_pResidual_of_surjective 2 q hq]
    exact hL
  let a : A := (A.equivMapOfInjective Y.subtype Y.subtype_injective).symm
    ⟨q b,hX.symm.le (mem_map_of_mem q b.property)⟩
  have ha : q b = (a:Y) := (congrArg Subtype.val
    ((A.equivMapOfInjective Y.subtype Y.subtype_injective).apply_symm_apply
      ⟨q b,hX.symm.le (mem_map_of_mem q b.property)⟩)).symm
  have ha3 : a^3=1 := by
    apply Subtype.ext
    apply Subtype.ext
    change ((a:Y):H)^3=1
    rw [←ha,←map_pow,show (b:G)^3=1 from congrArg (pResidual 2 G).subtype hb,map_one]
  have hane : a≠1 := by
    intro he
    apply hmove
    rw [←hker]
    change q (b:G)=1
    rw [ha,he]
    rfl
  have hord : orderOf (e.groupEquiv a)=3 := orderOf_eq_prime
    (by rw [←map_pow,ha3,map_one])
    (fun he => hane (e.groupEquiv.injective (he.trans e.groupEquiv.map_one.symm)))
  let W := ⁅U,pResidual 2 G⁆
  let C := centralizer (pResidual 2 G : Set G)
  let fv := sourceMovedQuotientMap U q hq hker Y A s (pResidual 2 G) hX _ e
  apply le_antisymm
  · intro z hz
    have hzprod : z ∈ (W : Set G)*(C : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left W C (by rw [normalizer_eq_top]; exact le_top)]
      exact hseed hz.1
    obtain ⟨w,hw,k,hk,rfl⟩ := hzprod
    have hbk : (b:G)*k*(b:G)⁻¹=k := by rw [hk b b.property,mul_inv_cancel_right]
    have hbw : (b:G)*w*(b:G)⁻¹=w := by
      apply mul_right_cancel (b := k)
      calc
        ((b:G)*w*(b:G)⁻¹)*k = ((b:G)*w*(b:G)⁻¹)*((b:G)*k*(b:G)⁻¹) := by rw [hbk]
        _ = (b:G)*(w*k)*(b:G)⁻¹ := by group
        _ = w*k := by rw [hz.2 b (Set.mem_singleton _),mul_inv_cancel_right]
    let v : Additive W := Additive.ofMul ⟨w,hw⟩
    have heq := sourceMovedQuotientMap_conjugation U q hq hker Y A s (pResidual 2 G) hX _ e b a ha v
    have hv : Additive.ofMul (MulAut.conjNormal (b:G) v.toMul)=v := by
      apply Additive.toMul.injective
      exact Subtype.ext hbw
    rw [hv] at heq
    have hf0 : fv v=0 := Matrix.SL2.cubic_fixed_eq_zero (e.groupEquiv a) hord (fv v) heq.symm
    have hwC := (sourceMovedQuotientMap_kernel U q hq hker Y A s (pResidual 2 G) hX _ e v).mp hf0
    exact ⟨hz.1,C.mul_mem hwC hk⟩
  · intro z hz
    exact ⟨hz.1,fun x hx => Set.mem_singleton_iff.mp hx ▸ hz.2 b b.property⟩
end CFSG.Quasithin.ChapterE.ThompsonAction
