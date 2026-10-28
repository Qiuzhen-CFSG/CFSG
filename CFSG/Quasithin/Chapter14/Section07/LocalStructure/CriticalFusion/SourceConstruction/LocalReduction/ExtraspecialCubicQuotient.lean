module
public import Theory.GroupTheory.NormalizedCubicSylowQuotient
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialCubicLifts

/-!
# The actual symmetric-three quotient of an escaping cubic overgroup

The selected reciprocal critical involution fixes exactly the center
of the extraspecial star residual. It therefore cannot centralize a
noncentral cubic star subgroup. The exact kernel of the restricted
star map lifts this movement to [Y,T] not contained in O₂(Y).
The three-coset action then constructs YT/O₂(YT) ≃ S₃.

Applying this to the literal order-four chief interval retains the
original escaping subgroup Y, its T-invariance, its normalization of L₁,
and its exact star kernel. Thus the S₃ quotient premise of source
14.5.3(2) is now discharged for that subgroup. The geometric containment
implication of 14.5.3(2) remains unproved here, so the interval is not yet
excluded and this is not the residual classification through 14.7.52.

Source: Aschbacher–Smith, 14.5.3(2), printed p.1013, the reducible Sylow
step in 14.7.9 and 14.7.15(2), pp.1045,1047, and 14.7.20(2), p.1049.
-/

public noncomputable section
open scoped commutatorElement
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The selected critical involution moves every normalized noncentral cubic
star subgroup, giving S₃ modulo the intrinsic two-core of its Sylow overgroup. -/
theorem extraspecial_cubic_sylow_quotient
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYK : Y ≤ K F)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hc : Nat.card (star F Y) = 3)
    (hZ : star F Y ≠ (center (pResidual 2 (HStar F.H))).map (pResidual 2 (HStar F.H)).subtype)
    (hker : ((starMap F).comp (inclusion hYH)).ker = pCore 2 Y)
    (hq : Nat.card (Y ⧸ pCore 2 Y) = 3) :
    Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) := by
  apply cubic_sylow_join_symmetricThree T Y hYT hq
  intro hm
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨c,hs,hcR,_,_⟩ := exists_selected_critical_geometry_of_point_normal h hab structural previous hn
  obtain ⟨a,ha,_,ht,hne,hcenter⟩ :=
    exists_extraspecial_critical_actor h hab structural previous hex hcard hexp c hs
  have hRT : F.Ri L 1 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow _ (T.subtype le_sup_right)).trans_eq (map_subgroupOf_eq_of_le le_sup_right)
  have haT : (a : G) ∈ (T : Subgroup G) := hRT (hcR ha)
  let α : MulAut P := MulAut.conjNormal (starMap F a)
  have hinv : Function.Involutive α := by
    intro x
    have he : α ^ 2 = 1 := by
      change (MulAut.conjNormal (starMap F a) : MulAut P) ^ 2 = 1
      rw [←map_pow,ht,map_one]
    exact congrArg (fun f : MulAut P => f x) (by simpa only [pow_two] using he)
  have hfix := MulAut.fixed_eq_center_of_extraspecial27_involution hP α hinv hne hcenter
  have hYP : star F Y ≤ P := by
    have hh := map_mono (f := starMap F) (subgroupOf_mono F.H hYK)
    rw [residual_subgroupOf,map_pResidual_of_surjective 2 (starMap F)
      (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  have hle : star F Y ≤ (center P).map P.subtype := by
    intro x hx
    have hxp : x ∈ P := hYP hx
    apply mem_map_of_mem P.subtype (x := (⟨x,hxp⟩ : P))
    rw [←hfix]
    apply (MulAut.mem_fixedSubgroup α _).mpr
    apply Subtype.ext
    change starMap F a * x * (starMap F a)⁻¹ = x
    obtain ⟨y,hy,rfl⟩ := hx
    have hcom : starMap F ⁅y,a⁆ = 1 := by
      have hcY : (⁅y,a⁆ : F.H).val ∈ Y.pCoreIn 2 :=
        hm (commutator_mem_commutator hy haT)
      obtain ⟨k,hk,hval⟩ := hcY
      have hk' : ((starMap F).comp (inclusion hYH)) k = 1 := hker.ge hk
      have he : inclusion hYH k = ⁅y,a⁆ := Subtype.ext hval
      change starMap F (inclusion hYH k) = 1 at hk'
      rwa [he] at hk'
    rw [map_commutatorElement] at hcom
    have hcomm := commutatorElement_eq_one_iff_mul_comm.mp hcom
    rw [←hcomm,mul_inv_cancel_right]
  apply hZ
  apply eq_of_le_of_card_ge hle
  rw [card_map_of_injective P.subtype_injective,IsExtraspecial.center_order_p 3 P,hc]
open NoncentralChiefRefinement in
/-- The original order-four chief interval supplies an escaping cubic whose
Sylow overgroup has its own two-core quotient isomorphic to S₃. -/
theorem extraspecial_four_interval_escaping_symmetricThree
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (N B : NormalNode F.H) (hNB : N ⋖ B)
    (hUN : F.U ≤ N.val.map F.H.subtype)
    (hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G))
    (hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U)
    (hm : ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype)
    (hc : Nat.card (Section N B) = 4) :
    ∃ Y : Subgroup G, ∃ hYH : Y ≤ F.H,
      Y ≤ K F ∧ IsPPerfect 2 Y ∧
      (T : Subgroup G) ≤ normalizer (Y : Set G) ∧
      Y ≤ normalizer (F.Li L 1 : Set G) ∧ ¬ Y ≤ normalizer (L : Set G) ∧
      Nat.card (star F Y) = 3 ∧
      star F Y ≠ (center (pResidual 2 (HStar F.H))).map (pResidual 2 (HStar F.H)).subtype ∧
      ((starMap F).comp (inclusion hYH)).ker = pCore 2 Y ∧
      Nat.card (Y ⧸ pCore 2 Y) = 3 ∧
      Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨Y,hYH,hYK,hYperfect,hYT,hYL,hout,hcY,hZ,hker,hquot⟩ :=
    extraspecial_four_interval_escaping_cubic h hab structural previous hex hcard hexp
      N B hNB hUN hBC hp hm hc
  exact ⟨Y,hYH,hYK,hYperfect,hYT,hYL,hout,hcY,hZ,hker,hquot,
    extraspecial_cubic_sylow_quotient h hab structural previous hex hcard hexp
      Y hYH hYK hYT hcY hZ hker hquot⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
