module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.OddDegree.CubicAction
public import Theory.SpecificGroups.SL2.OddSylowCentralizer
/-!
# Cubic fixed points on the original seed

The original V-star is Sylow in K-star. An odd nonidentity element of the
marked SL₂ centralizes no nonidentity Sylow element, so a V-element fixed
by the cubic subgroup lies in the literal star kernel B=C_V(V_H). Since
B lies in P, the already proved fixed-point freeness on P kills it.
The star quotient and both independent natural markings remain unchanged.

Source: Aschbacher--Smith, printed p.774, the even-degree paragraph.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H X A : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)}
    {f : InvariantFlag (.sl3 m)} {h : G}
    (d : OrthogonalInput D S m f H X A h)
include d

/-- The actual D₃ fixes no nonidentity element of V. -/
theorem source_cubic_seed_fixed_eq_bot (C : Subgroup G) (hC : Nat.card C = 3)
    (hCA : C ≤ oddCartanPart A) : V ⊓ centralizer (C : Set G) = ⊥ := by
  let K := outsideResidual H
  have hCK : C ≤ K := hCA.trans (oddCartanPart_le_residual_of_hall
    (normalizer (L : Set G)) A d.hall_le d.hall)
  have hmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^S.field.degree) :=
    ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,
      ⟨d.closure_natural.quotientEquiv.trans (Theory.PSL2.sl2QuotientEquiv _)⟩⟩
  let := source_residualQuotient_simple hmodel
  let e := residualStarEquiv T H d.source.outside.1.1.2 d.source.moves_omega_center
  let j := e.symm.trans d.closure_natural.quotientEquiv
  obtain ⟨R,hR⟩ := d.seed_star_sylow
  let R' : Sylow 2 SL(2,S.field.Carrier) := R.mapSurjective (f := j.toMonoidHom) j.surjective
  let : Nontrivial C := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x,hx⟩ := exists_ne (1 : C)
  let k : K := inclusion hCK x
  have hx3 : x^3 = 1 := by simpa only [hC] using pow_card_eq_one' (x := x)
  have hk3 : orderOf k = 3 := by
    apply orderOf_eq_prime
    · exact (map_pow (inclusion hCK) x 3).symm.trans (by rw [hx3,map_one])
    · intro he
      exact hx ((inclusion_injective hCK) (he.trans (map_one _).symm))
  let q := Hall.quotientMap d.closure_natural
  have hq3 : orderOf (q k) = 3 := by
    rw [q.orderOf_map_eq_of_coprime_of_isPGroup_ker
      (show IsPGroup 2 q.ker by rw [Hall.quotientMap_ker]; exact pCore_isPGroup) k (by rw [hk3]; decide),hk3]
  let ks : residualStar T H := e (QuotientGroup.mk' _ k)
  have hks : j ks = q k := by simp [j,ks,q,Hall.quotientMap]
  apply bot_unique
  rintro v ⟨hv,hvc⟩
  let vh : H := ⟨v,d.source.outside.1.1.2 (D.le_sylow hv)⟩
  have hvR : starProjection T H vh ∈ (R : Subgroup (residualStar T H)).map
      (residualStar T H).subtype := by
    rw [hR]
    exact mem_map_of_mem _ hv
  obtain ⟨vs,hvs,hvsval⟩ := hvR
  change (vs : Star T H) = starProjection T H vh at hvsval
  have hc : Commute (j vs) (q k) := by
    rw [←hks]
    apply Commute.map
    apply Subtype.ext
    change (vs : Star T H) * (ks : Star T H) = (ks : Star T H) * (vs : Star T H)
    rw [hvsval]
    have he : (ks : Star T H) = starProjection T H (inclusion (outsideResidual_le H) k) :=
      residualStarEquiv_apply _ _ _ _ _
    rw [he,←map_mul,←map_mul]
    congr 1
    apply Subtype.ext
    exact (hvc x x.property).symm
  have hvs1 : j vs = 1 := Matrix.SpecialLinearGroup.eq_one_of_sylow_commutes_nontrivial_odd
    R' (j vs) (q k) (mem_map_of_mem _ hvs)
    (fun he => by rw [he,orderOf_one] at hq3; omega)
    (by decide : Odd 3) (by rw [←hq3]; exact pow_orderOf_eq_one _) hc
  have hvstar : starProjection T H vh = 1 := by
    rw [←hvsval, j.injective (hvs1.trans j.map_one.symm)]
    rfl
  have hvaxis : v ∈ axis V H := by
    rw [axis_eq_fixed d.source d.preceding d.counterexample]
    exact ⟨hv,(QuotientGroup.eq_one_iff vh).mp hvstar⟩
  exact (d.pair_natural.cubic_fixed_eq_bot C hC hCK).le
    ⟨(show axis V H ≤ pairCore V H h from le_sup_left) hvaxis,hvc⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
