module

public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.NaturalLocalAction.ActorFixedSpaces

/-!
# The cubic J₂ actor in the actual natural module

A Sylow conjugation puts the SL₂ image of an elementary subgroup of the
noncentral centralizer into upper-unipotent form. Conjugating its full octonion
factors by the same block gives explicit six-coordinate displacement formulas.
Those formulas lower a three-step filtration, so every triple displacement
vanishes. This applies to the concrete rank-four subgroup constructed in Actors;
its fixed codimension is eight by ActorFixedSpaces. The supplied marking
transports this actual actor to the original source group.

The only remaining inputs are the named universal B.4.6 root facts. Neither
cubicity nor an attaining actor is assumed. The root formulas are applications
of the licensed ATLAS port imported by CentralizerCoordinates; no new upstream
source is copied here. Source: Aschbacher–Smith, K.4.5, printed p.460/PDF p.471.
-/

open Atlas.G2 Atlas.G2.Explicit Matrix
open Atlas.G2.PairStabilizer Atlas.G2.ShortRootProducts.CentralizerCore
open Atlas.G2.ConwayRootFour.OctonionLocals
open scoped MatrixGroups
open Subgroup Representation Representation.BinaryOffender
public noncomputable section
namespace CFSG.Quasithin.ChapterK.JankoTwo.NaturalLocalAction.CubicCoordinates
variable {K : Type*} [Field K] [CharP K 2]

private def upperFactor (p : Multiplicative (K × K)) (r u : K) : Model K :=
  longRootHom p * rootC r * blockHom (Matrix.SpecialLinearGroup.transvection zero_ne_one u)

private theorem upperFactor_action (p : Multiplicative (K × K)) (r u : K) (v : Fin 6 → K) :
    action (upperFactor p r u) v =
      ![v 0 + r^2*v 5 + p.toAdd.2*(v 3+u*v 4) + p.toAdd.1*v 4,
        v 1 + u*v 2 + r*(v 3+u*v 4) + p.toAdd.1*v 5,
        v 2 + r*v 4 + p.toAdd.2*v 5, v 3+u*v 4, v 4, v 5] := by
  rw [action_lift]
  ext i
  fin_cases i <;> simp [upperFactor, Natural.binaryOffDiagonal, liftSix,
    longRootHom, rootA, rootAEquiv, rootALinear, rootAApply,
    rootB, rootBEquiv, rootBLinear, rootBApply, rootC, rootCEquiv, rootCLinear,
    rootCApply, blockHom, blockEquiv, blockLinear,
    Matrix.SpecialLinearGroup.transvection_coe,
    CharTwo.neg_eq, CharTwo.sub_eq_add]

private def delta (p : Multiplicative (K × K)) (r u : K) (v : Fin 6 → K) :=
  action (upperFactor p r u) v - v

private theorem delta_formula (p : Multiplicative (K × K)) (r u : K) (v : Fin 6 → K) :
    delta p r u v =
      ![r^2*v 5 + p.toAdd.2*(v 3+u*v 4) + p.toAdd.1*v 4,
        u*v 2 + r*(v 3+u*v 4) + p.toAdd.1*v 5,
        r*v 4 + p.toAdd.2*v 5, u*v 4, 0, 0] := by
  rw [delta, upperFactor_action]
  ext i
  fin_cases i <;> simp <;> ring

private theorem triple_delta (p q s : Multiplicative (K × K)) (r u t v w z : K)
    (x : Fin 6 → K) : delta p r u (delta q t v (delta s w z x)) = 0 := by
  simp only [delta_formula]
  ext i
  fin_cases i <;> simp

private theorem conjugate_factor (k M : SL(2,K)) (p : Multiplicative (K × K)) (r : K) :
    ∃ q : Multiplicative (K × K),
      MulAut.conj (blockHom k)⁻¹ (longRootHom p * rootC r * blockHom M) =
        longRootHom q * rootC r * blockHom (MulAut.conj k⁻¹ M) := by
  have hn : blockHom k ∈ normalizer (longRootLocal (F := K) : Set (Model K)) :=
    block_le_longRootNormalizer ⟨k,rfl⟩
  obtain ⟨q,hq⟩ := (mem_normalizer_iff''.mp hn (longRootHom p)).mp ⟨p,rfl⟩
  refine ⟨q,?_⟩
  have hc : MulAut.conj (blockHom k)⁻¹ (rootC r) = rootC r := by
    change (blockHom k)⁻¹ * rootC r * ((blockHom k)⁻¹)⁻¹ = rootC r
    rw [inv_inv, (block_commute_rootC k r).inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]
  have hp : MulAut.conj (blockHom k)⁻¹ (longRootHom p) = longRootHom q := by
    simpa only [MulAut.conj_apply, inv_inv] using hq.symm
  rw [map_mul, map_mul, hp, hc]
  congr 1
  change (blockHom k)⁻¹ * blockHom M * ((blockHom k)⁻¹)⁻¹ =
    blockHom (k⁻¹ * M * (k⁻¹)⁻¹)
  rw [inv_inv, inv_inv, map_mul, map_mul, map_inv]

/-- A short-root-centralizer factor whose block lies in a specified conjugate
upper subgroup has cubic coordinates in the same conjugate chart. -/
private theorem factor_in_upper_chart (g : Model K) (k M : SL(2,K))
    (p : Multiplicative (K × K)) (r : K)
    (hM : M ∈ (Matrix.SpecialLinearGroup.upperUnipotent K).map (MulAut.conj k).toMonoidHom) :
    ∃ (q : Multiplicative (K × K)) (u : K),
      MulAut.conj g (longRootHom p * rootC r * blockHom M) =
        MulAut.conj (g * blockHom k) (upperFactor q r u) := by
  obtain ⟨N,hN,hNM⟩ := hM
  obtain ⟨u,hu⟩ := (Matrix.SpecialLinearGroup.mem_upperUnipotent K N).mp hN
  obtain ⟨q,hq⟩ := conjugate_factor k M p r
  have hm : MulAut.conj k⁻¹ M = Matrix.SpecialLinearGroup.transvection zero_ne_one u := by
    rw [← hNM, ← hu]
    simp [MulAut.conj_apply, mul_assoc]
  rw [hm] at hq
  refine ⟨q,u,?_⟩
  have hh := congrArg (MulAut.conj (g * blockHom k)) hq
  simpa [upperFactor, MulAut.conj_apply, mul_assoc] using hh

end CFSG.Quasithin.ChapterK.JankoTwo.NaturalLocalAction.CubicCoordinates

namespace CFSG.Quasithin.ChapterK.JankoTwo.MarkedModule
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.GeneratorPair
open Sporadic.LeechRelated.J2.InnerInvolutionCores
open NaturalLocalAction NaturalLocalAction.CubicCoordinates
open NaturalLocalAction.CentralizerCoordinates
variable {K G V : Type*} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
  [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (D : MarkedModule (K := K) ρ)

/-- Every elementary actor containing the noncentral involution is cubic on
the actual natural quotient. The proof uses the upper-root filtration. -/
theorem noncentral_actor_cubic
    (h : NaturalLocalAction.InvolutionImages.B46RootFacts K)
    (A : Subgroup Carrier) (hA : IsElementaryTwo A) (ha : a ∈ A) :
    IsCubic D.naturalCarrierAction A := by
  let : Module.Finite (ZMod 2) K := Module.finite_of_finrank_eq_succ D.fieldDegree
  let : Finite K := Module.finite_of_finite (ZMod 2)
  obtain ⟨g,r,hr,he⟩ := D.carrierEmbedding_a_isShortRootElement h
  obtain ⟨φ,hφ,-⟩ := D.shortRootCentralizer_comparison g r hr he
  obtain ⟨P,hP⟩ := (actorSL2Image_isTwoGroup φ A hA).exists_le_sylow
  obtain ⟨k,hk⟩ := MulAction.exists_smul_eq SL(2,K)
    (Matrix.SpecialLinearGroup.upperUnipotentSylow K 2) P
  have heP : (P : Subgroup SL(2,K)) =
      (Matrix.SpecialLinearGroup.upperUnipotent K).map (MulAut.conj k).toMonoidHom := by
    rw [← hk]
    rfl
  have hf (x : Carrier) (hx : x ∈ A) :
      ∃ (p : Multiplicative (K × K)) (t u : K),
      D.carrierEmbedding x = MulAut.conj (g * blockHom k) (upperFactor p t u) := by
    let c : involutionCentralizer := ⟨x,le_centralizer_of_elementary A hA ha hx⟩
    let y := a_centralizer_equiv c
    have hy : centralizerEmbedding y = x := by
      change (a_centralizer_equiv.symm (a_centralizer_equiv c)).val = x
      rw [MulEquiv.symm_apply_apply]
    have hm : φ y.2 ∈ (Matrix.SpecialLinearGroup.upperUnipotent K).map (MulAut.conj k).toMonoidHom := by
      rw [← heP]
      exact hP (mem_map_of_mem _ (show centralizerEmbedding y ∈ A from hy.symm ▸ hx))
    obtain ⟨p,t,hpt⟩ := hφ y
    obtain ⟨q,u,hqu⟩ := factor_in_upper_chart g k (φ y.2) p t hm
    exact ⟨q,t,u,by rw [← hy,hpt,hqu]⟩
  have hδ (x : Carrier) (p : Multiplicative (K × K)) (t u : K)
      (hx : D.carrierEmbedding x = MulAut.conj (g * blockHom k) (upperFactor p t u))
      (v : Natural.Space K) :
      shortRootChart (g * blockHom k) (displacement D.naturalCarrierAction x v) =
        delta p t u (shortRootChart (g * blockHom k) v) := by
    change shortRootChart (g * blockHom k) (Natural.action K (D.carrierEmbedding x) v - v) = _
    rw [map_sub,hx,shortRootChart_conj]
    rfl
  intro x hx y hy z hz v
  obtain ⟨p,t,u,hx'⟩ := hf x hx
  obtain ⟨q,w,s,hy'⟩ := hf y hy
  obtain ⟨l,j,n,hz'⟩ := hf z hz
  apply (shortRootChart (g * blockHom k)).injective
  rw [map_zero,hδ x p t u hx',hδ y q w s hy',hδ z l j n hz']
  exact triple_delta p q l t u w s j n _

/-- The specified rank-four subgroup supplies an actual attaining actor. -/
theorem sourceActor_calculation
    (h : NaturalLocalAction.InvolutionImages.B46RootFacts K) :
    IsElementaryTwo D.sourceActor ∧ rank D.sourceActor = 4 ∧
      IsCubic ρ D.sourceActor ∧ fixedCodim ρ D.sourceActor = 8 ∧
      ¬ IsQuadratic ρ D.sourceActor := by
  have hc := D.noncentral_actor_cubic h actor actor_elementary a_mem_actor
  have hd := D.noncentral_actor_fixedCodim h actor actor_elementary a_mem_actor (by rw [actor_rank]; decide)
  have hn := D.noncentral_actor_not_quadratic h actor actor_elementary a_mem_actor (by rw [actor_rank]; decide)
  obtain ⟨he,hr,hc',hd'⟩ := D.sourceActor_of_natural_calculation hc hd
  exact ⟨he,hr,hc',hd',fun hq => hn ((D.carrier_quadratic_iff actor).mp hq)⟩

end CFSG.Quasithin.ChapterK.JankoTwo.MarkedModule
