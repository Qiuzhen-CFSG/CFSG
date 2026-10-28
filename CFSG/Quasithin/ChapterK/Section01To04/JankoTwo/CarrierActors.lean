module

public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.NaturalLocalAction
public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.InvolutionGeometry
public import Theory.Representation.OrthogonalFourMinusRankOne.InnerClassification.Conjugacy
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# The inner actor alternatives in K.4.5

The exhaustive native J₂ involution fusion and the literal long-root fixer
exclude rank-two small actors. Every larger elementary actor contains a
conjugate of the noncentral involution. After the same conjugation of the
actor, the proved E₄ × A₅ natural-module calculation gives codimension eight
and failure of quadraticity. Divisibility of its order into the full
centralizer order 240 bounds its rank by four.

The only earlier-source inputs are the universal B.4.6 root and long-root
module facts. The embedding comparisons, actual conjugations, rank bounds,
and J₂ local calculations are proved by the imported modules.
Source: Aschbacher–Smith, K.4.5, printed p.460 / PDF p.471.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.GeneratorPair
open Sporadic.LeechRelated.J2.InnerInvolutionCores
namespace CFSG.Quasithin.ChapterK.JankoTwo.MarkedModule
open NaturalLocalAction
variable {K G V : Type*} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
  [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (D : MarkedModule (K := K) ρ)
  [FiniteDimensional (ZMod 2) V]

omit [FiniteDimensional (ZMod 2) V] in
private theorem carrierAction_fixedCodim (A : Subgroup Carrier) :
    fixedCodim D.carrierAction A = fixedCodim D.naturalCarrierAction A := by
  simpa only [Subgroup.map_id] using fixedCodim_map_equivariant D.carrierAction
    D.naturalCarrierAction (MonoidHom.id Carrier) D.equiv.toLinearEquiv
    D.carrier_equivariant A

/-- The two native involution classes give a uniform displacement bound on
the actual carrier restriction. -/
theorem carrier_involution_displacement
    (h : InvolutionImages.B46RootFacts K) (hV : B46LongRootModuleFacts K)
    (x : Carrier) (hx : orderOf x = 2) :
    4 ≤ fixedCodim D.carrierAction (zpowers x) := by
  rcases involution_fusion x hx with ha | hz
  · obtain ⟨g,rfl⟩ := isConj_iff.mp ha
    rw [fixedCodim_zpowers_conj,
      D.carrierAction_fixedCodim, (D.carrier_noncentral_dimensions h).1]
    decide
  · obtain ⟨g,rfl⟩ := isConj_iff.mp hz
    rw [fixedCodim_zpowers_conj, D.carrierAction_fixedCodim]
    have he : fixedCodim D.naturalCarrierAction (zpowers FirstFusion.t) =
        fixedCodim (naturalAction K) (zpowers (D.carrierEmbedding FirstFusion.t)) := by
      unfold fixedCodim
      rw [fixedSpace_comp_map, MonoidHom.map_zpowers]
    rw [he,(D.carrier_longRoot_data h hV).1]

private theorem conjugate_contains {A : Subgroup Carrier} {x t : Carrier}
    (hx : x ∈ A) (ht : IsConj t x) :
    ∃ g : Carrier, t ∈ A.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g,rfl⟩ := isConj_iff.mp ht
  refine ⟨g⁻¹, ?_⟩
  convert mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hx using 1
  simp [mul_assoc]

/-- A rank-two actor is excluded either by noncentral displacement six or
by the literal long-root pointwise fixer and cyclic centralizer center. -/
theorem carrier_small_rank_two_impossible
    (h : InvolutionImages.B46RootFacts K) (hV : B46LongRootModuleFacts K)
    (A : Subgroup Carrier) (hA : IsElementaryTwo A) (hr : rank A = 2) :
    2 * rank A < fixedCodim D.carrierAction A := by
  let := hA.2
  obtain ⟨x,hx,hne⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have hx2 : orderOf x = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian x hx) hne
  rcases involution_fusion x hx2 with ha | hz
  · obtain ⟨g,hg⟩ := conjugate_contains hx ha
    have hm := ChapterE.fixedCodim_mono D.carrierAction (zpowers_le.mpr hg)
    rw [fixedCodim_map_conj, D.carrierAction_fixedCodim (zpowers a),
      (D.carrier_noncentral_dimensions h).1] at hm
    omega
  · obtain ⟨g,hg⟩ := conjugate_contains hx hz
    have ht := D.carrier_rank_two_exclusion_of_B46 h hV
      (A.map (MulAut.conj g).toMonoidHom) (by rw [rank_map_conj,hr]) hg
    simpa only [rank_map_conj, fixedCodim_map_conj] using ht

private theorem noncentral_actor_rank_le (A : Subgroup Carrier)
    (hA : IsElementaryTwo A) (ha : a ∈ A) : rank A ≤ 4 := by
  have ha5 : Nat.card A5 = 60 := by
    rw [A5, nat_card_alternatingGroup]
    norm_num
  have hcard : Nat.card involutionCentralizer = 240 := by
    rw [Nat.card_congr a_centralizer_equiv.toEquiv, Nat.card_prod, ha5]
    norm_num [E4, C2, Nat.card_eq_fintype_card]
  have hd := card_dvd_of_le (le_centralizer_of_elementary A hA ha)
  rw [hA.card_eq_two_pow_rank, hcard] at hd
  by_contra! hn
  have hp : 2 ^ 5 ∣ 2 ^ rank A := pow_dvd_pow 2 hn
  have hf : 32 ∣ 240 := hp.trans hd
  norm_num at hf

/-- An actor of rank at least three contains a conjugate of the noncentral
involution. Its full centralizer bounds the rank, and its natural action
forces codimension eight and failure of quadraticity. -/
theorem carrier_large_actor_calculation
    (h : InvolutionImages.B46RootFacts K)
    (A : Subgroup Carrier) (hA : IsElementaryTwo A) (hr : 3 ≤ rank A) :
    rank A ≤ 4 ∧ fixedCodim D.carrierAction A = 8 ∧
      ¬ IsQuadratic D.carrierAction A := by
  obtain ⟨x,hx,ht⟩ := exists_noncentral_involution A hA hr
  obtain ⟨g,hg⟩ := conjugate_contains hx ht
  let B := A.map (MulAut.conj g).toMonoidHom
  have hB : IsElementaryTwo B := hA.map_conj g
  have hrB : 3 ≤ rank B := by simpa only [B,rank_map_conj] using hr
  refine ⟨?_,?_,?_⟩
  · simpa only [B,rank_map_conj] using noncentral_actor_rank_le B hB hg
  · have hd := D.noncentral_actor_fixedCodim h B hB hg hrB
    simpa only [← D.carrierAction_fixedCodim, B, fixedCodim_map_conj] using hd
  · intro hq
    have hqB := (Representation.OrthogonalFourMinus.RankOne.InnerTransport.quadratic_conj_iff
      D.carrierAction A g).mpr hq
    apply D.noncentral_actor_not_quadratic h B hB hg hrB
    apply (D.carrier_quadratic_iff B).mp
    rintro _ ⟨u,hu,rfl⟩ _ ⟨v,hv,rfl⟩ w
    exact hqB u hu v hv w
end CFSG.Quasithin.ChapterK.JankoTwo.MarkedModule
