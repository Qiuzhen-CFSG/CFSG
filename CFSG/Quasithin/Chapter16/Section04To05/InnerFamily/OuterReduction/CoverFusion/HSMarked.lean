module
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.CoverFusion.Reduction
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.CoverFusion.HSMarked.Certificate
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.PermutationFusion
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.Enumeration
public import Theory.SpecificGroups.Suzuki.SubgroupParameters
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.Mathieu.M22.Properties.Order

/-!
# Marked residual fusion for both outer HS involution classes

For each concrete outer representative, the permutation certificate gives
an HS element l with b(l)l⁻¹ = v. It writes v as a product of two odd-order
fixed elements, proving v ∈ O²(C_HS(b)) without identifying the full fixed
group with its residual. A second HS conjugator carries the central involution
e0 to v. The checked order-512 Sylow subgroup and a calculation on its three
generators establish the two-central mark of e0, hence of v.

The exhaustive outer-involution fusion theorem and the actual equivalence
between the permutation normalizer and Aut(HS) transport these witnesses to
every outer involution. The HS order separates its carrier from Sz(8), PSL₃(4)
and M₂₂, discharging the exceptional-quotient exclusions used in the cover
argument. Neither conclusion requires additional simplicity, perfectness,
centralizer-shape or fusion premises.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 16.4.9(2), printed pp.1190–1191; HS row of 16.1.5(10), p.1172.
The mark is precisely the hypothesis needed for I.2.2(5a), pp.409–411.
The cover lifting and order-four correction remain in CoverFusion.Reduction.
-/

public section
namespace CFSG.Quasithin.Chapter16.Intersections.OuterReduction.CoverFusion
open Subgroup Theory.GroupTheory
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.NormalizerIndex
open OtherPreliminaries.JankoTwoHigmanSims
open HSOuter LiePreliminaries DoubleCoverCentralizer
set_option maxRecDepth 100000

namespace HSMarked
open EvenLocalCandidates

private theorem central_commutes : ∀ j : Fin 3, ∀ x : Fin 100,
    (inclusion (sylowGenerator j) * inclusion e0) x =
      (inclusion e0 * inclusion (sylowGenerator j)) x := by
  apply OrderCertificate.allFin
  decide +kernel

/-- The existing central HS representative lies in the center of a Sylow subgroup. -/
theorem central_twoCentral : TwoCentral e0 := by
  have hm : e0 ∈ subgroup := by
    rw [e0_eq_word]
    exact subgroup.pow_mem (subgroup.inv_mem (subset_closure ⟨2, rfl⟩)) 2
  have hc : subgroup ≤ centralizer ({e0} : Set Carrier) := by
    apply (closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    exact Subtype.ext (Equiv.ext (central_commutes j))
  refine ⟨HSInner.ClassCoverage.Certificate.sylow, hm, ?_⟩
  apply mem_center_iff.mpr
  intro x
  apply Subtype.ext
  exact mem_centralizer_singleton_iff.mp (hc x.property)

open Certificate

/-- Both concrete representatives have the required marked residual fusion. -/
theorem representative_fusion (i : Fin 2) :
    TwoCentralResidualFusion (generated.normalizerMonoidHom (actor i)) := by
  let b := generated.normalizerMonoidHom (actor i)
  have hfixed (j : Fin 2) : element i ⟨3 + j.val, by omega⟩ ∈ b.fixedSubgroup := by
    rw [MulAut.mem_fixedSubgroup]
    exact Subtype.ext (Equiv.ext (fixed_check i j))
  let oddElement (j : Fin 2) : b.fixedSubgroup :=
    ⟨element i ⟨3 + j.val, by omega⟩, hfixed j⟩
  have hpow (j : Fin 2) : oddElement j ^ oddExponent i j = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact Equiv.ext (odd_check i j)
  have hcop : ∀ i j, Nat.Coprime 2 (oddExponent i j) := by
    decide +kernel
  have hmem (j : Fin 2) : element i ⟨3 + j.val, by omega⟩ ∈ fixedTwoResidual Carrier b := by
    exact ⟨oddElement j, mem_pResidual_of_orderOf_coprime
      ((hcop i j).of_dvd_right (orderOf_dvd_of_pow_eq_one (hpow j))), rfl⟩
  have hprod : element i 4 * element i 3 = element i 1 :=
    Subtype.ext (Equiv.ext (product_check i))
  refine ⟨element i 0, element i 1, ?_, ?_, ?_, ?_⟩
  · rw [← hprod]
    exact (fixedTwoResidual Carrier b).mul_mem (hmem 1) (hmem 0)
  · apply orderOf_eq_prime
    · exact Subtype.ext (Equiv.ext (square_check i))
    · intro he
      exact nontrivial_check i (congrArg (fun x : Carrier => inclusion x 0) he)
  · have hm := twoCentral_map (MulAut.conj (element i 2)) central_twoCentral
    have he : MulAut.conj (element i 2) e0 = element i 1 :=
      Subtype.ext (Equiv.ext (mark_check i))
    exact he ▸ hm
  · exact Subtype.ext (Equiv.ext (fusion_check i))

private theorem fusion_of_conjugate (n g : PermutationNormalizer) (i : Fin 2)
    (hn : n.val = g.val * (actor i).val * g.val⁻¹) :
    TwoCentralResidualFusion (generated.normalizerMonoidHom n) := by
  have hn' : n = g * actor i * g⁻¹ := Subtype.ext hn
  have he : MulAut.congr (generated.normalizerMonoidHom g).symm
      (generated.normalizerMonoidHom n) = generated.normalizerMonoidHom (actor i) := by
    rw [hn', map_mul, map_mul, map_inv]
    ext x
    simp [MulAut.congr_apply]
  apply TwoCentralResidualFusion.of_equiv (generated.normalizerMonoidHom g).symm
  rw [he]
  exact representative_fusion i

end HSMarked

/-- Every outer involution of the actual HS carrier has marked residual fusion. -/
theorem hs_twoCentralResidualFusion (b : MulAut Carrier) (hb : orderOf b = 2)
    (hout : ¬ ∃ s : Carrier, b = MulAut.conj s) : TwoCentralResidualFusion b := by
  obtain ⟨n, rfl, hn, ho⟩ := outer_involution_lift b hb hout
  rcases outer_involution_permutation_fusion n hn ho with ⟨g, hg⟩ | ⟨g, hg⟩
  · exact HSMarked.fusion_of_conjugate n g 0 hg
  · exact HSMarked.fusion_of_conjugate n g 1 hg

/-- HS is distinct from every quotient in the large-center exceptions of 16.1.2(2). -/
theorem hs_excludesLargeCenterQuotients : ExcludesLargeCenterQuotients Carrier := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨e⟩
    have he := Nat.card_congr e.toEquiv
    rw [card_carrier, BenderSuzuki.MatrixGroups.suzukiMatrixGroup_card 1 (by decide)] at he
    norm_num at he
  · rintro ⟨F, hF, hfin, hcard, ⟨e⟩⟩
    let := hF
    let := hfin
    have he := Nat.card_congr e.toEquiv
    have ho := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
    rw [← he, card_carrier, hcard] at ho
    norm_num [Fin.prod_univ_succ] at ho
  · rintro ⟨e⟩
    have he := Nat.card_congr e.toEquiv
    rw [card_carrier, Sporadic.Mathieu.m22_order] at he
    omega

end CFSG.Quasithin.Chapter16.Intersections.OuterReduction.CoverFusion
