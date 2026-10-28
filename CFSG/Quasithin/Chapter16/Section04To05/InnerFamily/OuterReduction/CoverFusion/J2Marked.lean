module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.CoverFusion.Reduction
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.CoverFusion.J2Marked.Words
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.J2Outer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.SylowCenter
public import Theory.SpecificGroups.Suzuki.SubgroupParameters
public import Theory.Mathieu.M22.Properties.Order
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Marked residual fusion in the actual Hall–Janko quotient

For the displayed outer involution, two fixed elements with cube one have
product v conjugate to the known central involution. They lie in O² of the
full fixed subgroup, so their product does too. A checked carrier word l
satisfies b(l)l⁻¹ = v. The Sylow-center calculation supplies the two-central
mark needed by I.2.2(5a).

The existing outer-involution fusion in the full automorphism group reduces
an arbitrary outer involution to this representative. An automorphism e
transports the already constructed carrier elements to e(l) and e(v).
Thus the conjugator remains an element of J₂; an arbitrary automorphism is
never substituted for the carrier conjugator.

The full fixed group in source 16.1.5(8) is Aut(L₃(2)), distinct from its
two-residual. This proof establishes membership in that actual residual
directly, without needing an additional fixed-group identification premise.
The imported full fixed-subgroup interfaces remain unchanged.

The orders 604800, 29120, 20160, and 443520 separate J₂ from the three
large-center quotient alternatives Sz(8), PSL₃(4), and M₂₂. No simplicity
or perfectness certification is needed for either endpoint.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.5(8), printed p.1172; proof of 16.4.9, pp.1190–1191; and
I.2.2(5a,b), p.409. Cover lifting and final source assembly are separate.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.Intersections.OuterReduction.CoverFusion
open LiePreliminaries DoubleCoverCentralizer
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.GeneratorPair
open Sporadic.LeechRelated.J2.ExceptionalParabolics
open Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic

namespace J2Marked

private def v : Carrier := MulAut.conj (Seed.localWord kWord)⁻¹ FirstFusion.t
private def l : Carrier := (Seed.localWord lWord)⁻¹

private theorem v_eq_product : v = Seed.localWord xWord * Seed.localWord yWord := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [v, MulAut.conj_apply, inv_inv, map_mul, map_mul, map_mul, map_inv,
    word_inclusion, word_inclusion,
    word_inclusion, FirstFusion.inclusion_t]
  exact certificate.2.2.2.2.1.symm

/-- The product belongs to the actual embedded O² of the full fixed subgroup. -/
private theorem v_residual : v ∈ fixedTwoResidual Carrier involutionAut := by
  have word_mem (w : List (Fin 3))
      (hf : involution * permWord w * involution⁻¹ = permWord w)
      (hc : permWord w ^ 3 = 1) :
      Seed.localWord w ∈ fixedTwoResidual Carrier involutionAut := by
    have hfixed : Seed.localWord w ∈ involutionAut.fixedSubgroup := by
      rw [MulAut.mem_fixedSubgroup]
      apply Sporadic.LeechRelated.J2.inclusion_injective
      change involution * inclusion (Seed.localWord w) * involution⁻¹ =
        inclusion (Seed.localWord w)
      rwa [word_inclusion]
    let x : involutionAut.fixedSubgroup := ⟨Seed.localWord w, hfixed⟩
    have hx : x ^ 3 = 1 := by
      apply Subtype.ext
      apply Sporadic.LeechRelated.J2.inclusion_injective
      change inclusion (Seed.localWord w ^ 3) = inclusion 1
      rwa [map_pow, map_one, word_inclusion]
    exact mem_map_of_mem _ (mem_pResidual_of_orderOf_coprime
      ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hx)))
  rw [v_eq_product]
  exact (fixedTwoResidual Carrier involutionAut).mul_mem
    (word_mem xWord certificate.1 certificate.2.2.1)
    (word_mem yWord certificate.2.1 certificate.2.2.2.1)

/-- The mark comes from the center of the checked Sylow subgroup of order 128. -/
private theorem t_twoCentral : TwoCentral FirstFusion.t := by
  have ht : FirstFusion.t ∈ (center Seed.s).map Seed.s.subtype := by
    rw [center_s]
    exact mem_zpowers _
  obtain ⟨t, _, ht⟩ := ht
  refine ⟨sylow FirstParabolic.card_l₁, ht ▸ t.property, mem_center_iff.mpr ?_⟩
  intro y
  apply Subtype.ext
  exact mem_centralizer_singleton_iff.mp (s_le_l₁ y.property)

private theorem representative : TwoCentralResidualFusion involutionAut := by
  refine ⟨l, v, v_residual, ?_, ?_, ?_⟩
  · exact (MulAut.conj (Seed.localWord kWord)⁻¹).orderOf_eq _ |>.trans
      central_involution_order
  · exact twoCentral_map (MulAut.conj (Seed.localWord kWord)⁻¹) t_twoCentral
  · apply Sporadic.LeechRelated.J2.inclusion_injective
    change involution * inclusion l * involution⁻¹ * (inclusion l)⁻¹ = inclusion v
    rw [l, v, MulAut.conj_apply, inv_inv, map_mul, map_mul, map_inv, map_inv,
      inv_inv, word_inclusion,
      word_inclusion, FirstFusion.inclusion_t]
    exact certificate.2.2.2.2.2


end J2Marked

/-- Actual model nonisomorphisms specialize the complete center alternative. -/
theorem j2_excludesLargeCenterQuotients : ExcludesLargeCenterQuotients Carrier := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨e⟩
    have hc := Nat.card_congr e.toEquiv
    rw [FirstParabolic.card_carrier,
      BenderSuzuki.MatrixGroups.suzukiMatrixGroup_card 1 (by decide)] at hc
    norm_num at hc
  · rintro ⟨F, _, _, hF, ⟨e⟩⟩
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
    rw [← Nat.card_congr e.toEquiv, FirstParabolic.card_carrier, hF] at hc
    norm_num [Fin.prod_univ_succ] at hc
  · rintro ⟨e⟩
    have hc := Nat.card_congr e.toEquiv
    rw [FirstParabolic.card_carrier, Sporadic.Mathieu.m22_order] at hc
    contradiction

/-- Every outer involution has the marked carrier fusion needed in the double cover. -/
theorem j2_twoCentralResidualFusion
    (b : MulAut Carrier) (hb : orderOf b = 2)
    (ho : ¬ ∃ s : Carrier, b = MulAut.conj s) : TwoCentralResidualFusion b := by
  obtain ⟨e, rfl⟩ :=
    OtherPreliminaries.JankoTwoHigmanSims.J2Outer.outer_involution_representative b hb ho
  apply TwoCentralResidualFusion.of_equiv e.symm
  have he : MulAut.congr e.symm (MulAut.congr e involutionAut) = involutionAut := by
    ext x
    simp [MulAut.congr]
  rw [he]
  exact J2Marked.representative


end CFSG.Quasithin.Chapter16.Intersections.OuterReduction.CoverFusion
