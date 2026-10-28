module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.ShortBender
public import BenderSuzuki.SE.StrongEmbeddingConjugacy

/-!
# Ambient generation from the two involution centralizers

When Mc equals the first endpoint, both ambient involution centralizers lie
in the original generated overgroup. Fusion control gives a unique fixed
coset for both classes, hence for every involution. A proper generated
overgroup would be strongly embedded and force the two classes to fuse.
Their proved separation therefore forces ambient generation.

This is the generation step following the F.4.42 centralizer argument in
the plain partner branch of Aschbacher--Smith 14.2.18--19, printed p.987.
The matching relation and recognition remain separate obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic

private theorem unique_fixed_conjugate {G Ω : Type*} [Group G] [MulAction G Ω]
    {z x : G} (h : IsConj z x) (hu : ∃! q : Ω, z • q = q) :
    ∃! q : Ω, x • q = q := by
  obtain ⟨g,rfl⟩ := isConj_iff.mp h
  obtain ⟨q,hq,hu⟩ := hu
  refine ⟨g • q,?_,?_⟩
  · simp only [mul_smul,inv_smul_smul,hq]
  · intro p hp
    have hh : z • (g⁻¹ • p) = g⁻¹ • p := by
      have hh := congrArg (fun w : Ω => g⁻¹ • w) hp
      simpa only [mul_smul,inv_smul_smul] using hh
    have he := congrArg (fun w : Ω => g • w) (hu (g⁻¹ • p) hh)
    simpa only [smul_inv_smul] using he

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
local notation "P" => binaryParameters 1 Nat.zero_lt_one
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H : Subgroup G}
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
include hG hempty hM hu hmany hcard e hH

theorem source_extended_eq_top_of_partner_eq (r : MarkedTriality T M Mc H)
    (hplain : Mc = H) : Mc ⊔ M = ⊤ := by
  let J := Mc ⊔ M
  let t := (markedShortRoot r (1 : ExtensionField P) : G)
  have ht2 : orderOf t = 2 := markedShortRoot_order r 1 one_ne_zero
  have htT : t ∈ (T : Subgroup G) := markedShortRoot_mem_sylow r hH.1.1.2 1
  have hTJ : (T : Subgroup G) ≤ J := hM.1.2.trans le_sup_right
  obtain ⟨z,hzne,_⟩ := (Nat.card_eq_two_iff' (1 : centralInvolutions T)).mp
    (plane_centralInvolutions_card T M hM.1.2 hcard e)
  have hz1 : (z : G) ≠ 1 := fun hh => hzne (Subtype.ext hh)
  have hzT : (z : G) ∈ (T : Subgroup G) := centralInvolutions_le_sylow T z.property
  have hzC : ∀ u ∈ (T : Subgroup G), Commute (z:G) u := by
    intro u hu
    exact (show u*(z:G)=(z:G)*u from centralInvolutions_le_centralizer_sylow T z.property u hu).symm
  have hfixZ : ∃! q : G ⧸ J, (z:G) • q = q :=
    source_central_unique_fixed hG hempty hM hu hmany hcard e hH r z.property hz1
  have hfixT : ∃! q : G ⧸ J, t • q = q := by
    apply UniqueFixedCoset.unique_of_fusion_and_centralizer (hTJ htT)
    · exact (source_short_centralizer_le_of_partner_eq hG hempty hM hu hmany hcard e hH
        r hplain 1 one_ne_zero).trans
        ((source_parabolics hG T hempty hM hu hmany hcard e H hH
          (firstResidualQuotientEquiv r)).2.2.2.2.trans le_sup_right)
    · intro g hg
      obtain ⟨m,hm,he⟩ := UniqueFixedCoset.p_element_fusion T hTJ hzT hzC hfixZ
        (hTJ htT) hg (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,ht2,pow_one]))
        (isConj_iff.mpr ⟨g,rfl⟩)
      exact ⟨m,hm,he.symm⟩
  have hfix (x : G) (hx : BenderSuzuki.PFAppendixIII.IsInvolution x) :
      ∃! q : G ⧸ J, x • q = q := by
    have hx2 : orderOf x = 2 := (orderOf_eq_prime_iff).mpr ⟨hx.2,hx.1⟩
    rcases source_involution_classes hG hempty hM hu hmany hcard e hH r 1 one_ne_zero
      z.property hz1 x hx2 with h | h
    · exact unique_fixed_conjugate h hfixZ
    · exact unique_fixed_conjugate h hfixT
  by_contra hproper
  have hzI : BenderSuzuki.PFAppendixIII.IsInvolution (z : G) := by
    refine ⟨hz1,?_⟩
    have hp := pow_card_eq_one' (x := z)
    rw [plane_centralInvolutions_card T M hM.1.2 hcard e] at hp
    exact congrArg Subtype.val hp
  have htI : BenderSuzuki.PFAppendixIII.IsInvolution t :=
    ⟨fun he => by simp only [he,orderOf_one] at ht2; omega,
      by simpa only [ht2] using pow_orderOf_eq_one t⟩
  have hstrong : BenderSuzuki.IsStronglyEmbedded J := by
    refine ⟨hproper,⟨z,hTJ hzT,hzI⟩,?_⟩
    intro g hg x hx hxg hi
    apply hg
    apply UniqueFixedCoset.transporter_mem hx (hfix x hi)
    have hh := BenderSuzuki.rightConjugateElem_mem_of_mem_rightConjugate
      (M := J) (g := g⁻¹) (by simpa only [inv_inv] using hxg)
    simpa only [BenderSuzuki.PFAppendixIII.rightConjugateElem,inv_inv] using hh
  obtain ⟨g,hg⟩ := hstrong.involutions_conjugate hzI htI
  apply source_short_not_conj_center hG hempty hM hu hmany hcard e hH r 1 one_ne_zero z.property hz1
  apply isConj_iff.mpr
  exact ⟨g⁻¹,by simpa only [BenderSuzuki.PFAppendixIII.rightConjugateElem,inv_inv] using hg⟩

theorem source_generated_eq_top_of_partner_eq (r : MarkedTriality T M Mc H)
    (hplain : Mc = H) : H ⊔ secondParabolic T M Mc H = ⊤ :=
  (source_generated_eq_top_iff hG hempty hM hu hmany hcard e hH r).mpr
    (source_extended_eq_top_of_partner_eq hG hempty hM hu hmany hcard e hH r hplain)

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
