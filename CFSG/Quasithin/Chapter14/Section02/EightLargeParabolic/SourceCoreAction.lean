module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourcePerfect
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourcePartnerCore
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Theory.SpecificGroups.PSL2.EightExtraspecialAction

/-!
# The original partner core action without marked triality

Equality of the original full cores identifies the intrinsic partner core
with the extraspecial core of H. The canonical partner action therefore has
kernel exactly O₂(Mc), and its restriction to the actual H inclusion has
kernel O₂(H). The same central quotient is elementary of order 256.

Full H is perfect by the source critical geometry. Its literal quotient
marking and the actual conjugation coordinates on the partner core quotient
then give a trivial action centralizer. No marked-triality realization or
replacement action is assumed.

Source: Aschbacher--Smith 14.2.18, printed p.987, and the Burnside--Frattini
action kernel theorem.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceCoreAction
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)

private def partnerCoreEquiv : pCore 2 Mc ≃* H.pCoreIn 2 :=
  ((pCore 2 Mc).equivMapOfInjective Mc.subtype Mc.subtype_injective).trans
    (MulEquiv.subgroupCongr
      (SourcePartnerCore.partner_core_eq hG T hempty hM hu hmany hcard e H hH eR))

private def firstPartnerCoreEquiv : pCore 2 H ≃* pCore 2 Mc :=
  ((pCore 2 H).equivMapOfInjective H.subtype H.subtype_injective).trans
    (partnerCoreEquiv hG T hempty hM hu hmany hcard e H hH eR).symm

private theorem firstPartnerCoreEquiv_val (q : pCore 2 H) :
    ((firstPartnerCoreEquiv hG T hempty hM hu hmany hcard e H hH eR q : Mc) : G) = q := by
  exact congrArg (fun x : H.pCoreIn 2 => (x : G))
    ((partnerCoreEquiv hG T hempty hM hu hmany hcard e H hH eR).apply_symm_apply
      ((pCore 2 H).equivMapOfInjective H.subtype H.subtype_injective q))

include hG hempty hM hu hmany hcard e hH eR

/-- The intrinsic partner core is extraspecial by equality of the original ambient cores. -/
theorem partner_core_extraspecial : IsExtraspecial 2 (pCore 2 Mc) :=
  IsExtraspecial.of_mulEquiv (partnerCoreEquiv hG T hempty hM hu hmany hcard e H hH eR).symm
    (source_core_structure hG T hempty hM hu hmany hcard e H hH eR).1

/-- The intrinsic original partner core has order 512. -/
theorem partner_core_card : Nat.card (pCore 2 Mc) = 512 :=
  (Nat.card_congr (partnerCoreEquiv hG T hempty hM hu hmany hcard e H hH eR).toEquiv).trans
    (source_core_orders hG T hempty hM hu hmany hcard e H hH eR).1

/-- The literal partner central quotient is elementary of order 256. -/
theorem partner_core_module :
    IsElementaryAbelian 2 (PartnerCoreModule Mc) ∧ Nat.card (PartnerCoreModule Mc) = 256 := by
  let := partner_core_extraspecial hG T hempty hM hu hmany hcard e H hH eR
  refine ⟨IsExtraspecial.quotient_elementary_abelian 2 _,?_⟩
  have hc := card_eq_card_quotient_mul_card_subgroup (center (pCore 2 Mc))
  rw [partner_core_card hG T hempty hM hu hmany hcard e H hH eR,
    IsExtraspecial.center_order_p 2 (pCore 2 Mc)] at hc
  change Nat.card (pCore 2 Mc ⧸ center (pCore 2 Mc)) = 256
  omega

/-- The existing canonical partner action has exactly the intrinsic two-core as kernel. -/
theorem partner_action_kernel : (partnerCoreAction Mc).ker = pCore 2 Mc := by
  let := partner_core_extraspecial hG T hempty hM hu hmany hcard e H hH eR
  have hk (N : Subgroup (pCore 2 Mc)) [N.Characteristic]
      (hN : N = frattini (pCore 2 Mc)) :
      ((quotientAut N).comp (MulAut.conjNormal : Mc →* MulAut (pCore 2 Mc))).ker =
        pCore 2 Mc := by
    subst N
    exact pCore_frattini_action_kernel 2
      (source_partner_characteristic_two hG hempty hM hu hmany hcard e hH)
  exact hk _ (IsExtraspecial.frattini_eq_center (p := 2) (P := pCore 2 Mc)).symm

/-- Restriction along the actual H inclusion has exactly O₂(H) as its kernel. -/
theorem first_action_kernel :
    (firstCoreAction hG hempty hM hu hmany hcard e hH).ker = pCore 2 H := by
  change (partnerCoreAction Mc).ker.comap (inclusion _) = _
  rw [partner_action_kernel hG T hempty hM hu hmany hcard e H hH eR]
  ext x
  constructor
  · intro hx
    have hx' : (x : G) ∈ Mc.pCoreIn 2 := ⟨inclusion
      (source_first_le_partner hG hempty hM hu hmany hcard e hH) x,hx,rfl⟩
    rw [SourcePartnerCore.partner_core_eq hG T hempty hM hu hmany hcard e H hH eR] at hx'
    obtain ⟨y,hy,he⟩ := hx'
    exact (Subtype.ext he : y = x) ▸ hy
  · intro hx
    have hx' : (x : G) ∈ H.pCoreIn 2 := ⟨x,hx,rfl⟩
    rw [←SourcePartnerCore.partner_core_eq hG T hempty hM hu hmany hcard e H hH eR] at hx'
    obtain ⟨y,hy,he⟩ := hx'
    change inclusion (source_first_le_partner hG hempty hM hu hmany hcard e hH) x ∈ pCore 2 Mc
    exact (Subtype.ext he : y = inclusion
      (source_first_le_partner hG hempty hM hu hmany hcard e hH) x) ▸ hy

/-- The actual first-endpoint action on the same partner module has trivial centralizer. -/
theorem first_action_centralizer_eq_bot :
    centralizer ((firstCoreAction hG hempty hM hu hmany hcard e hH).range :
      Set (MulAut (PartnerCoreModule Mc))) = ⊥ := by
  let f := firstPartnerCoreEquiv hG T hempty hM hu hmany hcard e H hH eR
  let a := firstCoreAction hG hempty hM hu hmany hcard e hH
  let c := (QuotientGroup.mk' (center (pCore 2 Mc))).comp f.toMonoidHom
  let : Group.IsPerfect H := SourcePerfect.first_perfect hG T hempty hM hu hmany hcard e H hH eR
  let : IsExtraspecial 2 (pCore 2 H) := IsExtraspecial.of_mulEquiv f.symm
    (partner_core_extraspecial hG T hempty hM hu hmany hcard e H hH eR)
  let := (partner_core_module hG T hempty hM hu hmany hcard e H hH eR).1
  have hs : Function.Surjective c := (QuotientGroup.mk'_surjective _).comp f.surjective
  have hk : c.ker = center (pCore 2 H) := by
    ext q
    change QuotientGroup.mk' (center (pCore 2 Mc)) (f q) = 1 ↔ q ∈ center (pCore 2 H)
    constructor
    · intro hq
      have hz := (QuotientGroup.eq_one_iff (f q)).mp hq
      have hh : f.symm (f q) ∈ center (pCore 2 H) := (centerCongr f.symm ⟨f q,hz⟩).property
      rwa [f.symm_apply_apply] at hh
    · intro hq
      exact (QuotientGroup.eq_one_iff (f q)).mpr (centerCongr f ⟨q,hq⟩).property
  have ha (h : H) (q : pCore 2 H) : c (MulAut.conjNormal h q) = a h (c q) := by
    change QuotientGroup.mk' (center (pCore 2 Mc)) (f (MulAut.conjNormal h q)) =
      quotientAut (center (pCore 2 Mc)) (MulAut.conjNormal
        (inclusion (source_first_le_partner hG hempty hM hu hmany hcard e hH) h))
        (QuotientGroup.mk' (center (pCore 2 Mc)) (f q))
    rw [quotientAut_apply_mk]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    rw [firstPartnerCoreEquiv_val]
    simp only [MulAut.conjNormal_apply,coe_mul,coe_inv]
    rw [firstPartnerCoreEquiv_val]
    rfl
  exact Theory.SpecificGroups.PSL2Eight.extraspecial_action_centralizer_eq_bot
    (sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR)
    c hs hk a ha (partner_core_module hG T hempty hM hu hmany hcard e H hH eR).2

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceCoreAction
