module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeSection
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourParabolic
import all CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.RankSieve.SmallRows.LocalActions

/-!
# The original M22-code image in the parabolic quotient

The literal five-dimensional B/U has a one-dimensional coinvariant quotient
for the original local residual. Its map to H/O₂(H) kills the residual
commutators, so the image of B has order at most two. The original degree-one
pair then gives the order-two/order-four alternatives for the image of V.
The same marked A₅ residual bounds the three- and five-ranks of H by one.
All statements retain the selected pair, conjugator and quotient maps.

Source: Aschbacher--Smith 8.2.9, printed p.720, refs/quasithin.pdf.
Exclusion of the order-four alternative and the later quotient sieve are
separate mathematical steps.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open Normalizer.SmallOvergroups HermitianSource
open Normalizer.ParabolicReduction.RankSieve
open Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G]
set_option backward.isDefEq.respectTransparency false

private theorem section_image_card_le_two
    (R B U H : Subgroup G) [IsElementaryAbelian 2 B]
    (hRB : R ≤ normalizer (B : Set G)) (hRU : R ≤ normalizer (U : Set G))
    [(U.subgroupOf B).Normal]
    (hBH : B ≤ H) (hUQ : U ≤ H.pCoreIn 2)
    (hcomm : ⁅R,B⁆ ≤ H.pCoreIn 2)
    (ρ : Representation (ZMod 2) R (Additive (B ⧸ U.subgroupOf B)))
    (hρ : ∀ x b, ρ x (Additive.ofMul b) = Additive.ofMul (sectionAction R B U hRB hRU x b))
    (hd : Module.finrank (ZMod 2) (Coinvariants ρ) = 1) :
    Nat.card ((B.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) ≤ 2 := by
  let A := (B.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))
  let : IsElementaryAbelian 2 (B.subgroupOf H) :=
    IsElementaryAbelian.of_injective (subgroupOfEquivOfLe hBH).toMonoidHom
      (subgroupOfEquivOfLe hBH).injective
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  let f : B →* A := ((QuotientGroup.mk' (pCore 2 H)).comp
    (inclusion hBH)).codRestrict A (fun b => mem_map_of_mem _ b.property)
  have hfs : Function.Surjective f := by
    rintro ⟨y,b,hb,rfl⟩
    exact ⟨⟨b,hb⟩,rfl⟩
  have hk : U.subgroupOf B ≤ f.ker := by
    intro b hb
    apply Subtype.ext
    change QuotientGroup.mk' (pCore 2 H) (inclusion hBH b) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    exact (mem_map_iff_mem (f := H.subtype) H.subtype_injective).mp (hUQ hb)
  let fQ := QuotientGroup.lift (U.subgroupOf B) f hk
  have hfQ : Function.Surjective fQ := QuotientGroup.lift_surjective_of_surjective _ f hfs hk
  let F : Additive (B ⧸ U.subgroupOf B) →ₗ[ZMod 2] Additive A :=
    fQ.toAdditive.toZModLinearMap 2
  have hF (x : R) : F.comp (ρ x) = F := by
    apply LinearMap.ext
    intro b
    change F (ρ x (Additive.ofMul b.toMul)) = F (Additive.ofMul b.toMul)
    rw [hρ]
    apply Additive.toMul.injective
    change fQ (sectionAction R B U hRB hRU x b.toMul) = fQ b.toMul
    obtain ⟨b,hb⟩ := QuotientGroup.mk'_surjective (U.subgroupOf B) b.toMul
    rw [←hb]
    rw [sectionAction_apply]
    change f (B.normalizerMonoidHom (inclusion hRB x) b) = f b
    apply Subtype.ext
    change QuotientGroup.mk' (pCore 2 H) _ = QuotientGroup.mk' (pCore 2 H) _
    apply eq_of_mul_inv_eq_one
    rw [←map_inv,←map_mul]
    apply (QuotientGroup.eq_one_iff _).mpr
    apply (mem_map_iff_mem (f := H.subtype) H.subtype_injective).mp
    exact hcomm (commutator_mem_commutator x.property b.property)
  let L := Coinvariants.lift ρ F hF
  have hL : Function.Surjective L := by
    intro a
    obtain ⟨b,hb⟩ := hfQ a.toMul
    exact ⟨Coinvariants.mk ρ (Additive.ofMul b),congrArg Additive.ofMul hb⟩
  have hdim : Module.finrank (ZMod 2) (Additive A) ≤ 1 := by
    exact hd ▸ LinearMap.finrank_le_finrank_of_surjective hL
  change Nat.card (Additive A) ≤ 2
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  exact (Nat.pow_le_pow_right Nat.zero_lt_two hdim).trans_eq (pow_one 2)

/-- The original M22 quintet gives the literal image bound and the two
intersection alternatives in 8.2.9. -/
theorem selected_m22_code_parabolic_image
    {V H M I L U : Subgroup G} {T : Sylow 2 G} [IsElementaryAbelian 2 V]
    {i : I} {S : Sylow 2 I} (s : Selected H T M V I 1 i S)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hU : U = V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hIC : I ≤ centralizer (U : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hcomm : ⁅Normalizer.localResidual L U,centralizer (U : Set G)⁆ ≤
      (Normalizer.localResidual L U).pCoreIn 2)
    {f : Normalizer.localResidual L U →* MathieuCode.M22Quintet.Q}
    (hsec : M22FiveSection (Normalizer.localResidual L U) (V ⊓ I.pCoreIn 2) U f) :
    (Normalizer.localResidual L U).pCoreIn 2 ⊔ U ≤ H.pCoreIn 2 ∧
      Nat.card (((V ⊓ I.pCoreIn 2).subgroupOf H).map
        (QuotientGroup.mk' (pCore 2 H))) ≤ 2 ∧
      ((V ⊓ I.pCoreIn 2 = V ⊓ H.pCoreIn 2 ∧
        Nat.card ((V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 2) ∨
        Nat.card ((V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 4) := by
  let R := Normalizer.localResidual L U
  let B := V ⊓ I.pCoreIn 2
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  have hUB : U ≤ B := (selected_core_factor_geometry s U hU).2.1 ▸ inf_le_left
  have hTR := Normalizer.normalizes_localResidual L U (T : Subgroup G) hTL hTU
  have hQT : R.pCoreIn 2 ≤ (T : Subgroup G) :=
    (isPGroup_pCoreIn 2 R).le_sylow_of_normalized T
      (hTR.trans (normalizer_le_normalizer_characteristic_image R (pCore 2 R)))
  have hcore := SmallRows.localCore_join_le_parabolicCore L H I U (T : Subgroup G)
    (selected_generates_hstar s hH) T.isPGroup' hIC hTL hTU hQT
    ((hUB.trans inf_le_left).trans s.family.le_sylow) hcomm
  have hsmall : Nat.card ((B.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) ≤ 2 := by
    obtain ⟨hRB,hRU,hBU,r,eB,hrsur,hrker,hrval,hact,hkernel,hEl,ρ,hρ,hd5,hd4,hd1⟩ := hsec
    let := hBU
    let := hEl
    let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le (show B ≤ V from inf_le_left)
    exact section_image_card_le_two R B U H hRB hRU
      ((inf_le_left.trans hVI).trans s.family.le_ambient)
      (le_sup_right.trans hcore)
      (((commutator_mono le_rfl ((inf_le_left.trans hVI).trans hIC)).trans hcomm).trans
        (le_sup_left.trans hcore)) ρ hρ hd1
  exact ⟨hcore,hsmall,SmallRows.ambient_pair_intersection_alternatives V I B H
    hVI s.family.le_ambient rfl (selected_one_core_index s) hsmall⟩

/-- The same original M22 residual bounds both odd ranks in its parabolic. -/
theorem selected_m22_code_parabolic_odd_ranks
    {V H M I L U : Subgroup G} {T : Sylow 2 G} [IsElementaryAbelian 2 V]
    {i : I} {S : Sylow 2 I} (s : Selected H T M V I 1 i S)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hTM : (T : Subgroup G) ≤ M)
    (hIC : I ≤ centralizer (U : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hcomm : ⁅Normalizer.localResidual L U,centralizer (U : Set G)⁆ ≤
      (Normalizer.localResidual L U).pCoreIn 2)
    {f : Normalizer.localResidual L U →* MathieuCode.M22Quintet.Q}
    (hsec : M22FiveSection (Normalizer.localResidual L U) (V ⊓ I.pCoreIn 2) U f)
    (hthin : IsStronglyQuasithin (normalizer (U : Set G))) :
    primeRank 3 H ≤ 1 ∧ primeRank 5 H ≤ 1 := by
  have hgen := selected_generates_hstar s hH
  have hIM : ¬ I ≤ M := by
    intro hi
    apply hH.1.2
    rw [←hgen]
    exact sup_le hi hTM
  have hHN : H ≤ normalizer (U : Set G) := by
    rw [←hgen]
    exact sup_le (hIC.trans (Subgroup.centralizer_le_normalizer _)) hTU
  have hjoin : H ⊔ Normalizer.localResidual L U ≤ normalizer (U : Set G) :=
    sup_le hHN ((Normalizer.localResidual_le L U).trans inf_le_right)
  obtain ⟨hRB,hRU,hBU,r,eB,hrsur,hrker,_⟩ := hsec
  let e : (Normalizer.localResidual L U ⧸ pCore 2 (Normalizer.localResidual L U)) ≃*
      alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq hrker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective r hrsur)
  exact SmallRows.odd_ranks_of_local_alternating_five T L M H I U hH
    s.family.le_ambient hIM hIC hTL hTU hcomm e
    ((primeRank_mono 3 hjoin).trans (hthin 3 Nat.prime_three (by decide)))
    ((primeRank_mono 5 hjoin).trans (hthin 5 (by decide) (by decide)))

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
