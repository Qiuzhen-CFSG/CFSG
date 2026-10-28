module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.DualOffender.Source
/-!
# Placing the genuine quadratic actors inside the source component image

The internal natural marking places the full actor in the block image.
For A₅ only its even pair-diagonal is used: it belongs to both actual
images, while the odd transpositions remain outside the block. Equality
of marked actions lifts through O₂(KT), which centralizes the span.
Source: Aschbacher–Smith C.5.13, printed pp.162–163.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
open ConjugateSource ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
/-- The natural alternative of the source setup carries its genuine internal marking. -/
theorem natural_internal {K T : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) {n : ℕ} (hn : IsL2EvenBlock K n) : h.coordinates.IsInternal := by
  rcases h.block with ⟨_,_,hi⟩ | ha
  · exact hi
  obtain ⟨e3⟩ := ha.2.2.quotient_iso
  have hc : Nat.card (K ⧸ pCore 2 K) = 3 := by
    rw [Nat.card_congr e3.toEquiv,Nat.card_eq_fintype_card,card_alternatingGroup]
    decide
  obtain ⟨hn,_,E,_,_,hE,_,hm⟩ := hn
  obtain ⟨e⟩ := hm.quotient_iso
  have hi := Nat.card_le_card_of_injective (Matrix.SpecialLinearGroup.upperUnipotentHom E)
    (Matrix.SpecialLinearGroup.upperUnipotentHom_injective E)
  change Nat.card E ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 2) E) at hi
  rw [← Nat.card_congr e.toEquiv,hc,hE] at hi
  have hfour : 4 ≤ 2^n := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
  omega

private theorem quotient_eq_of_module_difference (K T N V : Subgroup G)
    (hK : IsShort K) (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (hVN : V ≤ N) (hNV : N ≤ normalizer (V : Set G))
    (hPC : (K ⊔ T).pCoreIn 2 ≤ centralizer (V : Set G))
    (a b : N) (ha : (a : G) ∈ K ⊔ T) (hb : (b : G) ∈ K ⊔ T)
    (hd : (a : G) * (b : G)⁻¹ ∈ centralizer (U K : Set G)) :
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hVN).mpr hNV
    QuotientGroup.mk' (centralizer (V.subgroupOf N : Set N)) a =
      QuotientGroup.mk' (centralizer (V.subgroupOf N : Set N)) b := by
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hVN).mpr hNV
  apply (mul_inv_eq_one.mp ?_)
  rw [← map_inv,← map_mul]
  apply (QuotientGroup.eq_one_iff _).mpr
  have hc : (a : G)*(b : G)⁻¹ ∈ (K ⊔ T).pCoreIn 2 :=
    (CounterexampleCharacteristic.ReducedMarking.normal_short_extension_centralizer K T hK hT hTK) ▸
      ⟨(K ⊔ T).mul_mem ha ((K ⊔ T).inv_mem hb),hd⟩
  intro v hv
  exact Subtype.ext (hPC hc v hv)
/-- The genuine internal natural action places the entire original actor
inside the block image of the canonical auxiliary quotient. -/
theorem natural_actor_le_block_image {K T : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) (hi : h.coordinates.IsInternal) (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G))
    (N V : Subgroup G) (_hTN : T ≤ N) (hKN : K ≤ N)
    (hVN : V ≤ N) (hNV : N ≤ normalizer (V : Set G))
    (hPC : (K ⊔ T).pCoreIn 2 ≤ centralizer (V : Set G))
    {x : G} (hx : x ∈ normalizer (T : Set G)) :
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hVN).mpr hNV
    let q := QuotientGroup.mk' (centralizer (V.subgroupOf N : Set N))
    (((U K).map (MulAut.conj x⁻¹).toMonoidHom).subgroupOf N).map q ≤ (K.subgroupOf N).map q := by
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hVN).mpr hNV
  let q := QuotientGroup.mk' (centralizer (V.subgroupOf N : Set N))
  dsimp only
  rintro _ ⟨b,hb,rfl⟩
  have hbS := h.conjugate_le hx hb
  let bS : S T := ⟨b,hbS⟩
  obtain ⟨kS,hk,hparam⟩ := hi bS
  let kN : N := ⟨kS,hKN hk⟩
  have hd : (b : G) * (kN : G)⁻¹ ∈ centralizer (U K : Set G) := by
    apply (h.coordinates.parameter_kernel (bS*kS⁻¹)).mp
    rw [map_mul,map_inv,hparam,mul_inv_cancel]
  exact ⟨kN,hk,(quotient_eq_of_module_difference K T N V h.short hT hTK hVN hNV hPC b kN
    (mem_sup_right hbS.1) (mem_sup_left hk) hd).symm⟩
/-- The A₅ actor meets the block image nontrivially through its even
pair-diagonal involution; the odd transpositions are not placed in A₅. -/
theorem alternating_actor_inf_block_ne_bot {K T L : Subgroup G}
    (h : AlternatingPairSetup T K L) (hTK : T ≤ normalizer (K : Set G))
    (N V : Subgroup G) (hTN : T ≤ N) (hKN : K ≤ N)
    (hVN : V ≤ N) (hNV : N ≤ normalizer (V : Set G)) (hUV : sourceModule K ≤ V)
    (hPC : (K ⊔ T).pCoreIn 2 ≤ centralizer (V : Set G))
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hVN).mpr hNV
    let q := QuotientGroup.mk' (centralizer (V.subgroupOf N : Set N))
    ((((sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom).subgroupOf N).map q ⊓
      (K.subgroupOf N).map q : Subgroup _) ≠ ⊥ := by
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hVN).mpr hNV
  let q := QuotientGroup.mk' (centralizer (V.subgroupOf N : Set N))
  have hdK : pairDiagonal ∈ alternatingGroup (Fin 5) := by
    change Equiv.Perm.sign pairDiagonal = 1
    decide +kernel
  have hdD : pairDiagonal ∈ ChapterB.Offenders.D 5 := mul_mem
    (ChapterB.Offenders.pairSwap_mem (n := 5) (m := 2) 0 (by decide))
    (ChapterB.Offenders.pairSwap_mem (n := 5) (m := 2) 1 (by decide))
  have hdne : pairDiagonal ≠ 1 := by decide +kernel
  obtain ⟨k,hk,hkd⟩ := h.block_image.symm ▸ hdK
  obtain ⟨b,hb,hbd⟩ := (h.conjugate_action_image x hx hnc).symm ▸ hdD
  have hKS : K ⊔ ChapterB.baumann T ≤ K ⊔ T := sup_le_sup_left inf_le_left K
  have hAN : K ⊔ ChapterB.baumann T ≤ N := sup_le hKN (inf_le_left.trans hTN)
  let kN := inclusion hAN k
  let bN := inclusion hAN b
  have hd : ((b : G)*(k : G)⁻¹) ∈ centralizer (sourceModule K : Set G) := by
    have he : b*k⁻¹ ∈ h.action.ker := by
      change h.action (b*k⁻¹)=1
      rw [map_mul,map_inv,hbd,hkd,mul_inv_cancel]
    rw [h.action_kernel] at he
    exact he
  have he := quotient_eq_of_module_difference K T N V h.block.2.1 h.twoGroup hTK hVN hNV hPC
    bN kN (hKS b.property) (hKS k.property) hd
  have hmem : q kN ∈
      (((sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom).subgroupOf N).map q ⊓
        (K.subgroupOf N).map q := ⟨⟨bN,hb,he⟩,⟨kN,hk,rfl⟩⟩
  dsimp only
  intro hz
  have hq : q kN = 1 := hz.le hmem
  have hcv := (QuotientGroup.eq_one_iff _).mp hq
  have hcu : (k : G) ∈ centralizer (sourceModule K : Set G) := by
    intro u hu
    exact congrArg N.subtype (hcv ⟨u,hVN (hUV hu)⟩ (hUV hu))
  have hk1 : h.action k=1 := by
    apply MonoidHom.mem_ker.mp
    rw [h.action_kernel]
    exact hcu
  exact hdne (hkd.symm.trans hk1)
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
