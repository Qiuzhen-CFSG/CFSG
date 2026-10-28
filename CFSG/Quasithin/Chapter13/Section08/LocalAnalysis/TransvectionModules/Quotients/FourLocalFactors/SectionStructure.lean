module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.Sections
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.Bar
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# The literal quotient and bar action in 13.8.6(4)

The standing abelianness of ⟨V^{G₁}⟩ makes V central in U_L, without
making U_L abelian. Normalization of the defining conjugate spans gives
the full and local actors. A bound [U_H,C_{LT}(V)] ≤ V propagates through
the L-conjugates using the relative commutator preimage. Since U_L itself
centralizes V and lies in LT, this bounds [U_L,U_L] by V. Its elementary
conjugate generators then make the literal U_L/V elementary abelian.
Sections.exists_section_representation constructs the bar action, which
is transported to the actual image in N_G(V)/C_{N_G(V)}(V).

We also prove the bar-kernel identification from C_L(V) being a two-group
and the standing C_T(V)=O₂(LT) identity. The local natural-module bound is
explicit in the conditional assembly below. SourceAction discharges it from
the marked natural model, and Assembly constructs the complete source section.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Notation
12.2.5(2), printed p.796; 13.7.3 and F.9.2–4, pp.936 and 318; and the
proof of 13.8.6(4), printed p.948 (PDF p.965).
-/

@[expose] public section

open Subgroup Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors.SectionStructure
variable {G : Type*} [Group G]

theorem V_le_UL (L H V V₃ : Subgroup G)
    (hgen : V = conjugateSpanBy V₃ L) : V ≤ Source.UL L H V₃ := by
  rw [hgen]
  exact conjugateSpanBy_mono (le_conjugateSpanBy V₃ H) le_rfl

theorem LT_normalizes_V (L T V V₃ : Subgroup G)
    (hgen : V = conjugateSpanBy V₃ L) (hTV : T ≤ normalizer (V : Set G)) :
    L ⊔ T ≤ normalizer (V : Set G) := by
  apply sup_le _ hTV
  rw [hgen]
  exact le_normalizer_conjugateSpanBy _ _

theorem LT_normalizes_UL (L H T V₃ : Subgroup G)
    (hTH : T ≤ H) (hTL : T ≤ normalizer (L : Set G)) :
    L ⊔ T ≤ normalizer (Source.UL L H V₃ : Set G) := by
  apply sup_le (le_normalizer_conjugateSpanBy _ _)
  exact normalizes_conjugate_span T (Source.UH H V₃) L
    (hTH.trans (le_normalizer_conjugateSpanBy _ _)) hTL

theorem L1T_normalizes_UH (H T L₁ V₃ : Subgroup G)
    (hL₁ : L₁ ≤ H) (hT : T ≤ H) :
    L₁ ⊔ T ≤ normalizer (Source.UH H V₃ : Set G) :=
  (sup_le hL₁ hT).trans (le_normalizer_conjugateSpanBy _ _)

theorem T_normalizes_K2 (H T V₂ : Subgroup G)
    (hTH : T ≤ H) (hTV₂ : T ≤ normalizer (V₂ : Set G)) :
    T ≤ normalizer (Source.K2 H V₂ : Set G) := by
  apply le_trans _ (normalizer_le_normalizer_characteristic_image
    (H ⊓ centralizer (V₂ : Set G)) (pResidual 2 (H ⊓ centralizer (V₂ : Set G) : Subgroup G)))
  exact (le_inf (hTH.trans H.le_normalizer)
    (hTV₂.trans (normalizer_le_normalizer_centralizer V₂))).trans
      inf_normalizer_le_normalizer_inf

theorem L2T_normalizes_U2 (H T L₂ V V₂ : Subgroup G)
    (hTH : T ≤ H) (hTV₂ : T ≤ normalizer (V₂ : Set G))
    (hTV : T ≤ normalizer (V : Set G))
    (hL₂V : L₂ ≤ normalizer (V : Set G))
    (hKL : Source.K2 H V₂ ≤ normalizer (L₂ : Set G)) :
    L₂ ⊔ T ≤ normalizer (Source.U2 H V V₂ : Set G) := by
  exact sup_le (actor_normalizes_conjugate_span V L₂ (Source.K2 H V₂) hL₂V hKL)
    (normalizes_conjugate_span T V (Source.K2 H V₂) hTV
      (T_normalizes_K2 H T V₂ hTH hTV₂))

/-- Restrict the actual global conclusion 13.8.2 to the chosen H ≤ G₁. -/
theorem VH_commutative_of_global_span (G₁ H V : Subgroup G)
    [IsMulCommutative (conjugateSpanBy V G₁)] (hH : H ≤ G₁) :
    IsMulCommutative (Source.VH H V) :=
  ⟨⟨fun x y => Subtype.ext (setLike_mul_comm (s := conjugateSpanBy V G₁)
    (conjugateSpanBy_mono le_rfl hH x.property)
    (conjugateSpanBy_mono le_rfl hH y.property))⟩⟩

theorem UL_centralizes_V (L H V V₃ : Subgroup G)
    [IsMulCommutative (Source.VH H V)] (hflag : V₃ ≤ V)
    (hLV : L ≤ normalizer (V : Set G)) :
    Source.UL L H V₃ ≤ centralizer (V : Set G) := by
  have hUV : Source.UH H V₃ ≤ Source.VH H V := conjugateSpanBy_mono hflag le_rfl
  have hcomm : ⁅Source.UH H V₃, V⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (commutator_mono hUV (le_conjugateSpanBy V H)).trans
      (commutator_self_eq_bot_iff.mpr (inferInstance : IsMulCommutative (Source.VH H V))).le
  exact conjugateSpanBy_le (commutator_eq_bot_iff_le_centralizer.mp hcomm)
    (hLV.trans (normalizer_le_normalizer_centralizer V))

theorem V_normal_in_UL (L H V V₃ : Subgroup G)
    [IsMulCommutative (Source.VH H V)] (hflag : V₃ ≤ V)
    (hgen : V = conjugateSpanBy V₃ L) :
    (V.subgroupOf (Source.UL L H V₃)).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  exact (UL_centralizes_V L H V V₃ hflag (by
    rw [hgen]; exact le_normalizer_conjugateSpanBy _ _)).trans (centralizer_le_normalizer _)

theorem UH_elementary (H V V₃ : Subgroup G)
    [IsElementaryAbelian 2 V] [IsMulCommutative (Source.VH H V)] (hflag : V₃ ≤ V) :
    IsElementaryAbelian 2 (Source.UH H V₃) := by
  let : IsMulCommutative (closure {x | ∃ h ∈ H, ∃ v ∈ V₃, h * v * h⁻¹ = x}) :=
    ⟨⟨fun x y => Subtype.ext (setLike_mul_comm (s := Source.VH H V)
      (conjugateSpanBy_mono hflag le_rfl x.property)
      (conjugateSpanBy_mono hflag le_rfl y.property))⟩⟩
  apply IsElementaryAbelian.closure_of_isMulCommutative
  rintro x ⟨h, hh, v, hv, rfl⟩
  rw [conj_pow, elemPow_eq_one_of_isElementaryAbelian v (hflag hv), mul_one, mul_inv_cancel]

theorem barKernel_map (P V : Subgroup G) :
    (barKernel P V).map P.subtype = P ⊓ centralizer (V : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, hy⟩
  · rintro ⟨hx, hv⟩
    exact ⟨⟨x, hx⟩, hv, rfl⟩

theorem LT_normalizes_barKernel (L T V : Subgroup G)
    (hPV : L ⊔ T ≤ normalizer (V : Set G)) :
    L ⊔ T ≤ normalizer (((L ⊔ T) ⊓ centralizer (V : Set G) : Subgroup G) : Set G) :=
  (le_inf (L ⊔ T).le_normalizer
    (hPV.trans (normalizer_le_normalizer_centralizer V))).trans
      inf_normalizer_le_normalizer_inf

/-- The bar kernel is a two-group once its intersection with L is one.
The quotient by L is covered by the given two-group T. -/
theorem barKernel_isPGroup (L T V : Subgroup G)
    (hT : IsPGroup 2 T) (hTL : T ≤ normalizer (L : Set G))
    (hCL : IsPGroup 2 (L ⊓ centralizer (V : Set G) : Subgroup G)) :
    IsPGroup 2 (barKernel (L ⊔ T) V) := by
  let P := L ⊔ T
  let N := L.subgroupOf P
  let _ : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hTL)
  have hs : N ⊔ T.subgroupOf P = ⊤ := by
    rw [← subgroupOf_sup (show L ≤ P from le_sup_left) (show T ≤ P from le_sup_right)]
    exact subgroupOf_self P
  have hq : IsPGroup 2 (P ⧸ N) :=
    isPGroup_quotient_of_sup_eq_top N (T.subgroupOf P) hT.comap_subtype hs
  intro c
  obtain ⟨n, hn⟩ := hq (QuotientGroup.mk' N c.val)
  have hcL : (c.val : G) ^ (2 ^ n) ∈ L := by
    change c.val ^ (2 ^ n) ∈ N
    apply (QuotientGroup.eq_one_iff (c.val ^ (2 ^ n))).mp
    change (QuotientGroup.mk' N) (c.val ^ (2 ^ n)) = 1
    rw [map_pow]
    exact hn
  let d : (L ⊓ centralizer (V : Set G) : Subgroup G) :=
    ⟨(c.val : G) ^ (2 ^ n), hcL, (centralizer (V : Set G)).pow_mem c.property _⟩
  obtain ⟨m, hm⟩ := hCL d
  refine ⟨n + m, Subtype.ext (Subtype.ext ?_)⟩
  have he := congrArg Subtype.val hm
  change ((c.val : G) ^ (2 ^ n)) ^ (2 ^ m) = 1 at he
  change (c.val : G) ^ (2 ^ (n + m)) = 1
  simpa only [← pow_mul, ← pow_add] using he

/-- This identifies the actual bar kernel with O₂(LT) using the standing
C_T(V)=O₂(LT) identity; no such identification is assumed in the action. -/
theorem barKernel_map_eq_core (L T V : Subgroup G)
    (hT : IsPGroup 2 T) (hTL : T ≤ normalizer (L : Set G))
    (hPV : L ⊔ T ≤ normalizer (V : Set G))
    (hCL : IsPGroup 2 (L ⊓ centralizer (V : Set G) : Subgroup G))
    (hCT : T ⊓ centralizer (V : Set G) = (L ⊔ T).pCoreIn 2) :
    (barKernel (L ⊔ T) V).map (L ⊔ T).subtype = (L ⊔ T).pCoreIn 2 := by
  apply le_antisymm
  · apply le_pCoreIn_of_normalizes
      ((barKernel_isPGroup L T V hT hTL hCL).map (L ⊔ T).subtype) (map_subtype_le _)
    rw [barKernel_map]
    exact LT_normalizes_barKernel L T V hPV
  · rw [barKernel_map, ← hCT]
    exact inf_le_inf le_sup_right le_rfl


theorem UL_barKernel_commutator_of_UH (L H T V V₃ : Subgroup G)
    (hPV : L ⊔ T ≤ normalizer (V : Set G))
    (hUP : Source.UL L H V₃ ≤ L ⊔ T)
    (hseed : ⁅Source.UH H V₃, (L ⊔ T) ⊓ centralizer (V : Set G)⁆ ≤ V) :
    ⁅Source.UL L H V₃, (barKernel (L ⊔ T) V).map (L ⊔ T).subtype⁆ ≤ V := by
  rw [barKernel_map]
  let C := (L ⊔ T) ⊓ centralizer (V : Set G)
  have hLC : L ≤ normalizer (C : Set G) :=
    le_sup_left.trans (LT_normalizes_barKernel L T V hPV)
  have hspan : Source.UL L H V₃ ≤ commutatorPreimage (L ⊔ T) C V :=
    conjugateSpanBy_le
      (le_commutatorPreimage ((le_conjugateSpanBy _ _).trans hUP) hseed)
      (commutatorPreimage_normalized (L ⊔ T) C V L hPV
        (le_sup_left.trans (L ⊔ T).le_normalizer) hLC (le_sup_left.trans hPV))
  exact (commutator_mono hspan le_rfl).trans
    (commutator_commutatorPreimage_le (L ⊔ T) C V hPV)

private theorem section_elementary (B Z D L : Subgroup G)
    [(Z.subgroupOf B).Normal] [IsElementaryAbelian 2 D]
    (hB : B = conjugateSpanBy D L) (hcomm : ⁅B, B⁆ ≤ Z) :
    IsElementaryAbelian 2 (B ⧸ Z.subgroupOf B) := by
  let q := QuotientGroup.mk' (Z.subgroupOf B)
  let : IsMulCommutative (B ⧸ Z.subgroupOf B) := by
    refine ⟨⟨?_⟩⟩
    intro x y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf B) x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf B) y
    rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (hcomm (commutator_mem_commutator a.property b.property))
  refine { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf B) x
  have hp (g : G) (hg : g ∈ conjugateSpanBy D L) :
      ∀ hb : g ∈ B, q ⟨g, hb⟩ ^ 2 = 1 := by
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨l, hl, d, hd, rfl⟩ := hg
      intro hb
      rw [← map_pow]
      apply (QuotientGroup.eq_one_iff _).mpr
      change (l * d * l⁻¹) ^ 2 ∈ Z
      rw [conj_pow, elemPow_eq_one_of_isElementaryAbelian d hd, mul_one, mul_inv_cancel]
      exact Z.one_mem
    | one => intro hb; change q 1 ^ 2 = 1; simp only [map_one, one_pow]
    | mul g k hg hk ihg ihk =>
      intro hb
      have hgB : g ∈ B := hB.symm ▸ hg
      have hkB : k ∈ B := hB.symm ▸ hk
      change q ((⟨g, hgB⟩ : B) * ⟨k, hkB⟩) ^ 2 = 1
      rw [map_mul, mul_pow, ihg hgB, ihk hkB, one_mul]
    | inv g hg ihg =>
      intro hb
      have hgB : g ∈ B := hB.symm ▸ hg
      change q ((⟨g, hgB⟩ : B)⁻¹) ^ 2 = 1
      rw [map_inv, inv_pow, ihg hgB, inv_one]
  exact hp b (hB ▸ b.property) b.property

theorem ULsection_elementary_of_UH (L H T V V₃ : Subgroup G)
    [IsElementaryAbelian 2 V] [IsMulCommutative (Source.VH H V)]
    [(V.subgroupOf (Source.UL L H V₃)).Normal]
    (hflag : V₃ ≤ V) (hPV : L ⊔ T ≤ normalizer (V : Set G))
    (hUP : Source.UL L H V₃ ≤ L ⊔ T)
    (hseed : ⁅Source.UH H V₃, (L ⊔ T) ⊓ centralizer (V : Set G)⁆ ≤ V) :
    IsElementaryAbelian 2 (Source.ULsection L H V₃ V) := by
  let := UH_elementary H V V₃ hflag
  apply section_elementary (Source.UL L H V₃) V (Source.UH H V₃) L rfl
  have hUC : Source.UL L H V₃ ≤ (barKernel (L ⊔ T) V).map (L ⊔ T).subtype := by
    rw [barKernel_map]
    exact le_inf hUP (UL_centralizes_V L H V V₃ hflag (le_sup_left.trans hPV))
  exact (commutator_mono le_rfl hUC).trans
    (UL_barKernel_commutator_of_UH L H T V V₃ hPV hUP hseed)

theorem exists_bar_action_of_UH (L H T V V₃ : Subgroup G)
    [IsElementaryAbelian 2 V] [IsMulCommutative (Source.VH H V)]
    (hflag : V₃ ≤ V) (hgen : V = conjugateSpanBy V₃ L)
    (hTH : T ≤ H) (hTL : T ≤ normalizer (L : Set G))
    (hTV : T ≤ normalizer (V : Set G))
    (hUP : Source.UL L H V₃ ≤ L ⊔ T)
    (hseed : ⁅Source.UH H V₃, (L ⊔ T) ⊓ centralizer (V : Set G)⁆ ≤ V) :
    let hPV := LT_normalizes_V L T V V₃ hgen hTV
    let hPB := LT_normalizes_UL L H T V₃ hTH hTL
    let _ := V_normal_in_UL L H V V₃ hflag hgen
    let _ := ULsection_elementary_of_UH L H T V V₃ hflag hPV hUP hseed
    let _ := barKernel_normal (L ⊔ T) V hPV
    ∃ ρ : Representation (ZMod 2) ((L ⊔ T : Subgroup G) ⧸ barKernel (L ⊔ T) V)
        (Additive (Source.ULsection L H V₃ V)),
      SectionConjugationAlong (L ⊔ T) (Source.UL L H V₃) V
        (QuotientGroup.mk' (barKernel (L ⊔ T) V)) hPB ρ := by
  let hPV := LT_normalizes_V L T V V₃ hgen hTV
  let hPB := LT_normalizes_UL L H T V₃ hTH hTL
  let _ := V_normal_in_UL L H V V₃ hflag hgen
  let _ := ULsection_elementary_of_UH L H T V V₃ hflag hPV hUP hseed
  let _ := barKernel_normal (L ⊔ T) V hPV
  exact exists_section_representation (L ⊔ T) (Source.UL L H V₃) V
    (barKernel (L ⊔ T) V) hPB hPV
    (UL_barKernel_commutator_of_UH L H T V V₃ hPV hUP hseed)

/-- The isomorphism to the actual image respects the canonical bar map. -/
theorem barEquivImage_mk (P V : Subgroup G) (hPV : P ≤ normalizer (V : Set G)) :
    let _ := barKernel_normal P V hPV
    ∀ p : P, barEquivImage P V hPV (QuotientGroup.mk' (barKernel P V) p) =
      (barMap P V hPV).rangeRestrict p := by
  dsimp only
  intro p
  apply Subtype.ext
  rfl

/-- Transport the constructed action to the literal image in Notation 12.2.5(2),
preserving its conjugation formula. -/
theorem bar_action_on_image (P B V : Subgroup G)
    [(V.subgroupOf B).Normal] [IsElementaryAbelian 2 (B ⧸ V.subgroupOf B)]
    (hPB : P ≤ normalizer (B : Set G)) (hPV : P ≤ normalizer (V : Set G)) :
    let _ := barKernel_normal P V hPV
    ∀ ρ : Representation (ZMod 2) (P ⧸ barKernel P V) (Additive (B ⧸ V.subgroupOf B)),
      SectionConjugationAlong P B V (QuotientGroup.mk' (barKernel P V)) hPB ρ →
      ∃ τ : Representation (ZMod 2) (barMap P V hPV).range (Additive (B ⧸ V.subgroupOf B)),
        SectionConjugationAlong P B V (barMap P V hPV).rangeRestrict hPB τ := by
  let _ := barKernel_normal P V hPV
  dsimp only
  intro ρ hρ
  let e := barEquivImage P V hPV
  refine ⟨ρ.comp e.symm.toMonoidHom, ?_⟩
  intro p b
  change ρ (e.symm ((barMap P V hPV).rangeRestrict p)) _ = _
  have he : e.symm ((barMap P V hPV).rangeRestrict p) =
      QuotientGroup.mk' (barKernel P V) p := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (barEquivImage_mk P V hPV p).symm
  rw [he]
  exact hρ p b

end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors.SectionStructure

end
