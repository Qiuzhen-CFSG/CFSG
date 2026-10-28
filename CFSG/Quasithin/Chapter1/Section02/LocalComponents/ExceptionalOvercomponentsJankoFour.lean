module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.ContainingModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.JankoFour
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.MathieuTwentyFour
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu

/-!
# The M₂₃ local-overcomponent branch from a restricted J₄ model input

The prime-23 maximal Sylow-overgroup input places the actual local M₂₃
section in the native E2048.M24 subgroup. Its literal two-core quotient
is M₂₄, where the proved section exclusion gives a contradiction.
The resulting equality with the containing component is transported
through the original local join and its two-core quotient.

The intrinsic J₄ overgroup input is an explicit, unproved premise.
This module proves its full local consumer, not the unconditional
exceptional overcomponent theorem.

Source: Aschbacher–Smith A.3.12(17), pp.47–48, and 1.2.8, pp.506–507.
-/

public section
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
  Janko4.Cardinality.max1Subgroup Janko4.Cardinality.localKernel
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings

/-- The intrinsic J₄ Sylow-overgroup fact needed only in the prime-23 branch.
This is a contract, not an assertion of maximal-overgroup coverage. -/
@[expose] def JankoFourTwentyThreeOvergroups : Prop :=
  ∀ (T : Sylow 2 Janko4.Model) (M : Subgroup Janko4.Model),
    IsCoatom M → (T : Subgroup Janko4.Model) ≤ M → 23 ∣ Nat.card M →
      Nonempty (M ≃* Janko4.Cardinality.max1Subgroup
        Janko4.matrixA_mul_self Janko4.matrixB_pow_four)

/-- The actual M₂₄ quotient of max1 rules out the normalized exceptional section. -/
private theorem not_max1_section
    (S : Sylow 2 (Janko4.Cardinality.max1Subgroup
      Janko4.matrixA_mul_self Janko4.matrixB_pow_four))
    (B : Subgroup (Janko4.Cardinality.max1Subgroup
      Janko4.matrixA_mul_self Janko4.matrixB_pow_four))
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup (Janko4.Cardinality.max1Subgroup
      Janko4.matrixA_mul_self Janko4.matrixB_pow_four)) ≤
        normalizer (B : Set (Janko4.Cardinality.max1Subgroup
          Janko4.matrixA_mul_self Janko4.matrixB_pow_four)))
    (h : Exceptional.IsModel (B ⧸ pCore 2 B)) : False := by
  let q := QuotientGroup.mk' (Janko4.Cardinality.localKernel
    Janko4.matrixA_mul_self Janko4.matrixB_pow_four)
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk', Janko4.LocalStructure.localKernel_eq_twoCore]
    let := pCore_isNilpotent (p := 2) (G := Janko4.Cardinality.max1Subgroup
      Janko4.matrixA_mul_self Janko4.matrixB_pow_four)
    infer_instance
  obtain ⟨hb,hs,hm⟩ := Exceptional.local_section_map hB hn h q
  exact Exceptional.not_mathieu_twentyFour
    (S.mapSurjective (QuotientGroup.mk'_surjective _)) (B.map q) hb hs hm
    (Janko4.LocalStructure.localQuotientEquivM24
      Janko4.matrixA_mul_self Janko4.matrixB_pow_four)

/-- The restricted intrinsic overgroup fact excludes a local M₂₃ section in J₄.
All local membership and quotient transports are discharged here. -/
theorem not_mathieuTwentyThree_in_jankoFour_of_overgroups
    (hcover : JankoFourTwentyThreeOvergroups) (hO : pCore 2 Janko4.Model = ⊥)
    (S : Sylow 2 Janko4.Model) (B : Subgroup Janko4.Model)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup Janko4.Model) ≤ normalizer (B : Set Janko4.Model))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* Sporadic.Mathieu.M23)) : False := by
  have hm : Exceptional.IsModel (B ⧸ pCore 2 B) := Or.inr (Or.inl h)
  obtain ⟨N,hN,hBN,hSN⟩ := Exceptional.jankoFour_exists_twoLocal S B hB hn hm
    (MulEquiv.refl _)
  have hproper : N ≠ ⊤ := by
    intro he
    obtain ⟨Q,hQ,hp,hNQ⟩ := hN
    have hnormal : Q.Normal := normalizer_eq_top_iff.mp (hNQ.symm.trans he)
    have hle : Q ≤ pCore 2 Janko4.Model := le_sSup ⟨hnormal,hp⟩
    exact hQ (eq_bot_iff.mpr (hO ▸ hle))
  obtain ⟨M,hM,hNM⟩ := (eq_top_or_exists_le_coatom N).resolve_left hproper
  have hSM := hSN.trans hNM
  have hBM := hBN.trans hNM
  have h23 : 23 ∣ Nat.card M := by
    have hc : Nat.card (B ⧸ pCore 2 B) = 10200960 :=
      (Nat.card_congr h.some.toEquiv).trans Sporadic.Mathieu.m23_order
    exact (by decide : 23 ∣ 10200960).trans ((hc ▸ card_quotient_dvd_card (pCore 2 B)).trans
      (card_dvd_of_le hBM))
  obtain ⟨e⟩ := hcover S M hM hSM h23
  let P := S.subtype hSM
  have hl : B.subgroupOf M ∈ localCComponents P := local_restrict hB hBM
  have hnorm : (P : Subgroup M) ≤ normalizer (B.subgroupOf M : Set M) := by
    intro s hs
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp (hn hs) (x : Janko4.Model)
  have hsmall : Exceptional.IsModel ((B.subgroupOf M) ⧸ pCore 2 (B.subgroupOf M)) :=
    hm.of_equiv (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hBM)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hBM)))
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    infer_instance
  obtain ⟨hl',hn',hm'⟩ := Exceptional.local_section_map hl hnorm hsmall e.toMonoidHom
  exact not_max1_section (P.mapSurjective (f := e.toMonoidHom) e.surjective)
    ((B.subgroupOf M).map e.toMonoidHom) hl' hn' hm'

end CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents

namespace CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The one intrinsic J₄ placement premise closes every proper M₂₃ embedding. -/
theorem eq_of_mathieuTwentyThree_containing_of_jankoFour_overgroups
    (hcover : JankoFourTwentyThreeOvergroups)
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B ≤ K)
    (hn : (T : Subgroup G) ≤ normalizer (B : Set G))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* Sporadic.Mathieu.M23)) : B = K := by
  obtain ⟨S,_,hl,hs⟩ := exists_local_sylow_normalizing T hB hK.subnormal hBK hn
  have hsmall : Nonempty (((B.subgroupOf K) ⧸ pCore 2 (B.subgroupOf K)) ≃*
      Sporadic.Mathieu.M23) :=
    ⟨(QuotientGroup.congr _ _ (subgroupOfEquivOfLe hBK)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hBK))).trans h.some⟩
  rcases Exceptional.containing_models_of_core_eq_bot hG hO T hB hK hBK hn
    (Or.inr (Or.inl h)) with he | hJ | hM | hJ4
  · exact he
  · have hd : Nat.card (B ⧸ pCore 2 B) ∣ Nat.card K :=
      (card_quotient_dvd_card _).trans (card_dvd_of_le hBK)
    rw [Nat.card_congr h.some.toEquiv, Sporadic.Mathieu.m23_order,
      Nat.card_congr hJ.some.toEquiv,
      Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier] at hd
    norm_num at hd
  · apply le_antisymm hBK
    apply subgroupOf_eq_top.mp
    apply (B.subgroupOf K).eq_top_of_card_eq
    apply le_antisymm (Nat.card_le_card_of_injective (B.subgroupOf K).subtype
      (B.subgroupOf K).subtype_injective)
    rw [Nat.card_congr hM.some.toEquiv, ← Nat.card_congr hsmall.some.toEquiv]
    exact Nat.card_le_card_of_surjective (QuotientGroup.mk' (pCore 2 (B.subgroupOf K)))
      (QuotientGroup.mk'_surjective _)
  · obtain ⟨e⟩ := hJ4
    have hOK : pCore 2 K = ⊥ := by
      rw [pCore_subnormal_eq_comap 2 hK.subnormal, hO]
      exact (K.subtype.ker_eq_bot K.subtype_injective)
    have hOJ : pCore 2 Janko4.Model = ⊥ := by
      rw [← pCore_map_iso 2 e, hOK, Subgroup.map_bot]
    let : Group.IsSolvable e.toMonoidHom.ker := by
      rw [e.toMonoidHom.ker_eq_bot e.injective]
      infer_instance
    have hl' := localCComponents_map_of_solvable_ker hl e.toMonoidHom
    have hs' := (map_mono hs).trans (le_normalizer_map e.toMonoidHom)
    let eB := QuotientGroup.congr _ _ (e.subgroupMap (B.subgroupOf K))
      (pCore_map_iso 2 (e.subgroupMap (B.subgroupOf K)))
    exact (not_mathieuTwentyThree_in_jankoFour_of_overgroups hcover hOJ
      (S.mapSurjective (f := e.toMonoidHom) e.surjective) ((B.subgroupOf K).map e.toMonoidHom)
      hl' hs' ⟨eB.symm.trans hsmall.some⟩).elim
end CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents

namespace CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Apply the restricted J₄ model premise to the literal local M₂₃ quotient.
No local transport, equality of quotients, or containing-model premise remains. -/
theorem mathieuTwentyThree_local_overcomponent_of_jankoFour_overgroups
    (hcover : JankoFourTwentyThreeOvergroups)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {X K : Subgroup G}
    (hX : X ∈ L G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hK : K ∈ L G (T : Subgroup G)) (hXK : X ≤ K)
    (h : Nonempty ((X ⧸ pCore 2 X) ≃* Sporadic.Mathieu.M23)) :
    Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M23) := by
  let H := K ⊔ (T : Subgroup G)
  have hXH : X ≤ H := hXK.trans le_sup_left
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  have hx : X.subgroupOf H ∈ L H (S : Subgroup H) :=
    (mem_LIn_iff_subgroupOf le_sup_right hXH).mp ⟨hXH,hX⟩
  have hn' : (S : Subgroup H) ≤ normalizer (X.subgroupOf H : Set H) := by
    intro s hs
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp (hn hs) (x : G)
  let q := QuotientGroup.mk' (pCore 2 H)
  let Sbar := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have hbar : (X.subgroupOf H).map q ∈ localCComponents Sbar :=
    mem_L_map_twoCore_mem_localCComponents hx
  have hnorm : (Sbar : Subgroup (H ⧸ pCore 2 H)) ≤
      normalizer ((X.subgroupOf H).map q : Set _) :=
    (map_mono hn').trans (le_normalizer_map q)
  have hq := uniqueness_local_quotient_sqtk hG hK.2.2
  let eX := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hXH)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hXH))
  have hkX : IsPGroup 2 (q.subgroupMap (X.subgroupOf H)).ker := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let eB := MonoidHom.quotientPCoreEquivOfSurjective
    (q.subgroupMap (X.subgroupOf H)) (q.subgroupMap_surjective _) hkX
  have hm : Nonempty ((((X.subgroupOf H).map q) ⧸ pCore 2 ((X.subgroupOf H).map q)) ≃*
      Sporadic.Mathieu.M23) := ⟨eB.symm.trans (eX.trans h.some)⟩
  let := pCore_isNilpotent (p := 2) (G := H)
  have he := eq_of_mathieuTwentyThree_containing_of_jankoFour_overgroups hcover
    hq (pCore_quotient_pCore_eq_bot 2) Sbar hbar (hK.1.map_quotient _)
    (map_mono (comap_mono hXK)) hnorm hm
  rw [he] at hm
  have hkK : IsPGroup 2 (q.subgroupMap (K.subgroupOf H)).ker := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let eC := MonoidHom.quotientPCoreEquivOfSurjective
    (q.subgroupMap (K.subgroupOf H)) (q.subgroupMap_surjective _) hkK
  let eK := QuotientGroup.congr _ _ (subgroupOfEquivOfLe (show K ≤ H from le_sup_left))
    (pCore_map_iso 2 (subgroupOfEquivOfLe (show K ≤ H from le_sup_left)))
  exact ⟨eK.symm.trans (eC.trans hm.some)⟩
end CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents
