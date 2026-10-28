module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.BlockRecognition.IrrPlus
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.BlockRecognition.SourceDisplacement
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.Parameters

/-!
# Irr⁺ on the original noncubic moved space

The literal K-image in N/C_N(V₁) is its original L₂(4) quotient, hence
contains a five-element. Its action on I=[V₁,L] has displacement bounded
by the full U(K). The source commutator and reducedness identities supply
full generation and faithfulness, proving Irr⁺ for the actual A₇ image.
The natural/A₅ markings discharge the numerical bound in the final wrappers.
Source: Aschbacher–Smith C.5.13, printed p.163.
-/
public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
open ConjugateSource.RankOne Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
/-- Literal source application to the surviving A₇ action image. -/
theorem noncubic_source_moved_isIrrPlus (K T X : Subgroup G)
    (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hfour : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4)
    (hsmall : Nat.log 2 (Nat.card (U K)) < 8) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    let hs := noncubic_source_span K T X hK h3 hT hUT hTK P hP hA hAX S hS
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
    let : IsElementaryAbelian 2 V := hs.1
    let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
    IsAlternating (closureImage (V.subgroupOf N) (K.subgroupOf N)) 7 →
      IsIrrPlus (movedRepresentation (V.subgroupOf N) (K.subgroupOf N)) ⊤ ⊤ := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  have hs := noncubic_source_span K T X hK h3 hT hUT hTK P hP hA hAX S hS
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
  let : IsElementaryAbelian 2 V := hs.1
  let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
  change IsAlternating (closureImage (V.subgroupOf N) (K.subgroupOf N)) 7 →
    IsIrrPlus (movedRepresentation (V.subgroupOf N) (K.subgroupOf N)) ⊤ ⊤
  intro hmodel
  have hKN : K ≤ N := le_inf (le_sup_left.trans hAX)
    (le_sup_left.trans ((K ⊔ T).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (K ⊔ T) (pCore 2 (K ⊔ T : Subgroup G)))))
  have hUN : U K ≤ N := (map_subtype_le _).trans hKN
  have hc : ⁅V.subgroupOf N,K.subgroupOf N⁆ ≤ (U K).subgroupOf N := by
    apply map_le_map_iff_of_injective N.subtype_injective |>.mp
    rw [map_commutator,map_subgroupOf_eq_of_le hs.2.1,map_subgroupOf_eq_of_le hKN,
      map_subgroupOf_eq_of_le hUN]
    exact hs.2.2.2.2.2.2.2.le
  have hU : Nat.log 2 (Nat.card ((U K).subgroupOf N)) < 8 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hUN).toEquiv]
    exact hsmall
  let q := QuotientGroup.mk' (centralizer (V.subgroupOf N : Set N))
  have hfive : 5 ∣ Nat.card ((K.subgroupOf N).map q) := by
    obtain ⟨e⟩ := (noncubic_source_quotient_action K T X hK h3 hT hUT hTK P hP hA hAX S hS).2.2.2
    rw [← Nat.card_congr e.toEquiv]
    have hc := EmbeddingSelection.binary_card (n := 2) (by simpa using hfour)
    norm_num at hc
    rw [hc]
    decide
  exact moved_isIrrPlus_of_reduced (V.subgroupOf N) (K.subgroupOf N) ((U K).subgroupOf N)
    hs.2.2.2.2.2.2.1 hc hU hfive hmodel
    (noncubic_source_moved_dual_fixed K T X hK h3 hT hUT hTK P hP hA hAX S hS)

/-- The original natural marking discharges the central-cover dimension bound. -/
theorem natural_source_moved_isIrrPlus (K T X : Subgroup G)
    (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hfour : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4)
    {F : Type*} [Field F] (h : Setup T K F)
    {n : ℕ} (hn : IsL2EvenBlock K n) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    let hs := noncubic_source_span K T X hK h3 hT hUT hTK P hP hA hAX S hS
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
    let : IsElementaryAbelian 2 V := hs.1
    let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
    IsAlternating (closureImage (V.subgroupOf N) (K.subgroupOf N)) 7 →
      IsIrrPlus (movedRepresentation (V.subgroupOf N) (K.subgroupOf N)) ⊤ ⊤ := by
  have hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^n) := hn.2.2.choose_spec.choose_spec.choose_spec.2.1
  have hn2 : n = 2 := (EmbeddingSelection.binary_two_valuation (lt_trans (by decide : 0 < 1) hn.1) hm).symm.trans
    (EmbeddingSelection.binary_two_valuation (by decide : 0<2) (by simpa using hfour))
  have hc := natural_module_card_le h hn
  rw [natural_coordinate_card h hn,hn2] at hc
  have hl := Nat.log_monotone (b := 2) hc
  norm_num at hl
  exact noncubic_source_moved_isIrrPlus K T X hK h3 hT hUT hTK P hP hA hAX S hS
    hfour (by omega)

/-- The original A₅ marking discharges the dimension bound. -/
theorem alternating_source_moved_isIrrPlus (K T X : Subgroup G)
    (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hfour : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4)
    {J : Subgroup G} (h : ConjugateSource.AlternatingPairSetup T K J) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    let hs := noncubic_source_span K T X hK h3 hT hUT hTK P hP hA hAX S hS
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
    let : IsElementaryAbelian 2 V := hs.1
    let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
    IsAlternating (closureImage (V.subgroupOf N) (K.subgroupOf N)) 7 →
      IsIrrPlus (movedRepresentation (V.subgroupOf N) (K.subgroupOf N)) ⊤ ⊤ := by
  have hc : Nat.card (U K) = 16 := h.module_card
  exact noncubic_source_moved_isIrrPlus K T X hK h3 hT hUT hTK P hP hA hAX S hS
    hfour (by rw [hc]; decide)

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
