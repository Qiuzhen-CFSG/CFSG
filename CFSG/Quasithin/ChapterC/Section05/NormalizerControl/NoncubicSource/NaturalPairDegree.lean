module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.PairImageDegree
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.JankoFourInvolutionSource
/-!
# The natural source supplies the pair-image degree obstruction

The genuine natural block at field order four has U(K) of order at most
64, including its original central layer. Its full orbit span is reduced.
Transport to the literal host subgroup X supplies the short block,
Sylow normalization and characteristic-two hypotheses. The actual pair
image in X/O2(X) is SQTK by the original simple QTKE hypothesis.
Consequently each C-component of a pair image with trivial two-core has
central Fitting subgroup, with no assumed action or degree certificate.
The independent odd-core pair construction supplies that two-core condition.
Source: Aschbacher--Smith C.5.12, printed p.163.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource.RankOne Chapter1.Section02 DualOffender
universe u
variable {G : Type u} [Group G] [Finite G]
omit [Finite G] in
private theorem source_u_subgroupOf_pair (K X : Subgroup G) (hKX : K ≤ X) :
    U (K.subgroupOf X) = (U K).subgroupOf X := by
  let e := subgroupOfEquivOfLe hKX
  have he : (blockU (K.subgroupOf X)).map e.toMonoidHom = blockU K := by
    rw [blockU,map_commutator,pCore_map_iso,← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr e.surjective]
    rfl
  have hUX : U K ≤ X := (map_subtype_le _).trans hKX
  apply map_injective X.subtype_injective
  rw [map_subgroupOf_eq_of_le hUX]
  change ((blockU (K.subgroupOf X)).map (K.subgroupOf X).subtype).map X.subtype = _
  rw [map_map]
  change (blockU (K.subgroupOf X)).map (K.subtype.comp e.toMonoidHom) = _
  rw [← map_map,he]
  rfl
omit [Finite G] in
private theorem natural_not_three_jankoFour {K : Subgroup G} {n : ℕ} (hn : IsL2EvenBlock K n) :
    ¬ IsAlternatingBlock K 3 := by
  intro h3
  obtain ⟨F,_,_,hF,_,hm⟩ := hn.2.2
  obtain ⟨e⟩ := hm.quotient_iso
  obtain ⟨e3⟩ := h3.2.2.quotient_iso
  have hc : Nat.card (K ⧸ pCore 2 K) = 3 := by
    rw [Nat.card_congr e3.toEquiv,Nat.card_eq_fintype_card,card_alternatingGroup]
    decide
  have hle := Nat.card_le_card_of_injective (Matrix.SpecialLinearGroup.upperUnipotentHom F)
    (Matrix.SpecialLinearGroup.upperUnipotentHom_injective F)
  change Nat.card F ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) at hle
  rw [← Nat.card_congr e.toEquiv,hF,hc] at hle
  have hlo : 4 ≤ 2^n := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn.1
  omega

/-- The original natural block discharges both the degree and SQTK premises
for every literal pair image with trivial two-core. -/
theorem natural_source_pair_image_fitting_central
    {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    {K T : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) (hn : IsL2EvenBlock K 2) (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G))
    (X : Subgroup G) (hKX : K ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hVC : conjugateSpanBy (U K) X ≤ centralizer (U K : Set G))
    (g : X)
    (hO : pCore 2 (((K.subgroupOf X) ⊔ (K.subgroupOf X).conjBy g).map
      (QuotientGroup.mk' (pCore 2 X))) = ⊥)
    (L : Subgroup (((K.subgroupOf X) ⊔ (K.subgroupOf X).conjBy g).map
      (QuotientGroup.mk' (pCore 2 X)))) (hL : L.IsCComponent) :
    fittingSubgroup L ≤ center L := by
  have hK : IsChiZeroBlock K := Or.inl ⟨2,hn⟩
  have h3 : ¬ IsAlternatingBlock K 3 := natural_not_three_jankoFour hn
  let V := conjugateSpanBy (U K) X
  have hUV : U K ≤ V := le_conjugateSpanBy _ _
  have hUX : U K ≤ X := (map_subtype_le _).trans hKX
  have hVX : V ≤ X := conjugateSpanBy_le_self hUX
  have hr := noncubic_full_span_reduced K T hK h3 (h.module_le.trans inf_le_left)
    hT hTK X hKX S hS hVC
  have hshort : IsShort (K.subgroupOf X) := hK.chi.short.of_mulEquiv (subgroupOfEquivOfLe hKX).symm
  have hu := source_u_subgroupOf_pair K X hKX
  have hUiV : U (K.subgroupOf X) ≤ V.subgroupOf X := by
    rw [hu]
    exact subgroupOf_mono X hUV
  have hSK : (S : Subgroup X) ≤ normalizer (K.subgroupOf X : Set X) := by
    rw [← subgroupOf_normalizer_eq hKX]
    intro s hs
    exact hTK (hS ▸ mem_map_of_mem X.subtype hs)
  have hcU : Nat.card (U (K.subgroupOf X)) ≤ 64 := by
    have hc := natural_module_card_le h hn
    rw [natural_coordinate_card h hn] at hc
    rw [hu,Nat.card_congr (subgroupOfEquivOfLe hUX).toEquiv]
    norm_num at hc
    exact hc
  have hXH : X ∈ Chapter1.H G := by
    intro he
    have hU : U K = ⊥ := by
      apply bot_unique
      intro v hv
      have hcore : (⟨v,hVX (hUV hv)⟩ : X) ∈ pCore 2 X := hr.le_pCore (hUV hv)
      exact he ▸ mem_map_of_mem X.subtype hcore
    exact hK.chi.short.blockU_ne_bot ((map_eq_bot_iff_of_injective (blockU K) K.subtype_injective).mp hU)
  have hsq := (uniqueness_local_quotient_sqtk hG hXH).subgroup
    (((K.subgroupOf X) ⊔ (K.subgroupOf X).conjBy g).map (QuotientGroup.mk' (pCore 2 X)))
  exact reduced_pair_image_fitting_central _ _ hshort S hSK hr hUiV
    (Chapter1.mem_He_iff.mp hX) hcU g hsq hO L hL
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
