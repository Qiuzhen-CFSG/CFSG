module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.JankoInvolutionSource
public import Theory.SpecificGroups.Janko4.Representations.InvolutionDisplacement
/-!
# Excluding the J₄ row on the original small C.5.12 source blocks

The literal centralizer-quotient image of K has an involution, and its
movement on the original reduced module is bounded by log₂|U(K)|.
A faithful J₄ action instead forces movement at least twelve. This
excludes the actual A₅ source and the natural degree-two source, including
its central layer. The latter degree is the small-group constraint in
A.3.12(17), which remains to be supplied by the surrounding row selection.
The proof uses neither full-Sylow faithfulness on K nor irreducibility.
Source: Aschbacher–Smith A.3.12(17), C.5.12, printed pp.48,163.
-/
public section

open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource ConjugateSource.RankOne DualOffender
variable {G : Type*} [Group G] [Finite G]
theorem short_small_displacement_not_jankoFour (K V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hK : IsShort K) (hUV : U K ≤ V) (hr : IsPReduced 2 V)
    (hcomm : ⁅V,K⁆ ≤ U K) (hcard : Nat.log 2 (Nat.card (U K)) < 12)
    (heven : 2 ∣ Nat.card (K ⧸ pCore 2 K)) :
    ¬ Nonempty (closureImage V K ≃* Janko4.Model) := by
  rintro ⟨e⟩
  let q := QuotientGroup.mk' (centralizer (V : Set G))
  have hd : 2 ∣ Nat.card (K.map q) := heven.trans (short_core_quotient_card_dvd_image K V hK hUV)
  obtain ⟨b,hb⟩ := exists_prime_orderOf_dvd_card' (G := K.map q) 2 hd
  obtain ⟨k,hk,hkb⟩ := b.property
  let a : closureImage V K := ⟨q k,mem_map_of_mem _ (le_normalClosure hk)⟩
  have ha : orderOf a = 2 := by
    rw [← Subgroup.orderOf_coe a]
    change orderOf (q k) = 2
    rw [hkb]
    simpa only [Subgroup.orderOf_coe] using hb
  have hlo := Janko4.BinaryDegree.twelve_le_fixedCodim_of_involution (movedRepresentation V K)
    (moved_faithful_of_reduced V K hr).1 e a ha
  have hup := moved_displacement_le_card V K (U K) hcomm k hk
  change fixedCodim (movedRepresentation V K) (zpowers a) ≤ _ at hup
  omega
omit [Finite G] in
private theorem source_u_subgroupOf_jankoFour (K X : Subgroup G) (hKX : K ≤ X) :
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


theorem noncubic_full_span_jankoFour_bound
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hUT : U K ≤ T) (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (hKX : K ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hVC : conjugateSpanBy (U K) X ≤ centralizer (U K : Set G))
    (hm : let D := conjugateSpanBy K X
      Nonempty (((D.subgroupOf X) ⧸ pCore 2 (D.subgroupOf X)) ≃* Janko4.Model)) :
    12 ≤ Nat.log 2 (Nat.card (U K)) := by
  let V := conjugateSpanBy (U K) X
  let D := conjugateSpanBy K X
  have hr := noncubic_full_span_reduced K T hK h3 hUT hT hTK X hKX S hS hVC
  let : (V.subgroupOf X).Normal := hr.normal
  let : IsElementaryAbelian 2 (V.subgroupOf X) := hr.elementary
  let q := QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X))
  have hshort : IsShort (K.subgroupOf X) := hK.chi.short.of_mulEquiv (subgroupOfEquivOfLe hKX).symm
  have hUX : U K ≤ X := (map_subtype_le _).trans hKX
  have hu := source_u_subgroupOf_jankoFour K X hKX
  have hUV : U (K.subgroupOf X) ≤ V.subgroupOf X := by
    rw [hu]
    exact subgroupOf_mono X (le_conjugateSpanBy (U K) X)
  have hSK : (S : Subgroup X) ≤ normalizer (K.subgroupOf X : Set X) := by
    rw [← subgroupOf_normalizer_eq hKX]
    intro s hs
    exact hTK (hS ▸ mem_map_of_mem X.subtype hs)
  have hc : ⁅V.subgroupOf X,K.subgroupOf X⁆ ≤ U (K.subgroupOf X) :=
    (commutator_mono hr.le_pCore le_rfl).trans
      (source_core_commutator_of_reduced _ _ hshort S hSK hr hUV).le
  have hcU : Nat.card (U (K.subgroupOf X)) = Nat.card (U K) := by
    rw [hu]
    exact Nat.card_congr (subgroupOfEquivOfLe hUX).toEquiv
  let eK := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKX))
  have hcK : Nat.card ((K.subgroupOf X) ⧸ pCore 2 (K.subgroupOf X)) =
      Nat.card (K ⧸ pCore 2 K) := Nat.card_congr eK.toEquiv
  have he : closureImage (V.subgroupOf X) (K.subgroupOf X) = (D.subgroupOf X).map q := by
    rw [closureImage,normalClosure_subgroupOf_eq_conjugateSpanBy K X hKX]
  obtain ⟨eD⟩ := (noncubic_full_span_kernel K T X hK h3 hUT hT hTK hKX hX S hS hVC).2.2.2.1
  let e := (MulEquiv.subgroupCongr he).trans (eD.symm.trans hm.some)
  obtain ⟨n,hn,hbinary⟩ := EmbeddingSelection.noncubic_binary_model K hK h3
  have heven : 2 ∣ Nat.card ((K.subgroupOf X) ⧸ pCore 2 (K.subgroupOf X)) := by
    rw [hcK,EmbeddingSelection.binary_card hbinary]
    exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _
  by_contra! hsmall
  exact short_small_displacement_not_jankoFour (K.subgroupOf X) (V.subgroupOf X) hshort hUV hr hc
    (by simpa only [hcU] using hsmall) heven ⟨e⟩

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
omit [Finite G] in
private theorem alternating_not_three_jankoFour {K : Subgroup G} (h : IsAlternatingBlock K 5) :
    ¬ IsAlternatingBlock K 3 := by
  intro h3
  obtain ⟨e5⟩ := h.2.2.quotient_iso
  obtain ⟨e3⟩ := h3.2.2.quotient_iso
  have hc := Nat.card_congr (e5.symm.trans e3).toEquiv
  have h5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card,card_alternatingGroup]
    decide
  have hthree : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [Nat.card_eq_fintype_card,card_alternatingGroup]
    decide
  rw [h5,hthree] at hc
  norm_num at hc

/-- J₄ is excluded for the full original A₅ span by an actual involution
of its centralizer-quotient image. No two-conjugate generation is needed. -/
theorem alternating_source_full_span_not_jankoFour
    {K T J : Subgroup G} (h : AlternatingPairSetup T K J)
    (hTK : T ≤ normalizer (K : Set G))
    (X : Subgroup G) (hKX : K ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hVC : conjugateSpanBy (U K) X ≤ centralizer (U K : Set G)) :
    let D := conjugateSpanBy K X
    ¬ Nonempty (((D.subgroupOf X) ⧸ pCore 2 (D.subgroupOf X)) ≃* Janko4.Model) := by
  dsimp only
  intro hm
  have hb := noncubic_full_span_jankoFour_bound K T X (Or.inr (Or.inr h.block))
    (alternating_not_three_jankoFour h.block) (h.module_le.trans inf_le_left) h.twoGroup hTK hKX hX S hS hVC hm
  have hc : Nat.card (U K) = 16 := h.module_card
  norm_num [hc] at hb

theorem natural_source_full_span_not_jankoFour
    {K T : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) (hn : IsL2EvenBlock K 2) (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G))
    (X : Subgroup G) (hKX : K ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hVC : conjugateSpanBy (U K) X ≤ centralizer (U K : Set G)) :
    let D := conjugateSpanBy K X
    ¬ Nonempty (((D.subgroupOf X) ⧸ pCore 2 (D.subgroupOf X)) ≃* Janko4.Model) := by
  dsimp only
  intro hm
  have hb := noncubic_full_span_jankoFour_bound K T X (Or.inl ⟨2,hn⟩)
    (natural_not_three_jankoFour hn) (h.module_le.trans inf_le_left) hT hTK hKX hX S hS hVC hm
  have hc := natural_module_card_le h hn
  rw [natural_coordinate_card h hn] at hc
  have hl := Nat.log_monotone (b := 2) hc
  norm_num at hl
  omega

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
