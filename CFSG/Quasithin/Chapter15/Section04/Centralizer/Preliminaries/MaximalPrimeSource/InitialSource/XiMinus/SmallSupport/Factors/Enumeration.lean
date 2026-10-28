module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.SmallSupport.Factors.Generation
public import CFSG.Quasithin.Chapter1.Section03.FrattiniShape
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Exactly two canonical factors and their original Frattini images

The actual odd image is isomorphic, through its original projection, to
the Xi Frattini quotient of order25. Two distinct canonical order-five
factors therefore generate it. Independence in D.2.12 excludes any third
factor. Their literal images in X/O₂,Φ(X) are distinct order-five groups
and generate the entire quotient. Preservation by the module normalizer
is a separate remaining step; it is not included in these conclusions.
Source: Aschbacher--Smith, Lemma3.2.13, printed pp.584--585.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
variable {G : Type*} [Group G] [Finite G] {T X : Subgroup G}

theorem sourceOddImage_card (hX : X ∈ Chapter1.Xi G T)
    (hT : IsPGroup 2 T) (hred : IsPReduced 2 (sourceModule T X))
    (hk : SourceKernelInFrattini hX)
    (hratio : Representation.BinaryOffender.cubicRatio (sourceRepresentation hX) ≤ 2)
    (hp : Chapter1.XiOddQuotient 5 (Chapter1.XiQuotient X)) :
    Nat.card (sourceOddImage hX) = 25 := by
  let e := Equiv.ofBijective (sourceFrattiniProjection hX hk)
    ⟨sourceFrattiniProjection_injective hX hT hred hk hratio hp,
      sourceFrattiniProjection_surjective hX hk⟩
  exact (Nat.card_congr e).trans hp.frattini_card

theorem sourceFiveFactors_pair (hX : X ∈ Chapter1.Xi G T)
    (hT : IsPGroup 2 T) (hred : IsPReduced 2 (sourceModule T X))
    (hk : SourceKernelInFrattini hX)
    (hratio : Representation.BinaryOffender.cubicRatio (sourceRepresentation hX) ≤ 2)
    (hp : Chapter1.XiOddQuotient 5 (Chapter1.XiQuotient X)) :
    ∃ D C : Subgroup (sourceActionGroup hX),
      D ∈ sourceFiveFactors hX ∧ C ∈ sourceFiveFactors hX ∧ D ≠ C ∧
      D ⊔ C = sourceOddImage hX ∧ sourceFiveFactors hX = {D, C} := by
  classical
  let := sourceModule_normal hX
  let H := sourceActionGroup hX
  let P := sourceOddImage hX
  let W := Multiplicative (Additive (sourceModule T X))
  let := Representation.BinaryGroupAction.action (sourceRepresentation hX)
  let : IsElementaryAbelian 2 W := Representation.BinaryGroupAction.elementary
  let : FaithfulSMul H W := Representation.BinaryGroupAction.faithful
    (sourceRepresentation hX) (Representation.NormalElementaryQuotient.representation_injective _ _ _ _)
  have hgen := sourceFiveGroup_eq_oddImage hX hT hred hk hratio hp
  have hcard := sourceOddImage_card hX hT hred hk hratio hp
  have hle (D : Subgroup H) (hD : D ∈ sourceFiveFactors hX) : D ≤ P :=
    (le_sSup hD).trans hgen.le
  have hind : iSupIndep (fun D : sourceFiveFactors hX => D.val) :=
    (ChapterD.smallSupportFactors_internalDirectProduct (G := H) (V := W) (Or.inr rfl)).1
  obtain ⟨A, _, _, _, _, hD⟩ := source_five_canonical_support hX hT hred hratio hp
  let D := ⁅pCore 5 H, A⁆
  have hex : ∃ C ∈ sourceFiveFactors hX, C ≠ D := by
    by_contra hn
    push Not at hn
    have hs : sourceFiveGroup hX = D :=
      le_antisymm (sSup_le (fun C hC => (hn C hC).le)) (le_sSup hD)
    have hh := congrArg (fun K : Subgroup H => Nat.card K) (hs.symm.trans hgen)
    rw [hD.2.1, hcard] at hh
    norm_num at hh
  obtain ⟨C, hC, hCD⟩ := hex
  have hDC : D ≠ C := Ne.symm hCD
  have hCjoin : C ≤ ⨆ (F : sourceFiveFactors hX) (_ : F ≠ ⟨D, hD⟩), F.val := by
    exact le_iSup_of_le ⟨C, hC⟩ (le_iSup_of_le
      (show (⟨C, hC⟩ : sourceFiveFactors hX) ≠ ⟨D, hD⟩ from
        fun he => hCD (congrArg Subtype.val he)) le_rfl)
  have hdis : Disjoint D C := (hind ⟨D, hD⟩).mono_right hCjoin
  have hcD : C ≤ normalizer (D : Set H) :=
    (ChapterD.smallSupportFactors_commutingFamily (G := H) (V := W)
      (Or.inr rfl) C hC D hD).trans (Subgroup.centralizer_le_normalizer _)
  have hsup : D ⊔ C = P := by
    apply eq_of_le_of_card_ge (sup_le (hle D hD) (hle C hC))
    rw [card_sup_eq_mul_of_normalizes_of_disjoint D C hcD hdis, hD.2.1, hC.2.1, hcard]
  refine ⟨D, C, hD, hC, hDC, hsup, ?_⟩
  ext E
  constructor
  · intro hE
    by_cases hED : E = D
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Or.inl hED
    by_cases hEC : E = C
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Or.inr hEC
    have hother : D ⊔ C ≤ ⨆ (F : sourceFiveFactors hX) (_ : F ≠ ⟨E, hE⟩), F.val := by
      apply sup_le
      · exact le_iSup_of_le ⟨D, hD⟩ (le_iSup_of_le
          (fun he => hED (congrArg Subtype.val he).symm) le_rfl)
      · exact le_iSup_of_le ⟨C, hC⟩ (le_iSup_of_le
          (fun he => hEC (congrArg Subtype.val he).symm) le_rfl)
    have hz : E = ⊥ := by
      apply le_bot_iff.mp
      exact (le_inf le_rfl (hsup.symm ▸ hle E hE)).trans
        ((hind ⟨E, hE⟩).mono_right hother).le_bot
    have hEcard := hE.2.1
    rw [hz] at hEcard
    norm_num at hEcard
  · intro hE
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hE
    rcases hE with rfl | rfl
    · exact hD
    · exact hC

theorem source_canonical_frattini_pair (hX : X ∈ Chapter1.Xi G T)
    (hT : IsPGroup 2 T) (hred : IsPReduced 2 (sourceModule T X))
    (hk : SourceKernelInFrattini hX)
    (hratio : Representation.BinaryOffender.cubicRatio (sourceRepresentation hX) ≤ 2)
    (hp : Chapter1.XiOddQuotient 5 (Chapter1.XiQuotient X)) :
    ∃ D C : Subgroup (sourceActionGroup hX),
      D ∈ sourceFiveFactors hX ∧ C ∈ sourceFiveFactors hX ∧ D ≠ C ∧
      D ⊔ C = sourceOddImage hX ∧ sourceFiveFactors hX = {D, C} ∧
      let B := (D.subgroupOf (sourceOddImage hX)).map (sourceFrattiniProjection hX hk)
      let E := (C.subgroupOf (sourceOddImage hX)).map (sourceFrattiniProjection hX hk)
      Nat.card B = 5 ∧ Nat.card E = 5 ∧ B ≠ E ∧ B ⊔ E = ⊤ := by
  obtain ⟨D, C, hD, hC, hne, hsup, hfam⟩ :=
    sourceFiveFactors_pair hX hT hred hk hratio hp
  refine ⟨D, C, hD, hC, hne, hsup, hfam, ?_⟩
  dsimp only
  let P := sourceOddImage hX
  let f := sourceFrattiniProjection hX hk
  have hi := sourceFrattiniProjection_injective hX hT hred hk hratio hp
  have hDP : D ≤ P := (show D ≤ D ⊔ C from le_sup_left).trans hsup.le
  have hCP : C ≤ P := (show C ≤ D ⊔ C from le_sup_right).trans hsup.le
  have hcard (S : Subgroup (sourceActionGroup hX)) (hS : S ≤ P) (hc : Nat.card S = 5) :
      Nat.card ((S.subgroupOf P).map f) = 5 := by
    rw [card_map_of_injective hi,
      Nat.card_congr (subgroupOfEquivOfLe hS).toEquiv]
    exact hc
  refine ⟨hcard D hDP hD.2.1, hcard C hCP hC.2.1, ?_, ?_⟩
  · intro he
    apply hne
    have hm := congrArg (Subgroup.map P.subtype) ((map_injective hi) he)
    change (D.subgroupOf P).map P.subtype = (C.subgroupOf P).map P.subtype at hm
    simpa only [map_subgroupOf_eq_of_le hDP, map_subgroupOf_eq_of_le hCP] using hm
  · rw [← Subgroup.map_sup, ← subgroupOf_sup hDP hCP, hsup, subgroupOf_self,
      map_top_of_surjective _ (sourceFrattiniProjection_surjective hX hk)]

end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
