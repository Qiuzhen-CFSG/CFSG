module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.GaschutzComplement.Basic
public import Theory.GroupTheory.SylowCentralizerComplement

/-!
# The complement deduction at the end of 14.4.7

The preceding commutator bounds give the trivial action on DV/V, using the
actual quotient of I D by V. For a Sylow witness with the displayed carrier S,
apply odd-index cocycle averaging to A = L S. A corrected element vd fixes A;
both it and d fix S, so v ∈ C_V(S) ≤ C_{H^g}(U^g) = D. Consequently C_D(L)
is a literal complement to V₁^g in D, and multiplication gives V × C_D(L) ≃ DV.
This proves directly the binary splitting consequence cited as Gaschütz in the
source. No general Gaschütz theorem or source-specific complement is a premise.

The Sylow witness remains an explicit, undischarged premise of the consumer.
Its construction from 12.8.8(4)/G.2.5 is still required before this task, or source
14.4.7, is complete. The natural-module fixed-point condition, extraspecial
center equality, and preceding symmetric centralizer conclusions remain with
the source assembly owner; they are not bundled into a conclusion certificate.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
14.4.7, printed p.1009, final paragraph.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.GaschutzComplement
variable {G : Type*} [Group G]

/-- Conditional source consumer, with an actual Sylow witness for the displayed
candidate. Every other input is an earlier natural-module, extraspecial-center,
or preceding symmetric centralizer fact. The proof constructs C_D(L) itself,
including its relative complement property and the multiplication isomorphism.
The final implication uses the preceding uniqueness conclusion C_D(L)=1. -/
theorem source_complement_of_sylow [Finite G]
    (H U V V₁ V₂ L : Subgroup G) (g l : G) [IsMulCommutative V]
    (hg : g ∈ L) (hl : l ∈ L)
    (hgen : conjugateSpan U L = L ⊔ U)
    (hIV : conjugateSpan U L ≤ normalizer (V : Set G))
    (he : ∀ v ∈ V, v ^ 2 = 1)
    (hVU : V ≤ rightConjugate U g)
    (hUH : rightConjugate U g ≤ rightConjugate H g)
    (hbound : ∀ x ∈ L, ⁅conjugateCentralizer H U g, rightConjugate U x⁆ ≤
      rightConjugate V₁ x)
    (hline : ∀ x ∈ L, rightConjugate V₁ x ≤ V)
    (hW : U ⊓ centralizer (V₂ : Set G) ≤
      centralizer (conjugateCentralizer H U g : Set G))
    (hWl : rightConjugate U l ⊓ centralizer (V : Set G) ≤
      centralizer (conjugateCentralizer H U g : Set G))
    (hVL : V ⊓ centralizer (L : Set G) = ⊥)
    (hcenter : rightConjugate U g ⊓ centralizer (rightConjugate U g : Set G) =
      rightConjugate V₁ g)
    (P : Sylow 2 ↥(L ⊔ candidateSylow U V V₂ g l))
    (hP : (P : Subgroup ↥(L ⊔ candidateSylow U V V₂ g l)).map
      (L ⊔ candidateSylow U V V₂ g l).subtype = candidateSylow U V V₂ g l) :
    conjugateCentralizer H U g = rightConjugate V₁ g ⊔
      (conjugateCentralizer H U g ⊓ centralizer (L : Set G)) ∧
    ((conjugateCentralizer H U g ⊓ centralizer (L : Set G)).subgroupOf
      (conjugateCentralizer H U g)).IsComplement'
      ((rightConjugate V₁ g).subgroupOf (conjugateCentralizer H U g)) ∧
    (conjugateCentralizer H U g ⊓ centralizer (L : Set G) = ⊥ →
      conjugateCentralizer H U g = rightConjugate V₁ g) ∧
    ∃ e : V × ↥(conjugateCentralizer H U g ⊓ centralizer (L : Set G)) ≃*
      ↥(conjugateCentralizer H U g ⊔ V),
      ∀ v c, (e (v, c) : G) = (v : G) * (c : G) := by
  let D := conjugateCentralizer H U g
  let S := candidateSylow U V V₂ g l
  let A := L ⊔ S
  have hAI : A ≤ conjugateSpan U L := actor_le_span U V V₂ L hg hl hgen
  have hAV : A ≤ normalizer (V : Set G) := hAI.trans hIV
  have hAD : ⁅A, D⁆ ≤ V := (commutator_mono hAI le_rfl).trans
    (span_commutator_le U V V₁ L D hIV hbound hline)
  have hSD : S ≤ centralizer (D : Set G) := candidate_centralizes H U V V₂ g l hW hWl
  have hDP : D ≤ centralizer ((P : Subgroup A).map A.subtype : Set G) := by
    rw [hP]
    exact le_centralizer_iff.mp hSD
  have hfix : V ⊓ centralizer ((P : Subgroup A).map A.subtype : Set G) ≤ D := by
    rw [hP]
    exact inf_le_inf (hVU.trans hUH)
      (centralizer_le (show rightConjugate U g ≤ S from le_sup_left.trans le_sup_left))
  have hVA : V ⊓ centralizer (A : Set G) = ⊥ := by
    apply le_antisymm ?_ bot_le
    exact (inf_le_inf_left V (centralizer_le (show L ≤ A from le_sup_left))).trans_eq hVL
  have hDV : D ≤ centralizer (V : Set G) := inf_le_right.trans (centralizer_le hVU)
  have hCA : D ⊓ centralizer (A : Set G) = D ⊓ centralizer (L : Set G) :=
    centralizer_actor_eq L S D hSD
  have hcap : D ⊓ V = rightConjugate V₁ g :=
    centralizer_intersection H U V _ g hVU hUH hcenter (hline g hg)
  obtain ⟨hsplit, _, hcomp⟩ := Subgroup.centralizer_complement_of_sylow A V D hAV he P
    hAD hDP hfix hVA hDV
  have hprod := Subgroup.centralizer_directProduct_of_sylow A V D hAV he P
    hAD hDP hfix hVA hDV
  rw [hCA, hcap] at hsplit hcomp
  rw [hCA] at hprod
  refine ⟨hsplit, hcomp, ?_, hprod⟩
  intro hz
  change D ⊓ centralizer (L : Set G) = ⊥ at hz
  simpa only [hz, sup_bot_eq] using hsplit

/-- Normality is only asserted inside I D. -/
theorem quotient_layer_normal (I D V : Subgroup G)
    (hVI : V ≤ I) (hIV : I ≤ normalizer (V : Set G))
    (hDV : D ≤ centralizer (V : Set G)) : (V.subgroupOf (I ⊔ D)).Normal :=
  (normal_subgroupOf_iff_le_normalizer (hVI.trans le_sup_left)).mpr
    (sup_le hIV (hDV.trans (centralizer_le_normalizer _)))

/-- The literal images in (I D)/V commute; no ambient normality of V is used. -/
theorem quotient_centralizes (I D V : Subgroup G)
    (hVI : V ≤ I) (hIV : I ≤ normalizer (V : Set G))
    (hID : ⁅I, D⁆ ≤ V) [(V.subgroupOf (I ⊔ D)).Normal] :
    (I.subgroupOf (I ⊔ D)).map (QuotientGroup.mk' (V.subgroupOf (I ⊔ D))) ≤
      centralizer (((D ⊔ V).subgroupOf (I ⊔ D)).map
        (QuotientGroup.mk' (V.subgroupOf (I ⊔ D))) : Set (↥(I ⊔ D) ⧸ V.subgroupOf (I ⊔ D))) := by
  let J := I ⊔ D
  have hVJ : V ≤ J := hVI.trans le_sup_left
  have hDVJ : D ⊔ V ≤ J := sup_le le_sup_right hVJ
  have hJV : J ≤ normalizer (V : Set G) := le_normalizer_of_normal_subgroupOf hVJ
  have hpre : D ⊔ V ≤ commutatorPreimage J I V := by
    refine sup_le (le_commutatorPreimage le_sup_right ?_)
      (le_commutatorPreimage hVJ ?_)
    · rwa [commutator_comm]
    · exact le_normalizer_iff_commutator_le_left.mp hIV
  have hcomm : ⁅I, D ⊔ V⁆ ≤ V := by
    rw [commutator_comm]
    exact (commutator_mono hpre le_rfl).trans
      (commutator_commutatorPreimage_le J I V hJV)
  have hint : ⁅I.subgroupOf J, (D ⊔ V).subgroupOf J⁆ ≤ V.subgroupOf J := by
    apply (map_le_map_iff_of_injective J.subtype_injective).mp
    rw [map_commutator, map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le hDVJ, map_subgroupOf_eq_of_le hVJ]
    exact hcomm
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  exact hint

/-- Normality for the actual source quotient, from V ≤ U and V ≤ U^g. -/
theorem source_quotient_layer_normal (H U V L : Subgroup G) (g : G)
    (hVU : V ≤ U) (hVUg : V ≤ rightConjugate U g)
    (hIV : conjugateSpan U L ≤ normalizer (V : Set G)) :
    (V.subgroupOf (conjugateSpan U L ⊔ conjugateCentralizer H U g)).Normal :=
  quotient_layer_normal _ _ V (hVU.trans (le_conjugateSpan U L)) hIV
    (inf_le_right.trans (centralizer_le hVUg))

/-- The symmetric bounds make the source I centralize the image of DV in
(I D)/V. Use `source_quotient_layer_normal` for its normal-subgroup instance. -/
theorem source_quotient_centralizes (H U V V₁ L : Subgroup G) (g : G)
    (hVU : V ≤ U) (hIV : conjugateSpan U L ≤ normalizer (V : Set G))
    (hbound : ∀ x ∈ L, ⁅conjugateCentralizer H U g, rightConjugate U x⁆ ≤
      rightConjugate V₁ x)
    (hline : ∀ x ∈ L, rightConjugate V₁ x ≤ V)
    [(V.subgroupOf (conjugateSpan U L ⊔ conjugateCentralizer H U g)).Normal] :
    let I := conjugateSpan U L
    let D := conjugateCentralizer H U g
    (I.subgroupOf (I ⊔ D)).map (QuotientGroup.mk' (V.subgroupOf (I ⊔ D))) ≤
      centralizer (((D ⊔ V).subgroupOf (I ⊔ D)).map
        (QuotientGroup.mk' (V.subgroupOf (I ⊔ D))) : Set (↥(I ⊔ D) ⧸ V.subgroupOf (I ⊔ D))) :=
  quotient_centralizes _ _ V (hVU.trans (le_conjugateSpan U L)) hIV
    (span_commutator_le U V V₁ L _ hIV hbound hline)

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.GaschutzComplement
