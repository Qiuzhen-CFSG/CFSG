module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.Selection

/-!+# The selected ordinary A₇ replacement in Lemma 13.6.22

The Thompson/Baumann calculation chooses compatible seven-letter coordinates,
identifies Lᵥ with O²(N_K(S)), and places that normalizer in the stabilizer of
the seventh letter. Its two-residual is the actual subgroup K₁ used here.
The construction gives K₁/O₂(K₁) ≃ A₆ and Lᵥ ≤ K₁ ≤ K. The lifted Thompson
actor and movement of z then give membership in the literal Y_z family.
In particular the actual star image, without enlarging it by conjugates,
satisfies all X_z clauses, including commutator generation.

`source_replacement_mem_Yz` retains the coordinates of the construction;
`exists_source_replacement` gives the subgroup and the source chain
LᵥTᵥ ≤ K₁Tᵥ ≤ KTᵥ. The quotient orders also show that K₁ is not another
ordinary A₇ block. No placement, residual identity, actor witness, or
selection conclusion is an input to these theorems.

The remaining inputs are earlier source facts: normalization and Lᵥ ≤ K,
the elementary W_K ≤ Tᵥ and two-reduced plus action, the identification
U_K = [Z(O₂(K)),K] at the start of 13.6.22, relative normality in Mᵥ,
13.6.4–5, and the local {2,3}/Sylow-three information. The earlier module
and characteristic-normalizer owners supply the U_K identification.
This completes the replacement step; the enclosing small-model assembly
retains discharge of earlier inputs, C.1 block selection, and the separately
proved A₆ action/endgame. The final theorem is its explicit A₆ exclusion
reduction, not a claim to prove all of 13.6.22.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.6.22, printed p.932 (PDF p.949).
-/

public section

open Subgroup
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven

variable {G : Type*} [Group G] [Finite G]

/-- The actual A₆ core quotient prevents the replacement from returning to
the ordinary A₇ case. This uses the quotient isomorphisms, not a family tag. -/
theorem replacement_not_ordinarySeven (K : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) (x : Fin 7) :
    ¬ ChapterC.IsAlternatingBlock (replacement K e x) 7 := by
  intro h
  obtain ⟨e₇⟩ := h.2.2.quotient_iso
  have hc := Nat.card_congr ((replacementQuotientEquiv K e x).symm.trans e₇).toEquiv
  rw [nat_card_alternatingGroup, nat_card_alternatingGroup] at hc
  norm_num [Nat.factorial] at hc

variable (K L T M S : Subgroup G) (z v : G)
  (hblock : ChapterC.IsAlternatingBlock K 7)
  (hL : Tv T v ≤ normalizer (Lv L v : Set G))
  (hz : Tv T v ≤ centralizer ({z} : Set G))
  (hY : K ∈ Yz L T z v)
  (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
  (hS : S = ChapterB.baumann (Tv T v))
  [hW : IsElementaryAbelian 2 (WK K L T z v)]
  (hWT : WK K L T z v ≤ Tv T v)
  (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
  (hUK : ⁅WK K L T z v, K⁆ =
    ⁅((center (pCore 2 K)).map (pCore 2 K).subtype).map K.subtype, K⁆)
  (hLM : Lv L v ≤ Mv M v) (hLn : ((Lv L v).subgroupOf (Mv M v)).Normal)
  (h65 : Gv v ⊓ normalizer (S : Set G) ≤ Mv M v)
  (h23 : ∀ p : ℕ, p.Prime → p ∣ Nat.card (plusImage K L T z v hL hz (Lv L v)) →
    p = 2 ∨ p = 3)
  (P3 : Sylow 3 (plusImage K L T z v hL hz (Lv L v))) (hP3 : Nat.card P3 = 3)
  (hzL : ⁅zpowers z, Lv L v⁆ ≠ ⊥)

include hblock hY hK hLK hS hW hWT hR hUK hLM hLn h65 h23 P3 hP3 hzL

/-- Assemble the source placement, the actual A₆ quotient and every literal
Y_z clause on one and the same constructed residual lift. -/
theorem source_replacement_mem_Yz :
    ∃ e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7),
      Lv L v ≤ replacement K e 6 ∧ replacement K e 6 ≤ K ∧
      Tv T v ≤ normalizer (replacement K e 6 : Set G) ∧
      ⁅zpowers z, replacement K e 6⁆ ≠ ⊥ ∧
      IsPPerfect 2 (replacement K e 6) ∧
      Nonempty ((replacement K e 6 ⧸ pCore 2 (replacement K e 6)) ≃*
        alternatingGroup (Fin 6)) ∧
      replacement K e 6 ∈ Yz L T z v ∧
      starImage z v (replacement K e 6) ∈ Xz L T z v := by
  obtain ⟨e, hres, hN, hT, hLB, hBK, hn, hm, he, hw⟩ :=
    SourcePlacement.source_replacement K L T M S z v hblock hL hz hY hK hLK hS
      hWT hR hUK hLM hLn h65 h23 P3 hP3 hzL
  have hB := replacement_mem_Yz K L T S z v e 6 hY hres hN hT hzL hw
  have hsn := Source.starImage_normalizes_of_normalizes (Tv T v) (replacement K e 6)
    z v (hBK.trans hY.1.1) hn
  have hspan : conjugateSpanBy (starImage z v (replacement K e 6))
      (starImage z v (Tv T v)) = starImage z v (replacement K e 6) :=
    le_antisymm (conjugateSpanBy_le le_rfl hsn) (le_conjugateSpanBy _ _)
  refine ⟨e, hLB, hBK, hn, hm, replacement_twoPerfect K e 6, he, hB, ?_⟩
  simpa only [hspan] using hB.2.2

/-- The subgroup replacement in the ordinary A₇ paragraph, with genuine
selection, relative normalization, source product inclusions and A₆ quotient. -/
theorem exists_source_replacement :
    ∃ K₁ : Subgroup G, K₁ ∈ Yz L T z v ∧
      Lv L v ≤ K₁ ∧ K₁ ≤ K ∧ Tv T v ≤ normalizer (K₁ : Set G) ∧
      ⁅zpowers z, K₁⁆ ≠ ⊥ ∧ IsPPerfect 2 K₁ ∧
      Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* alternatingGroup (Fin 6)) ∧
      starImage z v K₁ ∈ Xz L T z v ∧
      (Lv L v ⊔ Tv T v ≤ K₁ ⊔ Tv T v) ∧
      (K₁ ⊔ Tv T v ≤ K ⊔ Tv T v) ∧ ¬ ChapterC.IsAlternatingBlock K₁ 7 := by
  obtain ⟨e, hLB, hBK, hn, hm, hp, he, hB, hs⟩ :=
    source_replacement_mem_Yz K L T M S z v hblock hL hz hY hK hLK hS
      hWT hR hUK hLM hLn h65 h23 P3 hP3 hzL
  exact ⟨replacement K e 6, hB, hLB, hBK, hn, hm, hp, he, hs,
    sup_le_sup_right hLB _, sup_le_sup_right hBK _, replacement_not_ordinarySeven K e 6⟩

/-- Feed the constructed member into the A₆ source case. The surrounding
small-model owner supplies the A₆ exclusion after C.1 selection and the
`BinaryRankTwo` action/endgame; no replacement or selection premise remains. -/
theorem false_of_source_and_alternatingSix_exclusion
    (hSix : ∀ B ∈ Yz L T z v,
      ¬ Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))) : False := by
  obtain ⟨e, _, _, _, _, _, he, hB, _⟩ :=
    source_replacement_mem_Yz K L T M S z v hblock hL hz hY hK hLK hS
      hWT hR hUK hLM hLn h65 h23 P3 hP3 hzL
  exact hSix (replacement K e 6) hB he

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven
