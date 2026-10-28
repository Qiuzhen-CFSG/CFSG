module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Complete
public import CFSG.Quasithin.ChapterB.Section03.Offenders.OddParity

/-!
# Fixed dimensions in the alternating branch of B.5.13

An elementary actor of rank at least two in A₈ fixes at most three dimensions
of its natural six-space. A larger fixed space would be an offender; the
proved B.3.2 list excludes every remaining possibility. The disjoint-swap
family is excluded by parity.

Source: Aschbacher–Smith, B.3.2 and B.5.13, printed pp.83–84 and 111–112.
-/

public section
open BinaryPermutation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceB513
open Offenders

theorem alternatingEight_natural_fixed_finrank_le_three
    (A : Subgroup (Equiv.Perm (Fin 8))) (hA : IsElementaryTwo A)
    (heven : A ≤ alternatingGroup (Fin 8)) (hr : 2 ≤ rank A) :
    Module.finrank (ZMod 2) (fixedSpace (naturalRepresentation (Fin 8)) A) ≤ 3 := by
  by_contra! hn
  have hd := fixedCodim_add_finrank (naturalRepresentation (Fin 8)) A
  rw [finrank_natural_even (Fin 8) (by decide)] at hd
  norm_num only [Fintype.card_fin] at hd
  have ho : IsOffender (naturalRepresentation (Fin 8)) A := ⟨hA, by omega⟩
  rcases EightExhaustion.caseBFamily_or_isRegularEight_of_isOffender_natural ho with
    hc | hc
  · rcases hc with hc | hc | hc | ⟨B, hB, _, hc⟩
    · exact hc.not_le_alternating heven
    · have hf := hc.fixedCodim_eq (naturalRepresentation (Fin 8))
      rw [Eight.fixedCodim_exceptional.2.2.2] at hf
      omega
    · have hf := hc.fixedCodim_eq (naturalRepresentation (Fin 8))
      rw [Eight.fixedCodim_evenPart.2.2.2] at hf
      omega
    · have hf := hc.fixedCodim_eq (naturalRepresentation (Fin 8))
      rw [(Eight.fixedCodim_hyperplane hB).2] at hf
      omega
  · have hf := fixedCodim_natural_regularEight hc
    omega

end CFSG.Quasithin.ChapterB.SourceB513
