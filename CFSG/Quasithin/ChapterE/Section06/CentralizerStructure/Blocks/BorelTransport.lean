module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.Models
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ChiTransport

/-!
# Transporting full block Borels

An isomorphism transports the original two-core quotient and the full
preimage of the marked model subgroup. These identities connect the local
C.1.29 marks inside an intermediate subgroup with the actual ambient block
in E.6.7; no containment is substituted for the full preimage equality.

Source: Aschbacher–Smith C.1.29 and E.6.7, printed pp.134 and 246.
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06
open Subgroup Theory.GroupTheory
variable {A B : Type*} [Group A] [Group B]

theorem L2BlockBorel.of_mulEquiv {P : Subgroup A} {n : ℕ}
    (h : L2BlockBorel A P n) (e : A ≃* B) :
    L2BlockBorel B (P.map e.toMonoidHom) n := by
  obtain ⟨F, _, _, hc, a, rfl⟩ := h
  let q := QuotientGroup.congr (pCore 2 A) (pCore 2 B) e (pCore_map_iso 2 e)
  refine ⟨F, inferInstance, inferInstance, hc, q.symm.trans a, ?_⟩
  rw [map_equiv_eq_comap_symm' e]
  rfl

theorem AlternatingBlockBorel.of_mulEquiv {P : Subgroup A} {n : ℕ}
    (h : AlternatingBlockBorel A P n) (e : A ≃* B) :
    AlternatingBlockBorel B (P.map e.toMonoidHom) n := by
  obtain ⟨a, i, rfl⟩ := h
  let q := QuotientGroup.congr (pCore 2 A) (pCore 2 B) e (pCore_map_iso 2 e)
  refine ⟨q.symm.trans a, i, ?_⟩
  rw [map_equiv_eq_comap_symm' e]
  rfl

end CFSG.Quasithin.ChapterE.Section06
