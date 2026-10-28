module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.Sections
public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Center
public import Theory.SpecificGroups.BinaryLinear.SylowCenters
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
/-!
# Separating the exceptional carriers from the binary four-space group

Orders distinguish J₂ and M₂₃ from PSL₄(2). PSL₃(4) has the same order,
but its Sylow two-center has order four; the binary four-space Sylow
center has order at most two. This supplies the actual model distinction
needed after a solvable quotient of a full-Sylow overgroup.
Source: Aschbacher–Smith A.3.12 and 13.6.27, pp.47–48,934.
-/
public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional
variable {X : Type*} [Group X]

private theorem linearThreeFour_not_binaryFour
    (eF : X ≃* Matrix.PSL3Four.PSL) : ¬ ClassicalGroup.IsPSL X 4 2 := by
  rintro ⟨E, _, _, hE, ⟨eE⟩⟩
  let := Fintype.ofFinite E
  let e : E ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hE]
    simp)
  let b := eF.symm.trans (eE.trans (Atlas.fieldEquivPSL 4 e))
  let S := Matrix.PSL3.LinearThree.unipotentSylow Matrix.PSL3Four.F (by decide : 0 < 2)
    (show Nat.card Matrix.PSL3Four.F = 2^2 from by
      simpa using GaloisField.card 2 2 (by decide))
  have h := BinaryLinear.psl_sylow_center_card_le_two (by decide : 2 ≤ 4)
    (S.mapSurjective (f := b.toMonoidHom) b.surjective)
  rw [← BinaryLinear.sylow_center_card_congr b S] at h
  have hc := Matrix.PSL3.LinearThree.card_center_sylow Matrix.PSL3Four.F (by decide : 0 < 2)
    (show Nat.card Matrix.PSL3Four.F = 2^2 from by
      simpa using GaloisField.card 2 2 (by decide)) S
  change Nat.card (center S) ≤ 2 at h
  change Nat.card (center S) = 4 at hc
  omega

/-- No exceptional carrier is the binary four-dimensional projective linear group. -/
theorem IsModel.not_binaryFour (h : IsModel X) : ¬ ClassicalGroup.IsPSL X 4 2 := by
  intro hm
  have hc : Nat.card X = 20160 := by
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
    rw [Nat.card_congr e.toEquiv]
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
    rw [hF] at hc
    norm_num [Fin.prod_univ_succ] at hc
    exact hc
  rcases h with h | h | h
  · obtain ⟨e⟩ := h
    have ho := (Nat.card_congr e.toEquiv).trans
      Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier
    omega
  · obtain ⟨e⟩ := h
    have ho := (Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.m23_order
    omega
  · exact linearThreeFour_not_binaryFour h.some hm

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional
