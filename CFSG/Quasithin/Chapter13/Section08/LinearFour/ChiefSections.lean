module

public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceApplication
public import Theory.GroupTheory.NoncentralChiefRefinement.BinarySections
public import Theory.GroupTheory.NoncentralChiefRefinement.SmallCommutator

/-!
# Chief factors in the final linear-four section

The H-normal lattice supplies genuine chief intervals inside H_C/V_H. Each
such factor is elementary abelian because H_C lies in O₂(H); no elementary
abelian hypothesis is placed on H_C/V_H. Its canonical conjugation action
descends through O₂(H), and the actual L₄(2) quotient makes a noncentral
action faithful. The existing full G.6.4 application then gives the marked
natural four-space, with order sixteen on the literal group section.

For an arbitrary chief series, one element of Uγ outside O₂(H) moves every
noncentral factor. The source bound on the literal image of Uγ ∩ H_C in
H_C/V_H limits the number of moved intervals to one. SourceExclusion uses
both results to contradict the separately supplied 13.8.31 obstruction.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), proof of 13.8.28, printed pp.965–966.
-/

public section
open Subgroup Representation NoncentralChiefRefinement
open BinaryLinear.OuterCyclic
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem quotient_simple (H : Subgroup G)
    (e : (H ⧸ pCore 2 H) ≃* LinearGroup 4) : IsSimpleGroup (H ⧸ pCore 2 H) := by
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 4 (by decide)
  exact (e.trans (projectiveEquivLinear (by decide : 0 < 4)).symm).isSimpleGroup

omit [Finite G] in
private theorem section_le_core (H QH HC : Subgroup G)
    (hQH : QH = H.pCoreIn 2) (hCQ : HC ≤ QH)
    (B : NormalNode H) (hBC : B.val.map H.subtype ≤ HC) : B.val ≤ pCore 2 H := by
  intro b hb
  have hh := hCQ (hBC (mem_map_of_mem H.subtype hb))
  rw [hQH] at hh
  exact (mem_map_iff_mem H.subtype_injective).mp hh

/-- Every actual noncentral chief interval inside H_C/V_H has its canonical
faithful irreducible H/O₂(H)-action and the marked natural four-space model. -/
theorem chief_section_four_model
    (H QH HC VH Uγ : Subgroup G) [IsElementaryAbelian 2 Uγ]
    (hQH : QH = H.pCoreIn 2) (hCQ : HC ≤ QH)
    (hU : Nat.card Uγ = 32) (hstar : QH.relIndex Uγ = 2)
    (hintersection : 8 ≤ Nat.card (Uγ ⊓ VH : Subgroup G))
    (hcomm : ⁅HC, Uγ⁆ ≤ HC ⊓ Uγ) (hUH : Uγ ≤ H)
    (hcover : IsSQTK KnownSimple.IsKnownSimple H)
    (e : (H ⧸ pCore 2 H) ≃* LinearGroup 4)
    (A B : NormalNode H) (hc : A ⋖ B) (hn : ¬ IsCentral A B)
    (hVA : VH ≤ A.val.map H.subtype) (hBC : B.val.map H.subtype ≤ HC) :
    ∃ hbin : IsElementaryAbelian 2 (Section A B),
      let _ := hbin
      ∃ σ : Representation (ZMod 2) (H ⧸ pCore 2 H) (Additive (Section A B)),
        Representation.IsIrreducible σ ∧ Function.Injective σ ∧
        σ.comp (QuotientGroup.mk' (pCore 2 H)) = binarySectionRepresentation A B ∧
        ChapterG.Section06.HasModelOn σ ⊤ ⊤ (ChapterG.Section06.binaryLinearAction 4) ∧
        Module.finrank (ZMod 2) (Additive (Section A B)) = 4 := by
  let _ := quotient_simple H e
  have hp : IsPGroup 2 B.val :=
    pCore_isPGroup.to_le (section_le_core H QH HC hQH hCQ B hBC)
  let hbin := chief_elementary A B hc hp
  let _ := hbin
  obtain ⟨σ, hirr, hf, hσ⟩ := binarySection_exists_faithful A B hc hn
  let _ := hirr
  have d : BinaryConjugationSection H (B.val.map H.subtype) (A.val.map H.subtype)
      (σ.comp (QuotientGroup.mk' (pCore 2 H))) := by
    rw [hσ]
    exact ambientBinarySection H A B hc.le
  obtain ⟨hm, hd⟩ := section_four_model H QH HC VH Uγ _ _ hQH σ hf d hVA hBC
    hCQ hU hstar hintersection hcomm hUH hcover e
  exact ⟨hbin, σ, hirr, hf, hσ, hm, hd⟩

/-- The four-dimensional conclusion is about the literal relative quotient. -/
theorem chief_section_card_sixteen
    (H QH HC VH Uγ : Subgroup G) [IsElementaryAbelian 2 Uγ]
    (hQH : QH = H.pCoreIn 2) (hCQ : HC ≤ QH)
    (hU : Nat.card Uγ = 32) (hstar : QH.relIndex Uγ = 2)
    (hintersection : 8 ≤ Nat.card (Uγ ⊓ VH : Subgroup G))
    (hcomm : ⁅HC, Uγ⁆ ≤ HC ⊓ Uγ) (hUH : Uγ ≤ H)
    (hcover : IsSQTK KnownSimple.IsKnownSimple H)
    (e : (H ⧸ pCore 2 H) ≃* LinearGroup 4)
    (A B : NormalNode H) (hc : A ⋖ B) (hn : ¬ IsCentral A B)
    (hVA : VH ≤ A.val.map H.subtype) (hBC : B.val.map H.subtype ≤ HC) :
    Nat.card (Section A B) = 16 := by
  obtain ⟨hbin, σ, _, _, _, _, hd⟩ := chief_section_four_model H QH HC VH Uγ
    hQH hCQ hU hstar hintersection hcomm hUH hcover e A B hc hn hVA hBC
  let _ := hbin
  have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (Section A B))
  rw [Nat.card_zmod, hd] at hh
  exact hh

/-- An actual H-chief series between V_H and H_C has at most one noncentral
factor. The source order-two image bound, rather than an assumed count, is used. -/
theorem chief_series_noncentral_count_le_one
    (H QH HC VH Uγ : Subgroup G)
    [(VH.subgroupOf HC).Normal]
    (hQH : QH = H.pCoreIn 2) (hVC : VH ≤ HC) (hCQ : HC ≤ QH)
    (hU : Nat.card Uγ = 32) (hstar : QH.relIndex Uγ = 2)
    (hintersection : 8 ≤ Nat.card (Uγ ⊓ VH : Subgroup G))
    (hcomm : ⁅HC, Uγ⁆ ≤ HC ⊓ Uγ) (hUH : Uγ ≤ H)
    (e : (H ⧸ pCore 2 H) ≃* LinearGroup 4)
    (s : ChiefSeries H) (hhead : s.head.val.map H.subtype = VH)
    (hlast : s.last.val.map H.subtype = HC) : s.noncentralTwoCount ≤ 1 := by
  let _ := quotient_simple H e
  have hsmall := intersection_quotient_image_card_le_two Uγ HC VH QH
    hVC hCQ hU hstar hintersection
  rw [← relIndex_ker, QuotientGroup.ker_mk'] at hsmall
  change (VH.comap HC.subtype).relIndex (Uγ.subgroupOf HC) ≤ 2 at hsmall
  rw [relIndex_comap, subgroupOf_map_subtype] at hsmall
  have hnot : ¬ Uγ ≤ QH := by
    intro hu
    have hh := relIndex_eq_one.mpr hu
    omega
  obtain ⟨a, ha, hna⟩ := SetLike.not_le_iff_exists.mp hnot
  let aH : H := ⟨a, hUH ha⟩
  have hnaH : aH ∉ pCore 2 H := by
    intro hh
    apply hna
    rw [hQH]
    exact mem_map_of_mem H.subtype hh
  apply small_relative_index_moving_steps
    (fun i => (s i).val.map H.subtype)
    (fun i j hij => map_mono (s.strictMono.monotone hij)) VH (Uγ ⊓ HC)
    hhead.ge hsmall (fun i => IsNoncentralTwo (s i.castSucc) (s i.succ))
  intro i hi
  have hBC : (s i.succ).val.map H.subtype ≤ HC := by
    rw [← hlast]
    exact map_mono (CompositionSeries.le_last i.succ)
  have hp : IsPGroup 2 (s i.succ).val :=
    pCore_isPGroup.to_le (section_le_core H QH HC hQH hCQ _ hBC)
  obtain ⟨b, hb, hn⟩ := exists_moving_commutator _ _ (s.step i) hp hi.2 aH hnaH
  have hbC : (b : G) ∈ HC := hBC (mem_map_of_mem H.subtype hb)
  have hc : ⁅a, (b : G)⁆ ∈ HC ⊓ Uγ := by
    apply hcomm
    rw [commutator_comm]
    exact commutator_mem_commutator ha hbC
  refine ⟨⁅a, (b : G)⁆, ⟨hc.2, hc.1⟩, ?_, ?_⟩
  · have hm : ⁅aH, b⁆ ∈ (s i.succ).val := by
      simpa only [commutatorElement_def] using
        ((s i.succ).val.mul_mem ((s i.succ).property.conj_mem b hb aH)
          ((s i.succ).val.inv_mem hb))
    exact mem_map_of_mem H.subtype hm
  · intro hh
    exact hn ((mem_map_iff_mem H.subtype_injective).mp hh)

end CFSG.Quasithin.Chapter13.Section08.LinearFour
