module
public import Theory.GroupAction.NormalPChiefSeries.Linear
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport
public import Theory.Representation.BinaryOffender.GeneratingFiltration

/-!
# A finite filtration by normalized internal subgroups

A subgroup normalized by the actor defines its literal subrepresentation in
an elementary abelian normal subgroup. Its vector space is linearly identified
with the same internal group. A generating family gives a finite sequence
whose successive sums exhaust the module, preserving each specified generator.

Source application: Aschbacher–Smith D.1.3(a–b), printed pp.173–174.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement
open scoped IsMulCommutative
namespace Representation.BinaryOffender
variable {H : Type*} [Group H] (U : Subgroup H) [U.Normal]
  [IsElementaryAbelian 2 U] (B W : Subgroup H) (hBW : B ≤ normalizer (W : Set H))

noncomputable def internalGenerator : Subrepresentation ((normalRepresentation U).comp B.subtype) where
  toSubmodule := AddSubgroup.toZModSubmodule 2 (W.subgroupOf U).toAddSubgroup
  apply_mem_toSubmodule b v hv := le_normalizer_iff.mp hBW b b.property v.toMul hv

noncomputable def internalGeneratorEquiv [IsElementaryAbelian 2 W] (hWU : W ≤ U) :
    Additive W ≃ₗ[ZMod 2] (internalGenerator U B W hBW).toSubmodule := by
  letI : IsElementaryAbelian 2 (W.subgroupOf U) := IsElementaryAbelian.subgroupOf hWU
  let e := (subgroupOfEquivOfLe hWU).symm
  exact LinearEquiv.ofBijective (e.toMonoidHom.toAdditive.toZModLinearMap 2) e.bijective
end Representation.BinaryOffender


open Representation Representation.BinaryOffender
namespace Representation.BinaryOffender
variable {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) H V)

theorem generatingSpan_eq_iSup_prefix (W : ℕ → Subrepresentation ρ) (n : ℕ) :
    generatingSpan ρ W n = ⨆ i : Fin n, W i := by
  induction n with
  | zero => exact le_antisymm bot_le (iSup_le fun i => Fin.elim0 i)
  | succ n ih =>
    rw [generatingSpan, ih]
    apply le_antisymm
    · refine sup_le (iSup_le fun i => ?_) ?_
      · exact le_iSup (fun j : Fin (n+1) => W j) i.castSucc
      · exact le_iSup (fun j : Fin (n+1) => W j) (Fin.last n)
    · apply iSup_le
      intro i
      by_cases hi : i.val < n
      · exact (le_iSup (fun j : Fin n => W j) ⟨i,hi⟩).trans le_sup_left
      · have he : i.val = n := by omega
        rw [he]
        exact le_sup_right

theorem exists_generatingSequence {ι : Type*} [Finite ι] [Nonempty ι]
    (W : ι → Subrepresentation ρ) (hw : ⨆ i, W i = ⊤) :
    ∃ (n : ℕ) (a : ℕ → ι), generatingSpan ρ (fun i => W (a i)) n = ⊤ := by
  classical
  let := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  let a : ℕ → ι := fun i => if hi : i < Fintype.card ι then e.symm ⟨i,hi⟩ else Classical.choice inferInstance
  refine ⟨Fintype.card ι,a,?_⟩
  rw [generatingSpan_eq_iSup_prefix]
  have he : (⨆ i : Fin (Fintype.card ι), W (a i)) = ⨆ i, W i := by
    apply le_antisymm
    · exact iSup_le fun i => le_iSup W (a i)
    · apply iSup_le
      intro i
      apply le_iSup_of_le (e i)
      simp only [a, dif_pos (e i).isLt, Fin.eta, e.symm_apply_apply]
      exact le_rfl
  exact he.trans hw
end Representation.BinaryOffender

open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement
open scoped IsMulCommutative
namespace Representation.BinaryOffender
variable {H : Type*} [Group H] (U : Subgroup H) [U.Normal]
  [IsElementaryAbelian 2 U] (B : Subgroup H)

theorem iSup_internalGenerator_eq_top {ι : Type*} (W : ι → Subgroup H)
    (hBW : ∀ i, B ≤ normalizer (W i : Set H))
    (hWU : ∀ i, W i ≤ U) (hgen : ⨆ i, W i = U) :
    (⨆ i, internalGenerator U B (W i) (hBW i)) = ⊤ := by
  let Z := ⨆ i, internalGenerator U B (W i) (hBW i)
  let L₀ := Subgroup.toAddSubgroup.symm Z.toSubmodule.toAddSubgroup
  let L := L₀.map U.subtype
  have hWL : ∀ i, W i ≤ L := by
    intro i w hw
    refine ⟨⟨w,hWU i hw⟩, ?_, rfl⟩
    exact (le_iSup (fun j => internalGenerator U B (W j) (hBW j)) i) hw
  have hUL : U ≤ L := by rw [← hgen]; exact iSup_le hWL
  apply top_unique
  intro v _
  obtain ⟨w,hw,he⟩ := hUL v.toMul.property
  have he' : w = v.toMul := Subtype.ext he
  change Additive.ofMul w ∈ Z at hw
  rw [he'] at hw
  exact hw
end Representation.BinaryOffender
