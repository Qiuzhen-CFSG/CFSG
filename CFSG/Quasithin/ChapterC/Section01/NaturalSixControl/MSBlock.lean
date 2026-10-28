module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.Setup
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.MSInputs
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# The whole-core terminal for the actual natural S6 MS pair

The literal MS pair is formed with the full Baumann subgroup of the actual
point-parabolic two-core. The outstanding symplectic branch of MS93 must
reconstruct the commutator core: it is elementary, central in the two-core,
and has a nonzero irreducible quotient by its fixed subgroup. The terminal
below derives the remaining block clauses from the actual component and
quotient map, then identifies its natural A6 block type and whole-core action.

`CoreReconstruction` records that outstanding structural output. This module
does not assert that the MS hypotheses produce it.

Source: Aschbacher--Smith C.1.32, printed pp.135--136; Meierfrankenfeld--
Stellmacher, Pushing up weak BN-pairs of rank two, Main Theorem case (2),
Sections 3 and 5.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.NaturalSixControl
open Subgroup Theory.GroupTheory
universe u
variable {K : Type u} [Group K]

/-- The whole-core output required from the symplectic MS93 source proof.
The core is the actual intrinsic `[O₂(L), L]`, not a selected constituent. -/
structure CoreReconstruction (L : Type*) [Group L] : Prop where
  elementary : IsElementaryAbelian 2 (blockU L)
  central : blockU L ≤ centralizer (pCore 2 L : Set L)
  irreducible : BlockModuleIrreducible L

variable {L V : Subgroup K} [L.Normal] [V.Normal] {T : Sylow 2 K}

/-- Exactly the MS2(a) and MS3 hypotheses on the full point Baumann subgroup
inside the original component--Baumann product. -/
structure IntrinsicMSPair (d : SourceData L V T) : Prop where
  radical : MSOddIndexRadical (d.B.subgroupOf (L ⊔ d.B))
  characteristic : MSCharacteristicCondition (d.B.subgroupOf (L ⊔ d.B))

/-- The original terminal statement, before discharge of the whole-core
reconstruction. This is a proposition, not a classification hypothesis. -/
def MSBlockStatement [Finite K] (d : SourceData L V T) : Prop :=
  MSOddIndexRadical (d.B.subgroupOf (L ⊔ d.B)) →
  MSCharacteristicCondition (d.B.subgroupOf (L ⊔ d.B)) → IsBlock L

namespace SourceData
variable (d : SourceData L V T)
include d

/-- The native A6 quotient on the actual component, with the intrinsic
two-core identified using subnormality. -/
noncomputable def componentQuotientEquiv [Finite K] :
    (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6) := by
  let a : L →* alternatingGroup (Fin 6) :=
    (d.q.comp L.subtype).codRestrict _
      (fun l => d.image_component ▸ mem_map_of_mem d.q l.property)
  have ha : Function.Surjective a := by
    intro x
    obtain ⟨l, hl, he⟩ := d.image_component.ge x.property
    exact ⟨⟨l, hl⟩, Subtype.ext he⟩
  have hcore : a.ker = pCore 2 L := by
    rw [pCore_subnormal_eq_comap 2 d.component.subnormal, ← d.ker_eq]
    ext l
    change a l = 1 ↔ d.q (l : K) = 1
    exact Subtype.ext_iff
  exact (QuotientGroup.quotientMulEquivOfEq hcore.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective a ha)

omit d in
private theorem a6_quasisimple : IsQuasisimple (alternatingGroup (Fin 6)) where
  toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  simple := by
    let : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    exact ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans
      QuotientGroup.quotientBot).isSimpleGroup

/-- The actual component has the quasisimple quotient required in the
short-group definition. -/
theorem component_quotient_quasisimple [Finite K] :
    IsQuasisimple (L ⧸ pCore 2 L) := by
  let : IsQuasisimple (alternatingGroup (Fin 6)) := a6_quasisimple
  exact IsQuasisimple.of_mulEquiv d.componentQuotientEquiv.symm

omit d in
private theorem perfect_twoPerfect {E : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] : IsPPerfect 2 E := by
  intro N hn hq
  let : N.Normal := hn
  by_contra hne
  let : Nontrivial (E ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (E ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (E ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (E ⧸ N) inferInstance

/-- Whole-core reconstruction discharges the three remaining short-group
clauses; finiteness, two-perfection, fitting, quotient and subnormality come
from the original source data. -/
theorem block_of_coreReconstruction [Finite K] (c : CoreReconstruction L) :
    IsBlock L := by
  let : Group.IsPerfect L := d.component.perfect
  exact {
    finite := inferInstance
    short := {
      finite := inferInstance
      twoPerfect := perfect_twoPerfect
      fitting := d.component_fitting
      elementary := c.elementary
      central := c.central
      quotient := Or.inl d.component_quotient_quasisimple
      irreducible := c.irreducible }
    subnormal := d.component.subnormal }

/-- The given native natural module is moved by the actual A6 component. -/
theorem natural_commutator_ne_bot [Finite K] : ⁅V, L⁆ ≠ ⊥ := by
  intro hbot
  let π := BinaryPermutation.naturalRepresentation (Fin 6)
  have hz := Representation.BinaryOffender.fixedSpace_eq_bot_of_faithful_irreducible_on
    π (alternatingGroup (Fin 6))
    (BinaryPermutation.naturalRepresentation_injective _ (by decide))
    (BinaryPermutation.alternatingNatural_isIrreducible (by decide))
  have hv : (d.eV d.v).toAdd ∈ Representation.BinaryOffender.fixedSpace
      π (alternatingGroup (Fin 6)) := by
    intro a
    obtain ⟨l, hl, he⟩ := d.image_component.ge a.property
    have hc : MulAut.conjNormal l d.v = d.v := by
      apply Subtype.ext
      change l * (d.v : K) * l⁻¹ = d.v
      rw [commutator_eq_bot_iff_le_centralizer.mp hbot d.v.property l hl,
        mul_inv_cancel_right]
    have hh := d.action l d.v
    rw [hc, he] at hh
    exact hh.symm
  rw [hz] at hv
  apply d.v_ne
  apply d.eV.injective
  apply Multiplicative.toAdd.injective
  rw [map_one]
  change (d.eV d.v).toAdd = 0
  exact hv

/-- Literal A6 typing after reconstruction, on the same natural coordinates
and conjugation action supplied by the source. -/
theorem alternatingBlock_of_coreReconstruction [Finite K]
    (c : CoreReconstruction L) : IsAlternatingBlock L 6 := by
  let : IsElementaryAbelian 2 V := d.elementary
  exact RankOne.SymmetricSix.isAlternatingBlock_of_natural_six L V
    (d.block_of_coreReconstruction c) d.q d.image_component d.eV d.action
    d.natural_commutator_ne_bot

/-- The source's actual commutator core has the whole natural A6 action;
this is a consequence of the reconstructed block, not an input equality
between a constituent and the whole core. -/
theorem natural_core_coordinates_of_coreReconstruction [Finite K]
    (c : CoreReconstruction L) :
    ∃ E : blockU L ≃* Multiplicative (BinaryPermutation.natural (Fin 6)),
      ∀ (l : L) (u : blockU L), (E (blockConjugate L l u)).toAdd =
        BinaryPermutation.naturalRepresentation (Fin 6) (d.q l) (E u).toAdd := by
  let : IsElementaryAbelian 2 V := d.elementary
  exact RankOne.SymmetricSix.blockU_natural_six_coordinates L V
    (d.block_of_coreReconstruction c) d.q d.image_component d.eV d.action
    d.natural_commutator_ne_bot

/-- The literal MS2/MS3 terminal consumer. Its independent reconstruction
input must be produced by the symplectic MS93 source argument. -/
theorem ms_block_of_coreReconstruction [Finite K]
    (_hR : MSOddIndexRadical (d.B.subgroupOf (L ⊔ d.B)))
    (_hC : MSCharacteristicCondition (d.B.subgroupOf (L ⊔ d.B)))
    (c : CoreReconstruction L) : IsBlock L ∧ IsAlternatingBlock L 6 :=
  ⟨d.block_of_coreReconstruction c, d.alternatingBlock_of_coreReconstruction c⟩

/-- A packaged intrinsic pair feeds exactly the same original terminal. -/
theorem intrinsic_ms_block_of_coreReconstruction [Finite K]
    (p : IntrinsicMSPair d) (c : CoreReconstruction L) :
    IsBlock L ∧ IsAlternatingBlock L 6 :=
  d.ms_block_of_coreReconstruction p.radical p.characteristic c

end SourceData
end CFSG.Quasithin.ChapterC.NaturalSixControl
