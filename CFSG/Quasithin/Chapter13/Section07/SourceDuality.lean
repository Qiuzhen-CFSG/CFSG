module

public import CFSG.Quasithin.Chapter13.Section07.PairFixedCore
public import Theory.Representation.BinaryConjugationSection.CentralDuality

/-!
# The literal source duality and its fixed core

The original seed span is elementary, its commutators with QH lie in the
central source line, and its relative centralizer in QH is exactly HC.
The central binary pairing therefore constructs both original radical
sections with contragredient H-actions. It retains the literal UH/U0
quotient map and the vanishing-commutator pairing.

The actual13.7.12 consumer combines this pairing with the proved original
fixed denominator of index four. This discharges the duality of13.7.4(2);
it does not assert the separate faithfulness conclusion of13.7.4(1).
Source: Aschbacher--Smith13.7.4(2),13.7.12(1), printed pp.936,942, viaF.9.7.
-/

public section

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup
variable {G:Type*} [Group G] [Finite G]
  {T:Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d
/-- The actual two radical sections and their contragredient H-actions. -/
theorem source_central_duality
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃)) :
    let U:=Section08.Source.UH H V₃
    let Q:=H.pCoreIn 2
    let U₀:=U⊓centralizer (Q:Set G)
    let C:=Section08.Source.HC H V₃
    ∃hE:IsElementaryAbelian 2 U, letI:=hE;
      ∃ (ρ:Representation (ZMod 2) H (Additive (U⧸U₀.subgroupOf U)))
        (sU:Representation.BinaryConjugationSection H U U₀ ρ)
        (sQ:Representation.BinaryConjugationSection H Q C ρ.dual),
        (∀(q:Q)(u:U),(sQ.coordinates q).toAdd (sU.coordinates u).toAdd=0 ↔ ⁅(q:G),(u:G)⁆=1) ∧
        (∀u:U,(sU.coordinates u).toAdd=Additive.ofMul (QuotientGroup.mk' (U₀.subgroupOf U) u)) := by
  dsimp only
  let U:=Section08.Source.UH H V₃
  let Q:=H.pCoreIn 2
  let C:=Section08.Source.HC H V₃
  let :IsElementaryAbelian 2 V:=NaturalAction.elementary d
  let :IsElementaryAbelian 2 V₃:=IsElementaryAbelian.of_le d.seed_le
  let :IsMulCommutative (conjugateSpanBy V₃ H):=hU
  have hE:IsElementaryAbelian 2 U:=conjugateSpanBy_elementary_of_commutative V₃ H
  let :=hE
  have hCQ:C≤Q := by
    apply le_trans _ h.kernel_UH_eq_QH.le
    intro z hz
    exact (h.mem_kernel_iff h.UH_le_H).mpr ⟨hz.1,fun u hu=>by
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hz.2 u hu)]
      exact V₁.one_mem⟩
  have hCeq:Q⊓centralizer (U:Set G)=C := by
    apply le_antisymm (inf_le_inf_right _ (pCoreIn_le 2 H))
    exact le_inf hCQ inf_le_right
  have hZQ:V₁≤Q:=h.point_lt.le.trans ((le_conjugateSpanBy V₃ H).trans h.UH_le_QH)
  have hZ:V₁≤centralizer (H:Set G):=le_centralizer_iff.mp h.H_centralizes
  have hh:=Representation.BinaryConjugationSection.exists_central_duality
    H Q U V₁ (pCoreIn_le 2 H) h.UH_le_H
    (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH (D:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (le_normalizer_conjugateSpanBy V₃ H) hZQ hZ
    (by rw [commutator_comm];exact h.commutator_UH_QH_le_point) d.line_card
  rw [hCeq] at hh
  obtain ⟨ρ,sU,sQ,hpair,hcoord⟩:=hh
  exact ⟨hE,ρ,sU,sQ,hpair,hcoord⟩


/-- The actual fixed core of index four is pointwise fixed in the source dual representation. -/
theorem source_duality_fixed_core
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V))
    (hHG:H≤G₁) (hne:⁅V₃,G₁.pCoreIn 2⁆≠⊥)
    (g:(L⊔(T:Subgroup G):Subgroup G))
    (hs:(QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) g)^2=1)
    (hout:¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    let U:=Section08.Source.UH H V₃
    let QH:=H.pCoreIn 2
    let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
    let U₀:=U⊓centralizer (QH:Set G)
    let C:=Section08.Source.HC H V₃
    let A:=conjugate (Section08.Source.VH H V) (g:G)⊓Q
    let R:=(QH⊓Q)⊔C
    ∃hE:IsElementaryAbelian 2 U, letI:=hE;
      ∃ (ρ:Representation (ZMod 2) H (Additive (U⧸U₀.subgroupOf U)))
        (sU:Representation.BinaryConjugationSection H U U₀ ρ)
        (sQ:Representation.BinaryConjugationSection H QH C ρ.dual),
        (∀(q:QH)(u:U),(sQ.coordinates q).toAdd (sU.coordinates u).toAdd=0 ↔ ⁅(q:G),(u:G)⁆=1) ∧
        (∀u:U,(sU.coordinates u).toAdd=Additive.ofMul (QuotientGroup.mk' (U₀.subgroupOf U) u)) ∧
        R.relIndex QH=4 ∧
        ∀a:H,(a:G)∈A→∀w∈sQ.imageSpace R,ρ.dual a w=w := by
  dsimp only
  obtain ⟨hE,ρ,sU,sQ,hpair,hcoord⟩:=source_central_duality d h hU
  exact ⟨hE,ρ,sU,sQ,hpair,hcoord,local_core_fixed_index_four d h hU hV hHG hne,
    fun a ha=>sQ.fixed_on_imageSpace_of_commutator_le _ _
      (pair_fixed_core_commutator d h hU hV g hs hout) a ha⟩

end CFSG.Quasithin.Chapter13.Section07