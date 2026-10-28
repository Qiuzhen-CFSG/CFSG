module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionPlaneCommutator

/-!
# Conjugating the two graph-root products

A plane-radical parameter with nonzero Frobenius trace conjugates the marked
graph involution f to ft. Since the same parameter centralizes the original
root z, it also conjugates fz to ftz. Thus the root-fusion conclusion for ftz
required in F.5.3 follows from the earlier exceptional fusion z ∼ fz.

The conjugator is retained in the literal source Q₂. Source:
Aschbacher–Smith, *The Classification of Quasithin Groups*, F.4.37 and
F.5.3, printed pp.293 and 300.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory Matrix
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourPlaneLocal UnitaryFourPlaneRadical UnitaryFourShortRoot
local notation "hn" => Nat.le_refl 1
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
variable {G G0 : Type*} [Group G] [Group G0]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G)
open scoped commutatorElement IsMulCommutative

theorem source_graph_short_conjugator (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z) :
    ∃ q ∈ Q c i true,
      q * Source.graphElement c i * q⁻¹ = Source.graphElement c i * sourceMarkedShort c i ∧
      Commute q (rootElement c i z) := by
  obtain ⟨X,hX⟩ := exists_graphParameter_trace_short
  let q := sourcePlaneParameter c i (Multiplicative.ofAdd X)
  have hqQ : q ∈ Q c i true := sourcePlaneParameter_range c i ▸ ⟨_,rfl⟩
  have hc : ⁅q,Source.graphElement c i⁆ = sourceMarkedShort c i := by
    rw [sourcePlaneParameter_commutator,hX]
    rfl
  have hqf : q * Source.graphElement c i * q⁻¹ =
      Source.graphElement c i * sourceMarkedShort c i := by
    have he := congrArg (fun a : G => a * Source.graphElement c i) hc
    rw [commutatorElement_def] at he
    simpa only [mul_assoc,inv_mul_cancel,mul_one,
      (source_short_commutes_graph c i).eq] using he
  refine ⟨q,hqQ,hqf,?_⟩
  let : IsElementaryAbelian 2 (Q c i true) := source_Q_plane_elementary c i
  exact congrArg Subtype.val (mul_comm (⟨q,hqQ⟩ : Q c i true)
    ⟨rootElement c i z,source_root_mem_Q_plane c i z h⟩)

theorem source_graph_root_fuses_graph_short_root (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z) :
    IsConj (Source.graphElement c i * rootElement c i z)
      (Source.graphElement c i * sourceMarkedShort c i * rootElement c i z) := by
  obtain ⟨q,_,hqf,hqz⟩ := source_graph_short_conjugator c i z h
  refine isConj_iff.mpr ⟨q,?_⟩
  calc
    q * (Source.graphElement c i * rootElement c i z) * q⁻¹ =
        (q * Source.graphElement c i * q⁻¹) * (q * rootElement c i z * q⁻¹) := by group
    _ = _ := by rw [hqf,mul_inv_eq_iff_eq_mul.mpr hqz.eq]

theorem source_root_fuses_graph_short_root_of_graph_root (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z)
    (hzf : IsConj (rootElement c i z) (Source.graphElement c i * rootElement c i z)) :
    IsConj (rootElement c i z)
      (Source.graphElement c i * sourceMarkedShort c i * rootElement c i z) :=
  hzf.trans (source_graph_root_fuses_graph_short_root c i z h)

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
