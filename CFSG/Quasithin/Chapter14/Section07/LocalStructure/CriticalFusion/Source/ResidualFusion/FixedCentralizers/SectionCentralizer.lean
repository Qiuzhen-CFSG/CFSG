module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.Basic
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.SectionCentralizer
public import Theory.GroupTheory.PCoreImage
public import Theory.Alternating.Aut

/-!
# The order-three section-centralizer obstruction in 14.7.68

The actual quotient map H → H/O₂(H) → S₅ sends K to A₅. An element
centralizing K/O₂(K) therefore has image in C_{S₅}(A₅) = 1, and lies
in O₂(H). If N_G(K)=H, the same calculation excludes every ambient
order-three element centralizing that section. This is the final contradiction
used after constructing the order-three subgroup in the Sp₄(4) and SL₃(4)
alternatives. Existence of that subgroup is a separate model-embedding step.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
14.7.63 and the end of 14.7.68(2), printed pp.1069 and 1072.
-/

@[expose] public section
noncomputable section
open Subgroup Representation
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

namespace Data
variable (d : Data T L V F W)

include d in
/-- The actual S₅ marking forces C_H(K/O₂(K)) into O₂(H). This is the
upper containment used in the final Sp₄(4)/SL₃(4) contradiction. -/
theorem sectionCentralizer_le_Hcore :
    ChapterA.Section04.twoSectionCentralizer (K F) F.H ≤ F.H.pCoreIn 2 := by
  have hcore : (K F).pCoreIn 2 ≤ F.H.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes (K_le_H F) (H_normalizes_K F)
  intro x hx
  have hcomm : d.qH ⟨x, hx.1⟩ ∈ centralizer (alternatingGroup (Fin 5) : Set ChapterJ.S5) := by
    apply mem_centralizer_iff.mpr
    intro a ha
    rw [← d.K_image] at ha
    obtain ⟨k, hk, rfl⟩ := ha
    apply (commutatorElement_eq_one_iff_mul_comm.mp ?_).symm
    rw [← map_commutatorElement]
    apply MonoidHom.mem_ker.mp
    rw [d.qH_ker]
    exact hcore (hx.2.2 k hk)
  rw [GroupTheory.AutAlternating.centralizer_alternatingGroup_eq_bot 5 (by decide)] at hcomm
  have hker : (⟨x, hx.1⟩ : F.H) ∈ d.qH.ker := hcomm
  rw [d.qH_ker] at hker
  exact hker

include d in
/-- No order-three element can centralize K/O₂(K) once N_G(K)=H.
The section centralizer includes normalization of K in its definition. -/
theorem no_orderThree_sectionCentralizer (hNK : normalizer (K F : Set G) = F.H)
    (y : G) (hy : orderOf y = 3)
    (hc : y ∈ ChapterA.Section04.twoSectionCentralizer (K F) ⊤) : False := by
  have hyH : y ∈ F.H := hNK ▸ hc.2.1
  have hycore : y ∈ F.H.pCoreIn 2 := d.sectionCentralizer_le_Hcore ⟨hyH, hc.2⟩
  have hcop := (isPGroup_pCoreIn 2 F.H).orderOf_coprime (by decide : Nat.Coprime 2 3)
    ⟨y, hycore⟩
  rw [Subgroup.orderOf_mk, hy] at hcop
  norm_num at hcop
end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
