module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.LargeSections
public import Theory.Representation.Suzuki.TwoDimensionalCentralizer

/-!
# Excluding the doubled SL₃ case in a Suzuki centralizer

A fixed-free Suzuki subgroup stabilizes the moved space of every commuting
actor. Transport its action through the literal doubled-natural marking.
The two-dimensional multiplicity calculation makes Suzuki fix that entire
nonzero space, contradicting its zero fixed space.

Source: Aschbacher–Smith B.5.9(3), B.5.10(2), and 10.1.1. This is applied
to the actual offender subgroup in Chapter10.Recognition.Quiet.SuzukiTwoFactors.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceInduction
open QuasisimpleSource BenderSuzuki.MatrixGroups
variable {Q D V : Type*} [Group Q] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V]

theorem not_doubleThree_of_commuting_suzuki
    (ρ : Representation (ZMod 2) Q V) (S : Subgroup Q)
    {m : ℕ} (hm : 0<m) (eS : S ≃* SuzukiMatrixGroup m)
    (hfix : fixedSpace ρ S = ⊥)
    (f : D →* Q) (hc : f.range ≤ centralizer (S : Set Q))
    (K : Subgroup D) (c : ProjectiveLine.QuasisimpleSourceConclusion (ρ.comp f) K)
    (F : BinaryField)
    (e : ActionEquiv (c.sectionData.space.toRepresentation.comp K.subtype)
      (repeated (linearNatural F 3) 2)) : False := by
  let W := c.sectionData.space.toSubmodule
  have hs : S ≤ subspaceStabilizer ρ W := by
    change S ≤ subspaceStabilizer ρ c.sectionData.space.toSubmodule
    rw [c.sectionData.space_eq]
    change S ≤ subspaceStabilizer ρ (subspaceCommutator (ρ.comp f) ⊤ K)
    rw [subspaceCommutator_comp_map]
    exact subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
      ((le_centralizer_iff.mp ((map_le_range f K).trans hc)).trans
        (Subgroup.centralizer_le_normalizer _))
  let τ : Representation (ZMod 2) (SuzukiMatrixGroup m) W :=
    ((stabilizerRepresentation ρ W).comp (inclusion hs)).comp eS.symm.toMonoidHom
  let α := (c.sectionData.space.toRepresentation.comp K.subtype).comp e.groupEquiv.symm.toMonoidHom
  have hcomm (a : SuzukiMatrixGroup m) (b : Matrix.SpecialLinearGroup (Fin 3) F.Carrier)
      (v : W) : τ a (α b v) = α b (τ a v) := by
    apply Subtype.ext
    change ρ (eS.symm a) (ρ (f (e.groupEquiv.symm b)) v) =
      ρ (f (e.groupEquiv.symm b)) (ρ (eS.symm a) v)
    rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul]
    exact LinearMap.congr_fun (congrArg ρ
      (hc (MonoidHom.mem_range.mpr ⟨(e.groupEquiv.symm b : D),rfl⟩)
        (eS.symm a) (eS.symm a).property)) v
  have he (b : Matrix.SpecialLinearGroup (Fin 3) F.Carrier) (v : W) :
      e.linearEquiv (α b v) = SL3DoubledNaturalOffenders.representation F.Carrier b (e.linearEquiv v) := by
    have hh := e.intertwines (e.groupEquiv.symm b) v
    rw [e.groupEquiv.apply_symm_apply] at hh
    exact hh
  have ht := Suzuki.doubled_natural_commuting_trivial_of_coordinates hm τ α hcomm e.linearEquiv he
  have hzero (v : W) : v = 0 := by
    apply Subtype.ext
    apply (show (v:V) ∈ (⊥ : Submodule (ZMod 2) V) from ?_)
    rw [←hfix]
    intro s
    have hh := congrArg Subtype.val (ht (eS s) v)
    change ρ (eS.symm (eS s)) v = v at hh
    rw [eS.symm_apply_apply] at hh
    exact hh
  let : Nontrivial W := e.linearEquiv.toEquiv.nontrivial
  obtain ⟨v,hv⟩ := exists_ne (0:W)
  exact hv (hzero v)

end CFSG.Quasithin.ChapterB.SourceInduction
