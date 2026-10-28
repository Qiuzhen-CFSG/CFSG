module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceOrthogonal
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction.Pairs
public import Theory.GroupTheory.BaerSuzukiSubgroup

/-!
# The original symmetric-three pair in the normal branch

Baer–Suzuki in the literal H/O₂(H) quotient chooses a non-two conjugate
pair of the original V image. Lift its actor back to H and apply the whole
quaternion-closure square action. All earlier block and quaternion inputs
are constructed internally; no additional plane-control hypothesis remains.

Source: Aschbacher–Smith13.5.15, printed p.920.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceNonTwoPair
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks
open SourceOrthogonal
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
  (hseed : D.Vplus=⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)
include d h e hseed hn hU

theorem exists_original_symmetricThree_pair : ∃g∈D.H,
    ¬IsPGroup 2 (Section08.Source.starImage D.H
      (D.V⊔ChapterG.Section02.Setup.conjugate D.V g)) ∧
    Nonempty ((Section08.Source.starImage D.H
      (D.V⊔ChapterG.Section02.Setup.conjugate D.V g))≃*Equiv.Perm (Fin 3)) := by
  have hc := LocalGeometry.star_V_card_two h (seed_index d) hU
  have hp : IsPGroup 2 (Section08.Source.starImage D.H D.V) :=
    IsPGroup.of_card (n:=1) (by simpa only [pow_one] using hc)
  obtain ⟨x,hx⟩ := (le_pCore_or_exists_conjugate_sup_not_isPGroup _ hp).resolve_left (by
    intro hle
    rw [pCore_quotient_pCore_eq_bot] at hle
    have hz := le_bot_iff.mp hle
    rw [hz,card_bot] at hc
    contradiction)
  obtain ⟨g,hg,_,he⟩ :=
    ComponentReduction.Fitting.SourceAction.lift_pair D.H D.V h.V_le_H x
  have hnpair : ¬IsPGroup 2 (Section08.Source.starImage D.H
      (D.V⊔ChapterG.Section02.Setup.conjugate D.V g)) := he ▸ hx
  refine ⟨g,hg,hnpair,?_⟩
  exact original_star_pair_symmetricThree d h e hseed hn hU g⁻¹ (D.H.inv_mem hg) hnpair

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceNonTwoPair
end
