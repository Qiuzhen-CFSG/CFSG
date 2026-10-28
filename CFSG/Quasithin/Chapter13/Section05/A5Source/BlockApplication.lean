module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.BlockMarking
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.Blocks
public import Theory.GroupTheory.PResidual.SylowSupplement
public import CFSG.Quasithin.ChapterG.Section01.SL2FourRecognition.Source

/-!
# The original marked substitution in13.5.14

The tilde commutator identity lifts across the original point line and
places U_H in O₂(L₁). G.2.4's proved generation then identifies the
actual join ⟨U_H,U_Hᵍ⟩ with L, and its prescribed two-residual L⁻ is L.
Consequently the literal MarkedBlockInput used in13.5.15 is constructed,
with every module, span and residual premise discharged.

The final application obtains the A₅ block and original quaternion
closure when L₁ is normal in H. The proved original G.1.3 supplies
recognition; only full A.3.12 remains an earlier-source input.
Source: Aschbacher–Smith13.5.14–15(3–5), printed pp.919–920.
-/
@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
open ChapterG.Section02.AlternatingFive
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
include d hA312 hH

/-- Original13.5.14(1), without assuming L₁ normal in H. -/
theorem closure_reduction_of_tilde
    (htilde : let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
      D.tilde D.UH = ⁅D.tilde D.UH,D.tilde D.L₁⁆) :
    Source.UH H V₃ = ⁅Source.UH H V₃,residualCentralizer L V₁⁆ ∧
      Source.UH H V₃ ≤ (residualCentralizer L V₁).pCoreIn 2 ∧ Source.UH H V₃ ≤ L := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  have hp : D.g2.V₁ ≤ ⁅D.g2.V,D.g2.L₁⁆ := by
    rw [hf.g2_L₁]
    exact hf.point_lt.le.trans (NormalBranch.seed_commutator hf d.third_eq_commutator).ge
  have ht : ⁅D.g2.tilde D.g2.U,D.g2.tilde D.g2.L₁⁆ = D.g2.tilde D.g2.U := by
    rw [hf.g2_L₁]
    exact htilde.symm
  have he := U_eq_commutator_of_tilde hf.g2_hypothesis hp ht
  have hc := U_le_local_core_of_tilde hf.g2_hypothesis hp ht
  rw [hf.g2_L₁] at he hc
  exact ⟨he,hc,hc.trans ((pCoreIn_le 2 D.L₁).trans ((map_subtype_le _).trans inf_le_left))⟩

variable (hU : ¬ IsMulCommutative (Source.UH H V₃))
  {g : G} (hg : g ∈ L) (hg₁ : g ∉ normalizer (V₁ : Set G))
  (htilde : let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
    D.tilde D.UH = ⁅D.tilde D.UH,D.tilde D.L₁⁆)
include hU hg hg₁ htilde

/-- The prescribed pair of closures generates the original L. -/
theorem block_group_eq :
    NormalBranch.K (⟨T,L,V,V₃,V₁,H⟩ : ChapterF.Section09.Setup G) g = L := by
  have b := blockMarking d hA312 hH hU hg hg₁
  have he := b.I_eq_LU
  have hu : Source.UH H V₃ ≤ L := (closure_reduction_of_tilde d hA312 hH htilde).2.2
  exact he.trans (sup_eq_left.mpr hu)

/-- The exact residual in the source substitution is L itself. -/
theorem block_residual_eq :
    NormalBranch.blockResidual (⟨T,L,V,V₃,V₁,H⟩ : ChapterF.Section09.Setup G) g = L := by
  unfold NormalBranch.blockResidual
  rw [block_group_eq d hA312 hH hU hg hg₁ htilde,sup_comm]
  exact embedded_pResidual_join_pGroup L ((L ⊔ (T : Subgroup G)).pCoreIn 2)
    d.twoPerfect (isPGroup_pCoreIn 2 _) (d.core_le_sylow.trans d.normalizes_L)

/-- The actual13.5.14 marked input, with no assumed block or core conclusion. -/
noncomputable def markedBlockInput :
    NormalBranch.MarkedBlockInput (⟨T,L,V,V₃,V₁,H⟩ : ChapterF.Section09.Setup G) 5 g := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have he : NormalBranch.blockResidual D g = L := block_residual_eq d hA312 hH hU hg hg₁ htilde
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  refine {
    marked := ?_
    span := ?_
    residual := ?_
    inside := he.le
    five_eq := fun _ => he.symm }
  · rw [he]
    exact blockMarking d hA312 hH hU hg hg₁
  · rw [he]
    exact d.line_span_eq
  · rw [he]
    exact hf.g2_L₁.symm

omit htilde in
/-- Literal13.5.15(3–5): the original L is an A₅ block and its original
H-closure is the quaternion central product of order32. -/
theorem normal_block_consequences
    (hn : ((residualCentralizer L V₁).subgroupOf H).Normal) :
    ChapterC.IsAlternatingBlock L 5 ∧ L.pCoreIn 2 = V ∧
      (residualCentralizer L V₁).pCoreIn 2 = Source.UH H V₃ ∧
      residualCentralizer L V₁ ⊓ Source.QH H = Source.UH H V₃ ∧
      Nat.card (Source.UH H V₃) = 32 ∧
      Nonempty (Source.UH H V₃ ≃* QuaternionCentralProduct.Model) := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  obtain ⟨_,_,_,_,hV,hcore,hint,hcard,hiso,hfive,_⟩ :=
    NormalBranch.block_consequences hf d.third_eq_commutator hn
      (fun ht => ⟨markedBlockInput d hA312 hH hU hg hg₁ ht⟩)
      ChapterG.Section01.SL2FourRecognition.recognitionInput
  obtain ⟨he,hblock⟩ := hfive rfl
  have hv : L.pCoreIn 2 = V := by
    change D.L.pCoreIn 2 = D.V
    rw [he]
    exact hV
  exact ⟨hblock,hv,hcore,hint,hcard,hiso⟩

end CFSG.Quasithin.Chapter13.Section05.A5Source
