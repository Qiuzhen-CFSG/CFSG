module
public import CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector.DerivedLine
public import Theory.GroupTheory.PGroup.ElementaryDihedralOmega
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# The original marked line in a dihedral overgroup

In any elementary-by-dihedral two-overgroup M of the source R, its derived
line has order two and lies in Ω₁(Φ(M)). The dihedral calculation shows that
this latter characteristic subgroup also has order two, so they coincide.
Thus the whole normalizer of M fixes the original marked vector.

Source: Aschbacher–Smith C.6.4(10), printed pp.168–169. Constructing an
overgroup whose normalizer contains Λ remains a separate local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector
variable {G : Type*} [Group G] [Finite G] {K R S Λ : Subgroup G}

/-- Any elementary-by-dihedral overgroup retains the original marked line as
its intrinsic Frattini omega. This is the invariant used at every maximal step. -/
theorem Input.commutator_eq_omegaFrattini_of_dihedral_overgroup (d : Input K R S Λ)
    (M : Subgroup G) (hRM : R ≤ M) (hM : IsPGroup 2 M)
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    {n : ℕ} (hn : 2 ≤ n) (e : M ≃* E × DihedralGroup (2 ^ n)) :
    ⁅(blockU K).map K.subtype,R⁆ = M.omegaFrattini := by
  have hcard : Nat.card M.omegaFrattini = 2 := by
    rw [← omegaFrattini_map_subtype,card_map_of_injective M.subtype_injective]
    exact omegaFrattini_card_of_elementary_dihedral hn e
  apply eq_of_le_of_card_ge ?_ (by rw [hcard,d.commutator_card])
  let : Fact (IsPGroup 2 M) := ⟨hM⟩
  have hder : ⁅R,R⁆ ≤ (frattini M).map M.subtype := by
    apply (commutator_mono hRM hRM).trans
    rw [← map_subtype_commutator]
    exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))
  intro z hz
  apply (omegaOneAmbient_le_iff _ _).mp le_rfl z
  · apply hder
    rwa [d.derived_eq_module_commutator]
  · let : IsElementaryAbelian 2 ((blockU K).map K.subtype) := d.block.2.1.elementary.map K.subtype
    have hZU : ⁅(blockU K).map K.subtype,R⁆ ≤ (blockU K).map K.subtype :=
      le_normalizer_iff_commutator_le_left.mp
        ((d.R_le_S.trans le_sup_right).trans d.normalizes_module)
    exact elemPow_eq_one_of_isElementaryAbelian z (hZU hz)

/-- Every normalizer of an elementary-by-dihedral overgroup fixes the original
marked line. This is the centrality step in the maximal-overgroup argument. -/
theorem Input.commutator_centralizes_normalizer_of_dihedral_overgroup (d : Input K R S Λ)
    (M : Subgroup G) (hRM : R ≤ M) (hM : IsPGroup 2 M)
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    {n : ℕ} (hn : 2 ≤ n) (e : M ≃* E × DihedralGroup (2 ^ n)) :
    ⁅(blockU K).map K.subtype,R⁆ ≤ centralizer (normalizer (M : Set G) : Set G) := by
  have hline := d.commutator_eq_omegaFrattini_of_dihedral_overgroup M hRM hM hn e
  have hN := normalizer_le_normalizer_omegaFrattini M hM
  rw [← hline] at hN
  exact le_centralizer_iff.mpr (hN.trans (normalizer_le_centralizer_of_card_two _ d.commutator_card))

end CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector
