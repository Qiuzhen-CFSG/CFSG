module
public import CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector.DihedralSplit
public import CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector.DihedralOvergroups
public import Theory.GroupTheory.PGroup.ThompsonNormalizerTower
public import CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector.ThompsonEndgame
public import Mathlib.Order.Preorder.Finite


/-!
# A maximal actual dihedral overgroup for the central-vector argument

The marked initial split makes the family of elementary-by-dihedral
overgroups of R in Λ nonempty. Choose a maximal member M. Its normalizer
fixes the original line because that line is Ω₁(Φ(M)). If the Thompson
subgroup of NΛ(M) is M, the normalizer condition gives NΛ(M)=Λ and proves
centrality. Otherwise we retain the exact maximal member and the
nonstationary Thompson condition for the remaining enlargement argument.

Source: Aschbacher–Smith C.6.4(10), printed pp.168–169. The family used
here omits the extra Levi-normalization condition, which the printed proof
uses for its additional clause (9). This module proves the reduction;
it does not prove that the nonstationary alternative is impossible.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector
variable {G : Type*} [Group G] [Finite G] {K R S Λ : Subgroup G}

/-- An actual elementary-by-dihedral overgroup inside the original Λ. -/
def DihedralOvergroup (R Λ M : Subgroup G) : Prop :=
  R ≤ M ∧ M ≤ Λ ∧ ∃ E : Subgroup G, IsElementaryAbelian 2 E ∧
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty (M ≃* E × DihedralGroup (2 ^ n))

theorem Input.initial_dihedral_overgroup (d : Input K R S Λ) : DihedralOvergroup R Λ R := by
  obtain ⟨E,_,hE,he⟩ := d.exists_initial_dihedral_model
  exact ⟨le_rfl,d.proper.le,E,hE,2,by omega,he⟩

theorem Input.exists_maximal_dihedral_overgroup (d : Input K R S Λ) :
    ∃ M : Subgroup G, Maximal (DihedralOvergroup R Λ) M := by
  exact (Set.toFinite {M | DihedralOvergroup R Λ M}).exists_maximal
    ⟨R,d.initial_dihedral_overgroup⟩

theorem Input.centrality_of_stationary_dihedral_overgroup (d : Input K R S Λ)
    (M : Subgroup G) (hM : DihedralOvergroup R Λ M)
    (hJ : elementaryAbelianMaxJ (Λ ⊓ normalizer (M : Set G)) = M) :
    ⁅(blockU K).map K.subtype,R⁆ ≤ centralizer ((S ⊔ Λ : Subgroup G) : Set G) := by
  obtain ⟨hRM,hMΛ,E,hE,n,hn,⟨e⟩⟩ := hM
  let := hE
  have hline := d.commutator_centralizes_normalizer_of_dihedral_overgroup
    M hRM (d.Λ_two.to_le hMΛ) hn e
  have heq := twoGroup_normalizer_eq_of_thompson_eq Λ M d.Λ_two hJ
  have hΛN : Λ ≤ normalizer (M : Set G) := heq ▸ inf_le_right
  apply le_centralizer_iff.mpr
  exact sup_le (le_centralizer_iff.mp d.commutator_centralizes_S)
    (hΛN.trans (le_centralizer_iff.mp hline))

/-- Failure of centrality leaves the nonstationary Thompson branch at a
maximal actual dihedral model; all model, rank and quotient inputs are discharged. -/
theorem Input.centrality_or_maximal_nonstationary_dihedral (d : Input K R S Λ) :
    (⁅(blockU K).map K.subtype,R⁆ ≤ centralizer ((S ⊔ Λ : Subgroup G) : Set G)) ∨
    ∃ M : Subgroup G, Maximal (DihedralOvergroup R Λ) M ∧ M < Λ ∧
      elementaryAbelianMaxJ (Λ ⊓ normalizer (M : Set G)) ≠ M := by
  classical
  by_cases hc : ⁅(blockU K).map K.subtype,R⁆ ≤ centralizer ((S ⊔ Λ : Subgroup G) : Set G)
  · exact Or.inl hc
  right
  obtain ⟨M,hM⟩ := d.exists_maximal_dihedral_overgroup
  have hproper : M ≠ Λ := by
    intro heq
    apply hc
    obtain ⟨hRM,hMΛ,E,hE,n,hn,⟨e⟩⟩ := hM.1
    let := hE
    have hline := d.commutator_centralizes_normalizer_of_dihedral_overgroup
      M hRM (d.Λ_two.to_le hMΛ) hn e
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp d.commutator_centralizes_S)
      ((heq.ge.trans M.le_normalizer).trans (le_centralizer_iff.mp hline))
  exact ⟨M,hM,lt_of_le_of_ne hM.1.2.1 hproper,
    fun hJ => hc (d.centrality_of_stationary_dihedral_overgroup M hM.1 hJ)⟩
end CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector
