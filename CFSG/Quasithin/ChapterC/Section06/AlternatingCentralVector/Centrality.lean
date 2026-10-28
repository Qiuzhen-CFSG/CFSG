module
public import CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector.FixedInvolution
public import Theory.GroupTheory.PGroup.ElementaryDihedralEnlargement

/-!
# The central vector of the ordinary A₇ block

For a proper elementary-by-dihedral overgroup M of R, the nonstationary
Thompson branch supplies an external involution fixing Z(M). The source
normalizer obstruction controls every maximum elementary subgroup of M,
so adjoining that involution gives a larger actual dihedral model.
This contradicts maximality. The stationary branch therefore applies,
and the original marked line [U,R] centralizes SΛ.

This proves the specialized conclusion of Aschbacher–Smith C.6.4(10),
printed pp.167–169, from the unchanged marked Input. The Levi condition
is needed by the source's additional clause (9); the central-vector
conclusion follows from the larger family used here without it.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector
variable {G : Type*} [Group G] [Finite G] {K R S Λ : Subgroup G}

/-- The nonstationary branch strictly enlarges the actual dihedral model. -/
theorem Input.exists_larger_dihedral_overgroup (d : Input K R S Λ)
    (M : Subgroup G) (hM : DihedralOvergroup R Λ M) (hproper : M < Λ)
    (hJ : elementaryAbelianMaxJ (Λ ⊓ normalizer (M : Set G)) ≠ M) :
    ∃ M' : Subgroup G, M < M' ∧ DihedralOvergroup R Λ M' := by
  obtain ⟨y,hy,hyM,hy2,hyZ⟩ := d.exists_dihedral_enlarging_involution M hM hproper hJ
  have hcontrol := d.dihedral_maximum_normalizer_le M hM hproper
  obtain ⟨hRM,hMΛ,E,hE,n,hn,⟨e⟩⟩ := hM
  let := hE
  obtain ⟨F,hF,he⟩ := ElementaryDihedral.enlarge_of_normalizer_control
    M Λ hMΛ hcontrol hn e y hy.1 hy.2 hyM hy2 hyZ
  refine ⟨M ⊔ zpowers y,lt_of_le_not_ge le_sup_left ?_,hRM.trans le_sup_left,
    sup_le hMΛ (zpowers_le.mpr hy.1),F,hF,n+1,by omega,he⟩
  intro h
  exact hyM (h (mem_sup_right (mem_zpowers y)))

/-- The specialized source C.6.4(10), with the original ambient module,
relative normalizers, quotient marking, and two-group hypotheses. -/
theorem Input.commutator_centralizes (d : Input K R S Λ) :
    ⁅(blockU K).map K.subtype,R⁆ ≤ centralizer ((S ⊔ Λ : Subgroup G) : Set G) := by
  obtain hc | ⟨M,hM,hproper,hJ⟩ := d.centrality_or_maximal_nonstationary_dihedral
  · exact hc
  · obtain ⟨M',hlt,hM'⟩ := d.exists_larger_dihedral_overgroup M hM.1 hproper hJ
    exact (hlt.not_ge (hM.2 hM' hlt.le)).elim

end CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector
