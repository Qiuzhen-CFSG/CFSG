module
public import Stellmacher.ElementaryAbelianMaxOrder
public import Stellmacher.OmegaOneCenterMap
public import Theory.ElementaryAbelian.Join

/-!
# Elementary centralizers of the elementary Thompson subgroup

Every elementary abelian two-subgroup E of S centralizing J(S) lies in
Ω₁(Z(J(S))). Choose a maximum-order elementary subgroup A of S.
Since E commutes with A, their join is elementary; maximal order gives
E ≤ A ≤ J(S). Centrality and exponent two then give the conclusion.

This is the maximal-elementary subgroup reduction in Stellmacher (2.2)
and the first case of (2.3), journal pp.20–21, in
`refs/latex/stellmacher-n-group.tex`. The result does not require S to be
Sylow or E to be normal.
-/

namespace Stellmacher

public theorem elementary_centralizer_maxJ_le_omegaCenter
    {G : Type*} [Group G] [Finite G]
    (S E : Subgroup G) [IsElementaryAbelian 2 E]
    (hES : E ≤ S)
    (hEC : E ≤ Subgroup.centralizer (elementaryAbelianMaxJ S : Set G)) :
    E ≤ omegaOneCenterAmbient (elementaryAbelianMaxJ S) := by
  obtain ⟨A,hA⟩ := elementaryAbelianMaxSubgroups_nonempty S
  let _ : IsElementaryAbelian 2 A := hA.2.1
  have hAJ : A ≤ elementaryAbelianMaxJ S := le_sSup hA
  have hEA : E ≤ Subgroup.centralizer (A : Set G) :=
    hEC.trans (Subgroup.centralizer_le hAJ)
  have hsup : IsElementaryAbelian 2 ↥(A ⊔ E) :=
    IsElementaryAbelian.sup_of_le_centralizer hEA
  have hEq : A = A ⊔ E := Subgroup.eq_of_le_of_card_ge le_sup_left
    (hA.2.2 (A ⊔ E) (sup_le hA.1 hES) hsup)
  have hEJ : E ≤ elementaryAbelianMaxJ S :=
    (show E ≤ A from hEq ▸ le_sup_right).trans hAJ
  intro e he
  exact (mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨hEJ he, elemPow_eq_one_of_isElementaryAbelian (p := 2) e he,
      Subgroup.mem_centralizer_iff.mp (hEC he)⟩

end Stellmacher

