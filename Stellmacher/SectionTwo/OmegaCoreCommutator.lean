module

public import Stellmacher.SectionsOneToFourDefs
public import Theory.GroupTheory.Commutator.NormalClosure

/-!
# Omega-core commutators with the Thompson normal closure

Let `H` and `V` be normal subgroups. If `H ≤ C_H(A)V` for every
maximal-order elementary abelian subgroup `A` of `S`, then
`[H, ⟨J(S)^G⟩] ≤ V`. This isolates the normal-closure inference in the
noncentralizing case of Stellmacher (2.3), journal p.20; in that application
`H` is the omega-center of the Thompson subgroup of `O₂(⟨J(S)^G⟩)`.
No Sylow or Section Two hypotheses enter this step.

Modulo `V`, the supplement bound makes the image of `H` centralize every
such `A`. The defining supremum for the actual elementary Thompson subgroup
then gives `[H,J(S)] ≤ V`. The imported normal-closure transfer, using the
normality of both `H` and `V`, extends the bound to the normal closure.
Source: `refs/latex/stellmacher-n-group.tex`, proof of (2.3).
-/

namespace Stellmacher.SectionTwo

public theorem omega_core_normalClosure_commutator_le
    {G : Type*} [Group G] [Finite G] (S H V : Subgroup G)
    [H.Normal] [V.Normal]
    (hcontrol : ∀ A ∈ elementaryAbelianMaxSubgroups S,
      H ≤ (H ⊓ Subgroup.centralizer (A : Set G)) ⊔ V) :
    ⁅H, Subgroup.normalClosure (elementaryAbelianMaxJ S : Set G)⁆ ≤ V := by
  let q := QuotientGroup.mk' V
  have hV : V.map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    simp only [q, QuotientGroup.ker_mk', le_refl]
  have hAcentral : ∀ A ∈ elementaryAbelianMaxSubgroups S,
      A.map q ≤ Subgroup.centralizer (H.map q : Set (G ⧸ V)) := by
    intro A hA
    have hH : H.map q ≤ (H ⊓ Subgroup.centralizer (A : Set G)).map q := by
      have hh := Subgroup.map_mono (f := q) (hcontrol A hA)
      simpa only [Subgroup.map_sup, hV, sup_bot_eq] using hh
    have hC : (H ⊓ Subgroup.centralizer (A : Set G)).map q ≤
        Subgroup.centralizer (A.map q : Set (G ⧸ V)) := by
      have hc : ⁅H ⊓ Subgroup.centralizer (A : Set G), A⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
      apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      rw [← Subgroup.map_commutator, hc, Subgroup.map_bot]
    exact Subgroup.le_centralizer_iff.mp (hH.trans hC)
  have hJ : elementaryAbelianMaxJ S ≤
      (Subgroup.centralizer (H.map q : Set (G ⧸ V))).comap q := by
    apply sSup_le
    intro A hA
    exact Subgroup.map_le_iff_le_comap.mp (hAcentral A hA)
  apply Subgroup.commutator_normalClosure_le_of_normal
  have hzero : (⁅H, elementaryAbelianMaxJ S⁆).map q = ⊥ := by
    rw [Subgroup.map_commutator, Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.map_le_iff_le_comap.mpr hJ)
  have hh := (Subgroup.map_eq_bot_iff _).mp hzero
  simpa only [q, QuotientGroup.ker_mk'] using hh

end Stellmacher.SectionTwo
