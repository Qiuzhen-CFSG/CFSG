module
public import Stellmacher.QuotientModuleWitness
public import Stellmacher.SectionEight.LocalQuotientCore
public import Stellmacher.SectionOne.Defs
public import Stellmacher.SectionFiveToSeven.Result7_3

/-!
# Section 1 hypotheses for local center quotients

Under the Section 7 graph hypotheses, the centralizer quotient of a vertex
stabilizer acts faithfully on its center module. If an elementary abelian
subgroup Y of that stabilizer acts nontrivially on the module, this quotient
has even order and satisfies all standing hypotheses of Section 1.

Solvability comes from the existing edge-transport data of (7.3) and passes
to the quotient. The explicit witness action is faithful by its centralizer
kernel, and the local Sylow-center argument supplies trivial 2-core. The
nontrivial elementary image of Y has even order; subgroup divisibility then
gives even order of the quotient.

This is the setup used at both endpoints when applying (1.5) and (1.7) in
Stellmacher (8.1), journal p.37. The exact witness action instance is retained
throughout; the module's elementary abelian structure is an explicit instance.
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

/-- A nontrivial elementary actor supplies the Section 1 local quotient setup. -/
public theorem local_quotient_hypotheses
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) (d : Γ.Vertex)
    {l : Γ.Vertex} (hl : l ∈ neighborhood Γ d)
    [IsElementaryAbelian 2 (z Γ d)]
    (w : QuotientModuleWitness (stabilizer Γ d)
      (stabilizer Γ d ⊓ Subgroup.centralizer (z Γ d : Set G)) (z Γ d))
    (Y : Subgroup G) (hYA : Y ≤ stabilizer Γ d)
    [IsElementaryAbelian 2 Y]
    (hYnot : ¬ Y ≤ Subgroup.centralizer (z Γ d : Set G)) :
    let _ := w.groupX
    let _ := w.finiteX
    let _ := MulDistribMulAction.compHom (z Γ d) w.action
    SectionOne.Hypotheses w.X (z Γ d) := by
  let := w.groupX
  let := w.finiteX
  let := MulDistribMulAction.compHom (z Γ d) w.action
  let : Group.IsSolvable (stabilizer Γ d) :=
    stabilizer_solvable_of_neighbor h Γ hl
  let Yb : Subgroup w.X := (Y.subgroupOf (stabilizer Γ d)).map w.projection
  let : IsElementaryAbelian 2 (Y.subgroupOf (stabilizer Γ d)) :=
    IsElementaryAbelian.subgroupOf hYA
  let : IsElementaryAbelian 2 Yb := IsElementaryAbelian.map w.projection
  have hYb : Yb ≠ ⊥ := by
    intro hbot
    apply hYnot
    intro y hy
    let yA : stabilizer Γ d := ⟨y, hYA hy⟩
    have hmem : w.projection yA ∈ Yb := Subgroup.mem_map_of_mem w.projection hy
    rw [hbot, Subgroup.mem_bot] at hmem
    have hk : yA ∈ w.projection.ker := hmem
    rw [w.kernel_eq] at hk
    exact hk.2
  let : Nontrivial Yb := (Subgroup.nontrivial_iff_ne_bot Yb).mpr hYb
  obtain ⟨n, hn, hcard⟩ :=
    (IsElementaryAbelian.isPGroup 2 Yb).nontrivial_iff_card.mp inferInstance
  have heven : Even (Nat.card w.X) := by
    apply even_iff_two_dvd.mpr
    apply (show 2 ∣ Nat.card Yb by
      rw [hcard]
      exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn)).trans
    exact Subgroup.card_subgroup_dvd_card Yb
  exact {
    G_solvable := Group.isSolvable_of_surjective w.surjective
    G_even := heven
    action_faithful := w.action_faithful
    twoCore_eq_bot := local_quotient_twoCore_eq_bot Γ d w }

end Stellmacher.SectionEight

