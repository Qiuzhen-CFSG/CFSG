module
public import Stellmacher.SectionEight.LemmaEightOneOffender
public import Stellmacher.SectionEight.LocalQuotientHypotheses
public import Stellmacher.SectionOne.OneSevenDihedralQuotient

/-!
# The faithful critical quotient from a dihedral core quotient

For the actual noncommuting critical-pair context, an explicit isomorphism
of the initial stabilizer modulo its two-core to an odd dihedral group
identifies its faithful center-action quotient with SL₂(2). This makes
explicit the first-paragraph consequence of (6.3) in Stellmacher (8.2),
Journal of Algebra 190 (1997), p.37. The core-quotient isomorphism remains
an explicit premise to be supplied by the eventual (8.2) caller.

The local center lies in the center of the two-core by (7.3), so the exact
witness projection factors through that core quotient. Local solvability,
faithfulness and the actual opposite endpoint offender supply the Section1
hypotheses and nontrivial J. The image of the distinguished Sylow is a
Sylow in the witness quotient; the odd-dihedral action theorem then gives
SL₂(2). The named witness action is reused throughout, and no pending
(6.3) or (8.2) declaration is imported or invoked.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem local_quotient_isSL2Two_of_dihedral_core
    {G : Type u} [Group G] [Finite G]
    {S0 : Sylow 2 G} {S P1 P2 : Subgroup G}
    (ctx : SectionEightContext G S0 S P1 P2)
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (n : ℕ)
    (eD : (GAt ctx.Γ ctx.criticalPath.a ⧸ pCore 2 (GAt ctx.Γ ctx.criticalPath.a)) ≃*
      DihedralGroup (3 ^ n)) :
    let _ := w.groupX
    let _ := w.finiteX
    IsSL2Two w.X := by
  classical
  let := w.groupX
  let := w.finiteX
  let := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
  let h := ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a
  let Sb := (S.subgroupOf P).map w.projection
  have h74 := lemma_seven_four h Γ cp
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hlen := cp.length_pos
  let last : Γ.Vertex := cp.path ⟨cp.length - 1, by omega⟩
  have hlastadj : Γ.adjacent cp.a' last := by
    have he := cp.path_adj ⟨cp.length - 1, by omega⟩
    have hi : (⟨cp.length - 1, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      simp
      omega
    rw [hi, cp.path_end] at he
    exact Γ.adjacent_symm he
  have hlast := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hlastadj
  let := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hfirst
  let := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hlast
  have hSP : S ≤ P := cp.S_le_edge_stabilizers.trans inf_le_left
  have hnotcentral : ¬ z Γ cp.a' ≤ Subgroup.centralizer (z Γ cp.a : Set G) := by
    intro hc
    apply ctx.commutator_ne
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hc
  have hlocal := local_quotient_hypotheses h Γ cp.a hfirst w (z Γ cp.a')
    h74.reverse_containment.1 hnotcentral
  have hP := (SevenSix.edge_local_data h Γ cp).1
  obtain ⟨_, U, hU⟩ := hP.1.1.2.1
  have hUSP : (U : Subgroup P) = S.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hSP]
    exact hU
  let Ub := U.mapSurjective w.surjective
  have hUb : (Ub : Subgroup w.X) = Sb := by
    change (U : Subgroup P).map w.projection = _
    rw [hUSP]
  have hZcentral : z Γ cp.a ≤ Subgroup.centralizer (q Γ cp.a : Set G) :=
    ((lemma_seven_three h Γ).center_core cp.a cp.firstStep hfirst).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
        (SevenSix.centerAmbient_le_centralizer _))
  have hQcentral : q Γ cp.a ≤ Subgroup.centralizer (z Γ cp.a : Set G) :=
    Subgroup.le_centralizer_iff.mp hZcentral
  have hker : pCore 2 P ≤ w.projection.ker := by
    intro x hx
    rw [w.kernel_eq]
    refine ⟨x.property, hQcentral ?_⟩
    change (x : G) ∈ Γ.twoCoreAt cp.a
    rw [Γ.twoCoreAt_def]
    exact Subgroup.mem_map_of_mem P.subtype hx
  let f := QuotientGroup.lift (pCore 2 P) w.projection hker
  have hf : Function.Surjective f :=
    QuotientGroup.lift_surjective_of_surjective _ _ w.surjective hker
  let qD : DihedralGroup (3 ^ n) →* w.X := f.comp eD.symm.toMonoidHom
  have hqD : Function.Surjective qD := hf.comp eD.symm.surjective
  have hJnot : SectionOne.oneJ (V := z Γ cp.a) (Ub : Subgroup w.X) ≠ ⊥ := by
    rw [hUb]
    exact (lemma_eight_one_offender ctx w).2
  exact SectionOne.isSL2Two_of_odd_dihedral_quotient hlocal Ub hJnot
    (3 ^ n) (by exact (by decide : Odd 3).pow) qD hqD

end Stellmacher.SectionEight
