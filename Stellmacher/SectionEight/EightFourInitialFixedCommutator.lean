module
public import Stellmacher.SectionEight.EightFourFixedClosureElementary
public import Stellmacher.SectionEight.LocalQuotientSylowActionSetup
public import Stellmacher.SectionOne.OneSevenCommutatorFixed
/-!
# The initial fixed subgroup is the opposite-closure commutator

For the actual local centered-first-step context and faithful quotient witness,
the commutator of the initial center with the opposite-center closure S1
is exactly the canonical J-fixed subgroup. This is the fixed/commutator
identity behind source (4) of Stellmacher (8.4), printed pp.38--39,
Journal of Algebra 190 (1997).

The opposite closure has precisely the J-image in the faithful action.
The natural-factor product shows that J fixes its action commutator and
that its fixed space is covered by that commutator and the E-fixed space.
The latter vanishes because the initial residual has trivial centralizer
in the initial center. Mapping both inclusions through the original center
subtype identifies the actual ambient commutator, retaining the exact
quotient witness and opposite closure. The canonical public theorem remains
an exact wrapper through the same local graph and action.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_four_initial_fixed_commutator_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S) :
    ⁅ZAt ctx.Γ ctx.criticalPath.a,oppositeClosureLocal ctx⁆ = w.oneJFixedPoints S := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.sectionSeven
  let P := GAt Γ cp.a
  let Za := ZAt Γ cp.a
  let K := oppositeClosureLocal ctx
  let _ := w.groupX
  let _ := w.finiteX
  let _ := MulDistribMulAction.compHom Za w.action
  let Sb := (S.subgroupOf P).map w.projection
  let J := SectionOne.oneJ (V := Za) Sb
  let E := SectionOne.oneE (V := Za) Sb
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hfirst
  have hSP : S ≤ P := cp.S_le_edge_stabilizers.trans inf_le_left
  have hKP : K ≤ P := (opposite_closure_normal_sylow_local ctx).1.trans hSP
  have himage : (K.subgroupOf P).map w.projection = J :=
    eight_four_opposite_closure_image_local ctx hcenter w hbranch
  have hlocal := (local_quotient_sylow_action_setup h Γ cp w).1
  obtain ⟨_, U, hU⟩ := (SevenSix.edge_sylow_data h Γ cp).1
  have hUS : (U : Subgroup P) = S.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hSP]
    exact hU
  let Ub := U.mapSurjective w.surjective
  have hUb : (Ub : Subgroup w.X) = Sb := by
    change (U : Subgroup P).map w.projection = _
    rw [hUS]
  have hcover := SectionOne.oneSeven_fixed_le_fixed_sup_commutator hlocal Ub
  have hreverse := SectionOne.oneSeven_commutator_le_fixed hlocal Ub
  rw [hUb] at hcover hreverse
  have hEzero : FixedPoints.subgroup E Za = ⊥ := by
    apply le_bot_iff.mp
    intro v hv
    have hres : ((EAt Γ cp.a).subgroupOf P).map w.projection ≤ E := by
      rw [show E = _ from lemma_eight_one_residual_join_local ctx w]
      exact le_sup_left
    have hvres : v ∈ FixedPoints.subgroup
        (((EAt Γ cp.a).subgroupOf P).map w.projection) Za :=
      fun r => hv ⟨r, hres r.property⟩
    have hEaP : EAt Γ cp.a ≤ P := by
      rw [show EAt Γ cp.a = twoResidualIn P from Γ.twoResidualAt_def cp.a]
      exact Subgroup.map_subtype_le _
    have hvmap := Subgroup.mem_map_of_mem Za.subtype hvres
    rw [w.fixedPoints_map_subtype (EAt Γ cp.a) hEaP,
      eight_four_initial_residual_center_trivial_local ctx hcenter] at hvmap
    exact Subtype.ext hvmap
  have hEq : commutatorAction J Za = FixedPoints.subgroup J Za := by
    apply le_antisymm hreverse
    exact hcover.trans (by rw [hEzero,bot_sup_eq])
  have hm := congrArg (Subgroup.map Za.subtype) hEq
  rw [← himage,w.commutatorAction_image_map_subtype K hKP] at hm
  rw [himage] at hm
  exact hm
public theorem eight_four_initial_fixed_commutator
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S) :
    ⁅ZAt ctx.Γ ctx.criticalPath.a,oppositeClosure ctx⁆ = w.oneJFixedPoints S := by
  exact eight_four_initial_fixed_commutator_local ctx.toLocalContext hcenter w hbranch

end Stellmacher.SectionEight
