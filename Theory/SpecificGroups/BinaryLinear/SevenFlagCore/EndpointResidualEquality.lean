module
public import Theory.SpecificGroups.BinaryLinear.SevenFlagCore.ResidualRectangles
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoBlocks
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.GroupTheory.PResidual.PerfectImage
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models

/-!
# The original endpoint join equals its two-residual

The literal moving core already contains the whole endpoint radical.
The marked PSL3(2) quotient is perfect, so its two-residual is the whole
quotient. The radical and residual therefore generate the full endpoint
parabolic, and radical containment makes the residual equal the parabolic.
-/
public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace BinaryLinear.SevenFlagCore
open OuterCyclic InvariantNodeActions SmallParabolicLevi
private instance : Finite (LinearGroup 4) :=
  Finite.of_injective (fun g : LinearGroup 4 => (g : Space 4 → Space 4)) DFunLike.coe_injective

private theorem residual_top_of_core_le {X : Type*} [Group X] [Finite X]
    (e : (X ⧸ pCore 2 X) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcore : pCore 2 X ≤ pResidual 2 X) : pResidual 2 X=⊤ := by
  let := Atlas.psl_perfect (F := ZMod 2) 3 (by decide)
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Group.IsPerfect.ofSurjective
      (f := Atlas.Comparisons.Exceptional.sl3TwoEquivPsl3Two.symm.toMonoidHom)
      Atlas.Comparisons.Exceptional.sl3TwoEquivPsl3Two.symm.surjective
  let : Group.IsPerfect (X ⧸ pCore 2 X) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hm : (pResidual 2 X).map (QuotientGroup.mk' (pCore 2 X))=⊤ := by
    rw [map_pResidual_quotient,pResidual_eq_top_of_isPerfect]
  have hh := congrArg (Subgroup.comap (QuotientGroup.mk' (pCore 2 X))) hm
  rwa [comap_map_eq_self (by simpa only [QuotientGroup.ker_mk'] using hcore),comap_top] at hh

/-- For either literal GL4 endpoint with the specified PSL3 quotient,
the embedded two-residual equals the whole endpoint subgroup. -/
theorem endpoint_residual_eq_self_of_quotient
    (b : Basis 3) (last : Bool)
    (e : ((cutStabilizer b ({if last then 2 else 0} : Set (Fin 3))) ⧸
      pCore 2 (cutStabilizer b ({if last then 2 else 0} : Set (Fin 3)))) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    let P := cutStabilizer b ({if last then 2 else 0} : Set (Fin 3))
    (pResidual 2 P).map P.subtype=P := by
  let k : Fin 3 := if last then 2 else 0
  let P := cutStabilizer b ({k} : Set (Fin 3))
  let R := (pResidual 2 P).map P.subtype
  have hP : P=parabolic (cutSpace b k) := by
    ext g
    simp only [P,cutStabilizer,mem_iInf,Set.mem_singleton_iff,forall_eq]
  have hrad : P.pCoreIn 2=radical (cutSpace b k) := by
    rw [hP]
    exact map_twoCore_eq_radical _
  have hmove : ⁅R.pCoreIn 2,R⁆=radical (cutSpace b k) :=
    (endpoint_residual_moving_rectangle b last).1
  have hRR : ⁅R.pCoreIn 2,R⁆ ≤ R :=
    (commutator_mono (R.pCoreIn_le 2) le_rfl).trans (commutator_le_self R)
  have hcore : pCore 2 P ≤ pResidual 2 P := by
    apply (Subgroup.map_le_map_iff_of_injective P.subtype_injective).mp
    change P.pCoreIn 2 ≤ R
    rw [hrad,←hmove]
    exact hRR
  let : Finite P := Finite.of_injective
    (fun g : P => (g.val : Space 4 → Space 4))
    (fun _ _ h => Subtype.ext (DFunLike.coe_injective h))
  have ht := residual_top_of_core_le e hcore
  change (pResidual 2 P).map P.subtype=P
  rw [ht,←MonoidHom.range_eq_map,range_subtype]

end BinaryLinear.SevenFlagCore
