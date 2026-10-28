module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.LinearFiveStabilizer
public import Theory.GroupTheory.SolvableResidual.TwoSupplement

/-!
# Normalized local A₈ sections in L₅(2)

The actual local section is perfect and normal in its join with the
normalizing Sylow subgroup. The quotient of this join by the section is a
two-group, so its embedded solvable residual is exactly the original section.
Full Sylow containment identifies the join as a binary flag stabilizer.
The A₈ quotient forces an end-node flag, giving the actual point or hyperplane
stabilizer and hence inner action of every preserving two-power automorphism.

The noncentral two-core of the smaller section is retained throughout.
No additional parabolic placement or quasisimplicity premise is required.

Source: Aschbacher–Smith15.3.32(3), printed p.1133, and A.3.12(5).
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.LinearFiveStabilizer
open BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.FiveParabolicStabilizer

private theorem embedded_residual_join
    {Q : Type*} [Group Q] [Finite Q] (A : Subgroup Q) (S : Sylow 2 Q)
    (hlocal : A ∈ ChapterA.Section03.localCComponents S)
    (hn : S.toSubgroup ≤ normalizer (A : Set Q)) :
    (solvableResidual ↥(A ⊔ S.toSubgroup)).map (A ⊔ S.toSubgroup).subtype = A := by
  let P := A ⊔ S.toSubgroup
  let N := A.subgroupOf P
  let : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hn)
  let : Group.IsPerfect N := hlocal.perfect
  have hsup : N ⊔ S.toSubgroup.subgroupOf P = ⊤ := by
    apply map_injective P.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show A ≤ P from le_sup_left),
      map_subgroupOf_eq_of_le (show S.toSubgroup ≤ P from le_sup_right),
      ← MonoidHom.range_eq_map, range_subtype]
  have hs := (residuals_of_perfect_normal_sup_twoGroup N (S.toSubgroup.subgroupOf P)
    S.isPGroup'.comap_subtype hsup).2
  change (solvableResidual P).map P.subtype = A
  rw [hs, map_subgroupOf_eq_of_le (show A ≤ P from le_sup_left)]

private instance : Finite (LinearGroup 5) :=
  Finite.of_injective (fun g : LinearGroup 5 => (g : Space 5 → Space 5)) DFunLike.coe_injective

/-- A local binary-four section normalized by a full Sylow in GL₅(2) is an
actual point or hyperplane stabilizer, including its noncentral two-core. -/
theorem endParabolic_of_normalized_local
    (A : Subgroup (LinearGroup 5)) (S : Sylow 2 (LinearGroup 5))
    (hA : ClassicalGroup.IsPSL (XiQuotient A) 4 2)
    (hlocal : A ∈ ChapterA.Section03.localCComponents S)
    (hn : S.toSubgroup ≤ normalizer (A : Set (LinearGroup 5))) :
    IsEndParabolic A := by
  let P := A ⊔ S.toSubgroup
  have hres : (solvableResidual P).map P.subtype = A := embedded_residual_join A S hlocal hn
  have hproper := parabolic_ne_top_of_residual_quotient A P hres hA
  have hfive := five_dvd_card_of_residual_quotient A P hres hA
  obtain ⟨b, cuts, hflag⟩ := isFlagParabolic_of_sylow_le S P le_sup_right
  rw [← hres, hflag]
  exact endParabolic_embeddedResidual_of_five_dvd b cuts
    (hflag ▸ hproper) (hflag ▸ hfive)

/-- The actual full-Sylow normalized local hypotheses supply the placement
needed for inner action, without an additional parabolic-residual premise. -/
theorem twoStabilizerActsInner_of_normalized_local
    {Q : Type*} [Group Q] [Finite Q] (hQ : ClassicalGroup.IsPSL Q 5 2)
    (A : Subgroup Q) (S : Sylow 2 Q)
    (hA : ClassicalGroup.IsPSL (XiQuotient A) 4 2)
    (hlocal : A ∈ ChapterA.Section03.localCComponents S)
    (hn : S.toSubgroup ≤ normalizer (A : Set Q)) :
    TwoStabilizerActsInner A := by
  let e := binaryFiveEquiv hQ
  apply twoStabilizerActsInner_of_endParabolic e
  have hA' : ClassicalGroup.IsPSL (XiQuotient (A.map e.toMonoidHom)) 4 2 := by
    let f := e.subgroupMap A
    exact hA.of_mulEquiv (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).symm
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hlocal' : A.map e.toMonoidHom ∈ ChapterA.Section03.localCComponents T := by
    let : Group.IsSolvable e.toMonoidHom.ker := by
      rw [e.toMonoidHom.ker_eq_bot e.injective]
      infer_instance
    exact Section02.localCComponents_map_of_solvable_ker hlocal e.toMonoidHom
  exact endParabolic_of_normalized_local _ T hA' hlocal'
    ((map_mono hn).trans (le_normalizer_map e.toMonoidHom))

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.LinearFiveStabilizer
