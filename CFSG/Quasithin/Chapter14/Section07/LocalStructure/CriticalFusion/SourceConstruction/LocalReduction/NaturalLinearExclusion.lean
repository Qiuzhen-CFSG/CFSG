module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.PointCoreMovement
public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Theory.SpecificGroups.BinaryLinear.ActionCardinality
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# Excluding the binary natural sections in dimensions four and five

The actual L₄(2) and L₅(2) star quotients are simple and larger than either
of the earlier faithful models. The point-core movement theorem therefore
applies to them. A natural identification of U/V₁ gives a surjective action
on the literal tilded section: compare the two quotient coordinate maps,
transport an arbitrary automorphism, and lift its binary linear matrix.
This contradicts the proper plane-centralizer orbit already proved.

The applications retain the original quotient projection and conjugation
section and have same-G,T guarded successors. They prove these two natural
rows at the full original point normalizer. The degree-three row, other
local groups and the later residual alternatives remain source work.

Source: Aschbacher–Smith, 14.7.37(1–2), printed p.1059, refs/quasithin.pdf.
The imported projective simplicity proof retains its ATLAS attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

open BinaryLinear.OuterCyclic
open scoped MatrixGroups

/-- The actual binary linear quotient in dimensions four and five forces
point-core movement through its simple component. -/
theorem plane_moved_of_binary_linear_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (n : ℕ) (hn : n = 4 ∨ n = 5)
    (e : HStar F.H ≃* SL(n,ZMod 2)) :
    ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥ := by
  have hn3 : 3 ≤ n := by omega
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) :=
    Atlas.psl_simple_high_rank n hn3
  let : IsSimpleGroup (LinearGroup n) :=
    (projectiveEquivLinear (by omega : 0 < n)).symm.isSimpleGroup
  let : Group.IsPerfect (LinearGroup n) := BinaryLinear.linearGroup_isPerfect n hn3
  let a := e.trans (slEquivLinear n)
  let : IsSimpleGroup (HStar F.H) := a.isSimpleGroup
  let : Group.IsPerfect (HStar F.H) :=
    Group.IsPerfect.ofSurjective (f := a.symm.toMonoidHom) a.symm.surjective
  let t : (⊤ : Subgroup (HStar F.H)) ≃* HStar F.H := topEquiv
  let : IsSimpleGroup (⊤ : Subgroup (HStar F.H)) := t.isSimpleGroup
  let : Group.IsPerfect (⊤ : Subgroup (HStar F.H)) :=
    Group.IsPerfect.ofSurjective (f := t.symm.toMonoidHom) t.symm.surjective
  have htop : (⊤ : Subgroup (HStar F.H)).IsCComponent :=
    isCComponent_of_isSimpleGroup_of_isPerfect (inferInstance : (⊤ : Subgroup (HStar F.H)).Normal).isSubnormal
  apply plane_moved_of_large_star_component_at h structural previous faithful ⊤ htop
  rw [card_top,Nat.card_congr e.toEquiv,BinaryLinear.card_SL]
  rcases hn with rfl | rfl <;>
    norm_num [BinaryLinear.order,Fin.prod_univ_succ]

private theorem tilde_action_surjective_of_natural
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (n : ℕ) (e : HStar F.H ≃* SL(n,ZMod 2))
    (c : BinaryConjugationSection F.H F.U (F.Vi 1)
      ((specialLinearNatural (k := ZMod 2) n).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F.H))))) :
    Function.Surjective (F.localTildeAction F.H le_rfl) := by
  let := h.chosen.elementary
  change Function.Surjective (F.tildeAction F.H F.U le_rfl
    (le_normalizer_conjugateSpanBy V F.H))
  let E : F.tilde F.U ≃* Multiplicative (Space n) :=
    F.utildeEquiv.symm.trans c.quotientEquiv
  have hE : ∀ u : F.U, E (F.tildeMap F.U F.U_le_H u) = c.coordinates u := by
    intro u
    rw [←F.utildeEquiv_apply_mk]
    exact congrArg c.quotientEquiv (F.utildeEquiv.symm_apply_apply _)
  intro b
  let a : MulAut (Multiplicative (Space n)) := MulAut.congr E b
  let f : Space n ≃ₗ[ZMod 2] Space n :=
    LinearEquiv.ofBijective ((AddMonoidHom.toMultiplicative.symm a.toMonoidHom).toZModLinearMap 2) a.bijective
  obtain ⟨x,hx⟩ := ((slEquivLinear n).surjective.comp
    (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 F.H)))) f
  change slEquivLinear n (e (QuotientGroup.mk' (pCore 2 F.H) x)) = f at hx
  refine ⟨x,?_⟩
  apply MulEquiv.ext
  intro v
  obtain ⟨u,rfl⟩ := F.tildeMap_surjective F.U F.U_le_H v
  apply E.injective
  rw [F.tildeAction_apply_map F.H F.U le_rfl F.U_le_H
    (le_normalizer_conjugateSpanBy V F.H),hE]
  apply Multiplicative.toAdd.injective
  rw [c.equivariant]
  change slEquivLinear n (e (QuotientGroup.mk' (pCore 2 F.H) x))
    (c.coordinates u).toAdd = _
  rw [hx]
  change (a (c.coordinates u)).toAdd = _
  rw [←hE]
  change (E (b (E.symm (E (F.tildeMap F.U F.U_le_H u))))).toAdd = _
  rw [E.symm_apply_apply]

/-- The literal natural section for L₄(2) or L₅(2) at the original point
normalizer is impossible, with movement derived from that actual quotient. -/
theorem original_binary_linear_natural_impossible_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (n : ℕ) (hn : n = 4 ∨ n = 5)
    (e : HStar F.H ≃* SL(n,ZMod 2))
    (c : BinaryConjugationSection F.H F.U (F.Vi 1)
      ((specialLinearNatural (k := ZMod 2) n).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F.H))))) : False := by
  exact local_tilde_action_not_surjective_at h structural
    (plane_moved_of_binary_linear_at h structural previous faithful n hn e) F.H
    (h.point_mem_Hz_at F previous) (tilde_action_surjective_of_natural h n e c)

/-- The binary natural exclusions under the original many-overgroup guard. -/
theorem original_binary_linear_natural_impossible_of_many_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (n : ℕ) (hn : n = 4 ∨ n = 5)
    (e : HStar F.H ≃* SL(n,ZMod 2))
    (c : BinaryConjugationSection F.H F.U (F.Vi 1)
      ((specialLinearNatural (k := ZMod 2) n).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F.H))))) : False :=
  original_binary_linear_natural_impossible_at h (structural hmany) (previous hmany)
    faithful n hn e c

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
