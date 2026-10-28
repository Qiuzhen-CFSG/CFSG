module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.PointCoreMovement
public import Theory.Representation.BinaryConjugationSection.PointStabilizerRank
public import Theory.Representation.BinaryPermutation.PointStabilizerRank

/-!
# The eight-letter natural section at the original point normalizer

Every vector of the binary deleted permutation module on eight letters is
fixed by an elementary nine-subgroup: the alternating groups on its zero
and one supports have combined three-rank at least two. Cubic stabilizers
lift through the literal central point kernel to the centralizer of V₂.
This contradicts its three-rank bound from 14.7.4(3).

For the original point normalizer, the actual A₈ component of its S₈ star
quotient forces point-core movement, using the earlier faithful-component
classification. The resulting exclusion and its many-overgroup application
have no separate movement or point-normality premise.

This excludes the six-dimensional natural action on the whole U/V₁.
Recognition and lifting through an arbitrary proper invariant quotient,
as used in the full source 14.7.51, remain separate source obligations.
No residual alternative or Data construction is asserted here.

Source: Aschbacher–Smith, 14.7.4(3), printed p.1043, and the S₈ orthogonal
case of 14.7.51, printed p.1065, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
open BinaryNaturalDual.VectorStabilizers
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem eight_stabilizer_rank (v : BinaryPermutation.natural (Fin 8)) :
    2 ≤ primeRank 3 (representationStabilizer
      (BinaryPermutation.naturalRepresentation (Fin 8)) v) := by
  let S := representationStabilizer (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)) v
  let R := representationStabilizer (BinaryPermutation.naturalRepresentation (Fin 8)) v
  let f : S →* R := ((alternatingGroup (Fin 8)).subtype.comp S.subtype).codRestrict R
    (fun a => a.property)
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun r : R => (r : Equiv.Perm (Fin 8))) he
  exact (BinaryPermutation.PointStabilizerRank.two_le_natural_stabilizer
    (by simp : 8 ≤ Fintype.card (Fin 8)) v).trans
      (Theory.GroupTheory.primeRank_le_of_injective 3 f hf)

/-- The actual six-dimensional deleted S₈ section is impossible in every
original local, whenever the point core moves the flag plane. -/
theorem local_eight_natural_impossible_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hm : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (e : HStar I ≃* Equiv.Perm (Fin 8))
    (c : BinaryConjugationSection I (F.UH I) (F.Vi 1)
      ((BinaryPermutation.naturalRepresentation (Fin 8)).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))))) : False := by
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 π.ker := by
    change IsPGroup 2 (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))).ker
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hp : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hplane : (F.Vi 1).relIndex (F.Vi 2) = 2 := by
    have hh := ((F.Vi 1).subgroupOf (F.Vi 2)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (F.monotone (by decide : 1 ≤ 2))).toEquiv,hp] at hh
    have hc : Nat.card (F.Vi 2) = 4 := by simpa using F.card 2 (by decide)
    change 2 * (F.Vi 1).relIndex (F.Vi 2) = Nat.card (F.Vi 2) at hh
    omega
  have hnot : ¬ F.Vi 2 ≤ F.Vi 1 := by
    intro hle
    have he := le_antisymm hle (F.monotone (by decide : 1 ≤ 2))
    rw [he,relIndex_self] at hplane
    omega
  obtain ⟨v,hv,hvZ⟩ := SetLike.not_le_iff_exists.mp hnot
  let vU : F.UH I := ⟨v,(le_conjugateSpanBy V I) (F.le_seed 2 hv)⟩
  have hr := c.point_threeRank_le (BinaryPermutation.naturalRepresentation (Fin 8)) π
    hπ hk (F.Vi 2) (F.monotone (by decide : 1 ≤ 2)) hplane hp
    (hI.2.1.trans (normalizer_le_centralizer_of_card_two _ hp)) vU hv hvZ
  have hu := (eight_stabilizer_rank (c.coordinates vU).toAdd).trans hr
  have hbound := plane_centralizer_three_rank_le_one_at h structural hm
  omega

/-- The actual alternating component in an S₈ star quotient supplies the
point-core movement needed by the local exclusion. -/
theorem plane_moved_of_symmetric_eight_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (e : HStar F.H ≃* Equiv.Perm (Fin 8)) :
    ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥ := by
  let A := alternatingGroup (Fin 8)
  let : IsSimpleGroup A := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect A := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have hA : A.IsCComponent := isCComponent_of_isSimpleGroup_of_isPerfect
    (inferInstance : A.Normal).isSubnormal
  apply plane_moved_of_large_star_component_at h structural previous faithful
    (A.map e.symm.toMonoidHom) (hA.map_equiv e.symm)
  rw [←Nat.card_congr (A.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).toEquiv]
  change 168 < Nat.card (alternatingGroup (Fin 8))
  rw [nat_card_alternatingGroup,Nat.card_fin]
  norm_num

/-- The six-dimensional deleted S₈ section at the original point normalizer
is excluded without assuming point normality or core movement. -/
theorem original_eight_natural_impossible_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (e : HStar F.H ≃* Equiv.Perm (Fin 8))
    (c : BinaryConjugationSection F.H F.U (F.Vi 1)
      ((BinaryPermutation.naturalRepresentation (Fin 8)).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F.H))))) : False :=
  local_eight_natural_impossible_at h structural
    (plane_moved_of_symmetric_eight_at h structural previous faithful e) F.H
    (h.point_mem_Hz_at F previous) e c

/-- The same S₈ exclusion at the literal many-overgroup consumer. -/
theorem original_eight_natural_impossible_of_many_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (e : HStar F.H ≃* Equiv.Perm (Fin 8))
    (c : BinaryConjugationSection F.H F.U (F.Vi 1)
      ((BinaryPermutation.naturalRepresentation (Fin 8)).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F.H))))) : False :=
  original_eight_natural_impossible_at h (structural hmany) (previous hmany) faithful e c

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
