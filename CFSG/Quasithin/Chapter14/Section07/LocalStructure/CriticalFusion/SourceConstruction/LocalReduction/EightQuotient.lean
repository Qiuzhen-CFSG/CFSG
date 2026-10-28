module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightNatural
public import Theory.Representation.BinaryConjugationSection.FixedQuotientRank

/-!
# Excluding the S₈ quotient above its fixed space

The binary deleted S₈ module has vector stabilizers of three-rank at least
two. This obstruction survives any equivariant quotient of the original
U_H/V₁ whose kernel is fixed by the actual two-residual: cubic elements
fix their original lifts, so the stabilizer rank still bounds the literal
centralizer of V₂. The source bound 14.7.4(3) contradicts that rank.

At the full point normalizer the actual alternating component supplies
point-core movement. The final application constructs the projection from
U/V₁ onto its quotient by the full fixed space and proves the kernel
condition. It retains the original star marking, all conjugation maps,
and the same-G,T guarded earlier inputs.

This proves the fixed-space-quotient S₈ obstruction used in 14.7.38,
printed p.1060 of Aschbacher–Smith, refs/quasithin.pdf. The maximal
invariant quotient in 14.7.51 has a possibly noncentral kernel; its
14.7.2(3) lifting argument and the remaining source classification are
still required. No Data or whole-residual component premise is assumed.
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

/-- The S₈ natural quotient obstruction permits any two-residual-fixed
kernel above the quotient, without identifying the whole local section. -/
theorem local_eight_residual_fixed_quotient_impossible_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hm : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (e : HStar I ≃* Equiv.Perm (Fin 8))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) I W}
    (c : BinaryConjugationSection I (F.UH I) (F.Vi 1) ρ)
    (p : ρ.IntertwiningMap ((BinaryPermutation.naturalRepresentation (Fin 8)).comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I)))))
    (hk : p.toLinearMap.ker ≤ invariants (ρ.comp (pResidual 2 I).subtype)) : False := by
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπk : IsPGroup 2 π.ker := by
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
  have hr := c.point_threeRank_le_of_residual_fixed_quotient
    (BinaryPermutation.naturalRepresentation (Fin 8)) π hπ hπk p hk
    (F.Vi 2) (F.monotone (by decide : 1 ≤ 2)) hplane hp
    (hI.2.1.trans (normalizer_le_centralizer_of_card_two _ hp)) vU hv hvZ
  let w := p (c.coordinates vU).toAdd
  let S := representationStabilizer (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)) w
  let R := representationStabilizer (BinaryPermutation.naturalRepresentation (Fin 8)) w
  let f : S →* R := ((alternatingGroup (Fin 8)).subtype.comp S.subtype).codRestrict R
    (fun a => a.property)
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun r : R => (r : Equiv.Perm (Fin 8))) he
  have hl : 2 ≤ primeRank 3 R :=
    (BinaryPermutation.PointStabilizerRank.two_le_natural_stabilizer
      (by simp : 8 ≤ Fintype.card (Fin 8)) w).trans
      (Theory.GroupTheory.primeRank_le_of_injective 3 f hf)
  have hbound := plane_centralizer_three_rank_le_one_at h structural hm
  have hu := hl.trans hr
  omega

/-- At the original point, the A₈ component forces the movement needed by
the quotient obstruction. The kernel is fixed by the literal source residual K. -/
theorem original_eight_residual_fixed_quotient_impossible_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (e : HStar F.H ≃* Equiv.Perm (Fin 8))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (p : ρ.IntertwiningMap ((BinaryPermutation.naturalRepresentation (Fin 8)).comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F.H)))))
    (hk : p.toLinearMap.ker ≤ invariants (ρ.comp ((K F).subgroupOf F.H).subtype)) : False := by
  have hres : (K F).subgroupOf F.H = pResidual 2 F.H :=
    comap_map_eq_self_of_injective F.H.subtype_injective _
  rw [hres] at hk
  exact local_eight_residual_fixed_quotient_impossible_at h structural
    (plane_moved_of_symmetric_eight_at h structural previous faithful e)
    F.H (h.point_mem_Hz_at F previous) e c p hk

/-- The literal fixed-space quotient in the S₈ branch of 14.7.38 is
impossible. The quotient kernel is constructed, not supplied as a lifting premise. -/
theorem original_eight_fixedSpace_quotient_impossible_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (e : HStar F.H ≃* Equiv.Perm (Fin 8))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (j : (W ⧸ invariants ρ) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8))
    (hj : ∀ g w, j ((invariants ρ).mkQ (ρ g w)) =
      BinaryPermutation.naturalRepresentation (Fin 8)
        (e (QuotientGroup.mk' (pCore 2 F.H) g)) (j ((invariants ρ).mkQ w))) : False := by
  let p : ρ.IntertwiningMap ((BinaryPermutation.naturalRepresentation (Fin 8)).comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F.H)))) :=
    (j.toLinearMap.comp (invariants ρ).mkQ).intertwiningMap_of_isIntertwiningMap ρ _ hj
  apply original_eight_residual_fixed_quotient_impossible_at h structural previous faithful e c p
  intro w hw g
  have hwq : (invariants ρ).mkQ w = 0 := j.injective (by
    change j ((invariants ρ).mkQ w) = j 0
    rw [map_zero]
    exact hw)
  exact ((Submodule.Quotient.mk_eq_zero (invariants ρ)).mp hwq) g.val

/-- The same fixed-space-quotient exclusion at the many-overgroup consumer. -/
theorem original_eight_fixedSpace_quotient_impossible_of_many_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (e : HStar F.H ≃* Equiv.Perm (Fin 8))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (j : (W ⧸ invariants ρ) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8))
    (hj : ∀ g w, j ((invariants ρ).mkQ (ρ g w)) =
      BinaryPermutation.naturalRepresentation (Fin 8)
        (e (QuotientGroup.mk' (pCore 2 F.H) g)) (j ((invariants ρ).mkQ w))) : False :=
  original_eight_fixedSpace_quotient_impossible_at h (structural hmany) (previous hmany)
    faithful e c j hj

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
