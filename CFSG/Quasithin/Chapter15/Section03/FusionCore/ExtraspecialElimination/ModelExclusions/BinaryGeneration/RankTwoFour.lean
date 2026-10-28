module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.BinaryGeneration.Lifting
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.BinaryGeneration.FlagCoordinates
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.Levi.FourComponent.Flags
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four.Bruhat
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four.StandardOvergroups

/-!
# Degree-four generation by intrinsic rank-two parabolics

A minimal parabolic omits one of the three cuts in a Sylow basis flag.
Retaining either of its other cuts gives a rank-two overgroup. The line
and hyperplane cases have diagonal blocks 1+3 and 3+1, hence intrinsic
quotient PSL₃(2); the middle case has blocks 2+2, hence quotient S₃ × S₃.
We reuse the checked two-block action and its exact two-core kernel.

The degree-four Bruhat theorem identifies every overgroup of the full
flag stabilizer with a partial flag stabilizer. An overgroup of two
distinct single-cut stabilizers can retain neither cut, so it is the
whole linear group. Basis conjugation and the supplied component model
transport this calculation to the original ambient subgroups. The core
transport uses `pCore_map_iso`, so the quotients are literally Q/O₂(Q).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
p.1145, the L₄(2) generation paragraph in the proof of 15.3.49. This
proves the intrinsic degree-four helper; the parent owns quotient lifting
and the outer-action alternative.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics
open BinaryLinear.SmallParabolicLevi

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.BinaryGeneration

/-- The nonadjacent omitted nodes give two actual binary two-dimensional blocks. -/
noncomputable def fourMiddleQuotientEquiv (b : Basis 3) :
    (cutStabilizer b {1} ⧸ pCore 2 (cutStabilizer b {1})) ≃*
      Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) :=
  (fourCutQuotientEquiv b 1).trans
    (((linearGroupCongr (fourCutCoordinates b 1)).prodCongr
      (linearGroupCongr (fourQuotientCoordinates b 1))).trans
        (linearTwoEquivSymmetricThree.prodCongr linearTwoEquivSymmetricThree))

/-- Each of the three single-cut parabolics has one of the required intrinsic quotients. -/
lemma fourCut_small (b : Basis 3) (i : Fin 3) : SmallQuotient (cutStabilizer b {i}) := by
  fin_cases i
  · exact Or.inr ⟨fourLineQuotientEquiv b⟩
  · exact Or.inl ⟨fourMiddleQuotientEquiv b⟩
  · exact Or.inr ⟨fourHyperplaneQuotientEquiv b⟩

/-- Two distinct retained cuts give parabolics generating the whole binary four-space group. -/
lemma fourCuts_generate (b : Basis 3) (i j : Fin 3) (hij : i ≠ j) :
    cutStabilizer b {i} ⊔ cutStabilizer b {j} = ⊤ := by
  have hstd : cutStabilizer Four.standardBasis {i} ⊔
      cutStabilizer Four.standardBasis {j} = ⊤ := by
    obtain ⟨cuts, he⟩ := Four.standard_overgroups_of_bruhat Four.hasBruhatDecomposition
      (cutStabilizer Four.standardBasis {i} ⊔ cutStabilizer Four.standardBasis {j})
      (((cutStabilizer_le_iff _ _ _).mpr (Set.subset_univ _)).trans le_sup_left)
    have hi : cuts ⊆ ({i} : Set (Fin 3)) :=
      (cutStabilizer_le_iff _ _ _).mp (he ▸ le_sup_left)
    have hj : cuts ⊆ ({j} : Set (Fin 3)) :=
      (cutStabilizer_le_iff _ _ _).mp (he ▸ le_sup_right)
    have hc : cuts = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro k hk
      exact hij ((hi hk).symm.trans (hj hk))
    simpa [hc, cutStabilizer] using he
  let g := Four.standardBasis.equiv b (Equiv.refl _)
  have ht (cuts : Set (Fin 3)) :
      (cutStabilizer Four.standardBasis cuts).map (MulAut.conj g).toMonoidHom =
        cutStabilizer b cuts := by
    rw [Four.cutStabilizer_map_conj]
    congr 1
    ext k
    simp [g]
  rw [← ht {i}, ← ht {j}, ← Subgroup.map_sup, hstd,
    Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective]

/-- The rank-two flag retains exactly one of the three proper cuts. -/
noncomputable def rankTwoFlagFour (b : Basis 3) (i : Fin 3) : Flag 4 where
  spaces := {cutSpace b i}
  nonempty := Finset.singleton_nonempty _
  proper W hW := by
    have he : W = cutSpace b i := Finset.mem_singleton.mp hW
    subst W
    have hd := cutSpace_finrank b i
    constructor <;> intro h
    · rw [h, finrank_bot] at hd
      omega
    · rw [h, finrank_top, Module.finrank_fin_fun] at hd
      have := i.isLt
      omega
  chain W hW W' hW' := by
    have hW := Finset.mem_singleton.mp hW
    have hW' := Finset.mem_singleton.mp hW'
    exact Or.inl (by rw [hW, hW'])

/-- The retained geometric dimension is exactly the specified cut dimension. -/
lemma rankTwoFlagFour_types (b : Basis 3) (i : Fin 3) :
    (rankTwoFlagFour b i).types = {i.val + 1} := by
  classical
  simp [Flag.types, rankTwoFlagFour, cutSpace_finrank]

variable {X : Type*} [Group X] {K : Subgroup X}

/-- The actual flag stabilizer is the transported singleton-cut stabilizer. -/
lemma rankTwoFlagFour_stabilizer (e : K ≃* PSL 4) (b : Basis 3) (i : Fin 3) :
    flagStabilizer e (rankTwoFlagFour b i) =
      (cutStabilizer b {i}).comap (linearModel e).toMonoidHom := by
  ext g
  simp [mem_flagStabilizer, rankTwoFlagFour, mem_cutStabilizer]

/-- Restrict the specified component model to the actual ambient rank-two overgroup. -/
noncomputable def rankTwoFourModelEquiv (e : K ≃* PSL 4) (b : Basis 3) (i : Fin 3) :
    ambientFlagStabilizer e (rankTwoFlagFour b i) ≃* cutStabilizer b {i} := by
  let a := linearModel e
  let U := (cutStabilizer b {i}).comap a.toMonoidHom
  let f : U ≃* cutStabilizer b {i} :=
    MulEquiv.ofBijective (a.toMonoidHom.subgroupComap _)
      ⟨fun _ _ h => Subtype.ext (a.injective (congrArg Subtype.val h)),
        a.toMonoidHom.subgroupComap_surjective_of_surjective _ a.surjective⟩
  have hU : ambientFlagStabilizer e (rankTwoFlagFour b i) = U.map K.subtype := by
    rw [ambientFlagStabilizer, rankTwoFlagFour_stabilizer]
  exact (MulEquiv.subgroupCongr hU).trans
    ((U.equivMapOfInjective K.subtype K.subtype_injective).symm.trans f)

/-- Transport the intrinsic two-core and the literal small quotient to the ambient subgroup. -/
lemma rankTwoFlagFour_small (e : K ≃* PSL 4) (b : Basis 3) (i : Fin 3) :
    SmallQuotient (ambientFlagStabilizer e (rankTwoFlagFour b i)) := by
  let f := rankTwoFourModelEquiv e b i
  let q := QuotientGroup.congr _ _ f (pCore_map_iso 2 f)
  have hs := fourCut_small b i
  change _ ∨ _ at hs
  rcases hs with h | h
  · obtain ⟨h⟩ := h
    exact Or.inl ⟨q.trans h⟩
  · obtain ⟨h⟩ := h
    exact Or.inr ⟨q.trans h⟩

/-- Retaining one of the original cuts enlarges the supplied minimal parabolic. -/
lemma deletedFlag_le_rankTwoFlagFour (e : K ≃* PSL 4) (b : Basis 3)
    (i j : Fin 3) (hji : j ≠ i) :
    ambientFlagStabilizer e (deletedFlag (by decide) b i) ≤
      ambientFlagStabilizer e (rankTwoFlagFour b j) := by
  apply Subgroup.map_mono
  rw [deletedFlag_stabilizer, rankTwoFlagFour_stabilizer]
  apply Subgroup.comap_mono
  exact (cutStabilizer_le_iff _ _ _).mpr (by simpa using hji.symm)

/-- The transported rank-two overgroups generate the original embedded component. -/
lemma rankTwoFlagFour_generate (e : K ≃* PSL 4) (b : Basis 3)
    (i j : Fin 3) (hij : i ≠ j) :
    ambientFlagStabilizer e (rankTwoFlagFour b i) ⊔
      ambientFlagStabilizer e (rankTwoFlagFour b j) = K := by
  have hgen : flagStabilizer e (rankTwoFlagFour b i) ⊔
      flagStabilizer e (rankTwoFlagFour b j) = ⊤ := by
    apply Subgroup.map_injective (f := (linearModel e).toMonoidHom) (linearModel e).injective
    rw [Subgroup.map_sup, rankTwoFlagFour_stabilizer, rankTwoFlagFour_stabilizer,
      Subgroup.map_comap_eq_self_of_surjective (linearModel e).surjective,
      Subgroup.map_comap_eq_self_of_surjective (linearModel e).surjective,
      fourCuts_generate b i j hij,
      Subgroup.map_top_of_surjective _ (linearModel e).surjective]
  rw [ambientFlagStabilizer, ambientFlagStabilizer, ← Subgroup.map_sup, hgen]
  ext x
  simp

variable [Finite X] {P : Subgroup X}

/-- Every degree-four position with its contained Sylow has a nonempty generating family
of overgroups with intrinsic quotient S₃ × S₃ or PSL₃(2). -/
lemma rankTwoFour_generation (pos : BinaryGeometry.Position K P 4)
    (S : Sylow 2 K) (hSP : (S : Subgroup K) ≤ P.subgroupOf K) :
    (smallComponentOvergroups K P).Nonempty ∧ K ≤ sSup (smallComponentOvergroups K P) := by
  obtain ⟨b, i, _, hP⟩ := position_deletedFlag (by decide : 2 ≤ 3) pos S hSP
  have hmem (j : Fin 3) (hji : j ≠ i) :
      ambientFlagStabilizer pos.model (rankTwoFlagFour b j) ∈ smallComponentOvergroups K P := by
    refine ⟨?_, ambientFlagStabilizer_le _ _, rankTwoFlagFour_small _ _ _⟩
    exact hP.le.trans (deletedFlag_le_rankTwoFlagFour _ _ _ _ hji)
  have hpair : ∃ j k : Fin 3, j ≠ i ∧ k ≠ i ∧ j ≠ k := by
    fin_cases i
    · exact ⟨1, 2, by decide, by decide, by decide⟩
    · exact ⟨0, 2, by decide, by decide, by decide⟩
    · exact ⟨0, 1, by decide, by decide, by decide⟩
  obtain ⟨j, k, hji, hki, hjk⟩ := hpair
  refine ⟨⟨_, hmem j hji⟩, ?_⟩
  exact (rankTwoFlagFour_generate pos.model b j k hjk).ge.trans
    (sup_le (le_sSup (hmem j hji)) (le_sSup (hmem k hki)))

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.BinaryGeneration
