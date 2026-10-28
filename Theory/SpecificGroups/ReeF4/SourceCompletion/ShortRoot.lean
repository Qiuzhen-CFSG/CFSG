module
public import Theory.SpecificGroups.ReeF4.SourceCompletion.Centers
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Linear.FullLeviRepresentation.FixedFactors
import all Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.LongCommutators.RootCalculus
import all Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.Levi

/-!
# A perfect linear subgroup in the marked short-root centralizer

The two split roots of the fourth relative root block are orthogonal to
the two end nodes. The characteristic-two root exchanges give commutation
with the positive end curves. The end reflections fix both fourth-block
roots, so conjugation gives commutation with the negative end curves too.
Generation of the full fixed linear Levi by its signed blocks therefore
puts that Levi in the short-root centralizer. Its actual PSL₂ equivalence
gives a faithful embedding into the same full linear parabolic.

This is the short-root witness used in the three-divisor nonfusion argument
of Aschbacher–Smith F.4.35, printed p.292 (`refs/quasithin.pdf`), with the
root convention of GLS3 Table 2.4 (`refs/KGroup/GLS3/chapter2.tex`). The
internal imports reuse the existing split-root and reflection calculations;
the exports concern the unchanged native carrier and literal parabolic.
No simplicity of the ambient Ree group, completion or extension is assumed.
-/

public noncomputable section
namespace ReeF4.SourceCompletion
open Subgroup Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open LargeLocalSeeds Parabolics EvenInvolutionGeometry
open LocalBlockInput.PairRigidity LocalBlockInput.PairRigidity.FixedCollection
open LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
open BlockParameters.FieldRecovery
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open MatrixRelations.LongCommutators
open Binary.FixedGeometry
open ConverseParabolics.FullLeviRepresentation
private local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private theorem end_reflection_fixes (j : Fin 4) (hj : j = 0 ∨ j = 3)
    (i : Fin 24) (hi : i = 10 ∨ i = 11) :
    typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex j) (R i) = R i := by
  apply Subtype.ext
  rw [SeedGeneration.reflection_val, rval]
  rcases hj with rfl | rfl <;> rcases hi with rfl | rfl <;>
    ext k <;> fin_cases k <;> norm_num [V, typeF4CorootScale_simpleRoot,
      typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem short_curve_commute_end (m : ℕ) (i : Fin 24) (hi : i = 10 ∨ i = 11)
    (j : Fin 4) (hj : j = 0 ∨ j = 3) (p : Bool) (a b : CoefficientField m) :
    Commute (rootGeneratorInGroup m (R i) a)
      (rootGeneratorInGroup m (signedRoot p (typeF4SimpleRootIndex j)) b) := by
  have hpos : Commute (rootGeneratorInGroup m (R i) a)
      (rootGeneratorInGroup m (typeF4SimpleRootIndex j) b) := by
    apply curve_commute_nonneg m _ _ (rpos i)
      (isSimpleBlockRoot_simple .linear j (by
        rcases hj with rfl | rfl <;> simp [leviNodes])).2
    rw [rval, typeF4SimpleRootIndex_val]
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      norm_num [V,typeF4SimpleRoot,dot,Fin.sum_univ_four,
        Matrix.cons_val_two,Matrix.cons_val_three]
  cases p
  · have hc := hpos.map (MulAut.conj (simpleWord m [j])).toMonoidHom
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom,
      simpleWord_conj, reflectWord] at hc
    rw [end_reflection_fixes j hj i hi] at hc
    exact hc
  · exact hpos

private theorem short_word_commute_linear (m : ℕ) (t u : CoefficientField m) (p : Bool) :
    Commute (rootWord m 3 t) (linearElement (canonicalLocalBlockInput m) p u).val := by
  have hw : rootWord m 3 t = rootGeneratorInGroup m (R 10) t *
      rootGeneratorInGroup m (R 11) (rootFieldEnd m (longRoot 3) t) := by
    simp only [rootWord, if_neg (by decide : ¬ (3 : Fin 8).val % 2 = 0),mul_one]
    rfl
  rw [hw]
  have hc (j : Fin 4) (hj : j = 0 ∨ j = 3) (b : CoefficientField m) :
      Commute (rootGeneratorInGroup m (R 10) t *
        rootGeneratorInGroup m (R 11) (rootFieldEnd m (longRoot 3) t))
        (rootGeneratorInGroup m (signedRoot p (typeF4SimpleRootIndex j)) b) :=
    (short_curve_commute_end m 10 (.inl rfl) j hj p t b).mul_left
      (short_curve_commute_end m 11 (.inr rfl) j hj p _ b)
  cases p
  · rw [linearElement_negative]
    exact (hc 0 (.inl rfl) u).mul_right (hc 3 (.inr rfl) _)
  · rw [linearElement_positive]
    exact (hc 0 (.inl rfl) u).mul_right (hc 3 (.inr rfl) _)

/-- The marked short-root curve centralizes the whole fixed linear Levi. -/
theorem short_root_commute_linear_levi {m : ℕ} (hm : 0 < m) (t : CoefficientField m)
    (x : fixedLevi (canonicalLocalBlockInput m) .linear) :
    Commute (shortRootElement m t) (seedLeviHom m x) := by
  let d := canonicalLocalBlockInput m
  have hb (p : Bool) : simpleBlock d .linear p ≤
      (centralizer ({rootWord m 3 t} : Set (SplitGroup m))).comap d.fixedGroup.subtype := by
    intro y hy
    obtain ⟨u,rfl⟩ := linearElement_surjective d p hy
    exact mem_centralizer_singleton_iff.mpr (short_word_commute_linear m t u p).symm.eq
  have hc := (sup_le (hb true) (hb false))
    (fixedLevi_linear_le_signed_of_longRootMap d (linearLongRootMap m hm) x.property)
  apply Commute.of_map (toSplitGroup_injective m)
  rw [shortRootElement_coe]
  change Commute (rootWord m 3 t) (toSplitGroup m (d.modelEquiv x.val))
  rw [toSplitGroup_apply,LocalBlockInput.modelEquiv_coe]
  exact (mem_centralizer_singleton_iff.mp hc).symm

/-- The actual PSL₂ subgroup embeds in the short-root centralizer inside the full linear parabolic. -/
theorem short_root_linear_centralizer_embedding {m : ℕ} (hm : 0 < m)
    (t : CoefficientField m) :
    ∃ f : LinearQuotient m →* parabolic m .linear,
      Function.Injective f ∧ ∀ x, Commute (f x).val (shortRootElement m t) := by
  let e := LinearProjection.fixedLeviEquivPSL hm (canonicalLocalBlockInput m)
  let f := (seedLeviHom m).comp e.symm.toMonoidHom
  have hf : ∀ x, f x ∈ parabolic m .linear := fun x =>
    SectionGeometry.LinearRadical.fullLevi_le_parabolic m
      (seedLeviHom_le_fullLevi m ⟨e.symm x,rfl⟩)
  refine ⟨f.codRestrict _ hf, ?_, ?_⟩
  · exact (MonoidHom.injective_codRestrict _ _ _).mpr
      ((seedLeviHom_injective m).comp e.symm.injective)
  · intro x
    exact (short_root_commute_linear_levi hm t (e.symm x)).symm

end ReeF4.SourceCompletion
