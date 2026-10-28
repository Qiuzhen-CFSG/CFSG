module
public import Theory.SpecificGroups.ReeF4.SourceCompletion.ShortCentralizerGeometry
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.Replacement.Centralizers.Geometry
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.LinearParabolic
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.WeylGeometry.Orbits
import all Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.LongCommutators.RootCalculus
import all Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.Levi

/-!
# The natural long-root plane in the Ree short centralizer

The replacement plane is an actual elementary abelian 2-subgroup. Root
commutators show that the unipotent radical and relative Weyl element
normalize it, while the fixed linear Levi acts faithfully on its two field
coordinates. Every nonidentity vector is a long-root involution, and the
induced image of the actual PSL₂ quotient is nonsolvable for all positive
parameters. These are the natural-module facts used in the F.4.42
short-centralizer argument.

Source: Aschbacher--Smith, Lemma F.4.42, printed pp.295--296
(`refs/quasithin.pdf`); root conventions follow GLS3 Table 2.4.
-/
public noncomputable section
open Subgroup Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.SourceCompletion.ShortCentralizerGeometry
open LargeLocalSeeds Parabolics EvenInvolutionGeometry ElementaryTwoBound
open ElementaryTwoBound.Replacement ElementaryTwoBound.Replacement.CentralizerGeometry
open NormalizedRootCentralizers.CenterExponent
open Parabolics.RadicalCoordinates.FixedCoordinates
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open MatrixRelations.LongCommutators
open LocalBlockInput.PairRigidity FixedCollection SeedGeneration
open Parabolics.Binary.FixedGeometry

private theorem end_two_four :
    wordAction [0,3] (highRoot 2) = highRoot 4 ∧
    wordAction [0,3] (mixedRoot 2) = mixedRoot 4 := by
  change wordAction [0,3] (R 9) = R 15 ∧ wordAction [0,3] (R 8) = R 14
  constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
    norm_num [wordAction, Equiv.Perm.mul_apply, SeedGeneration.reflection_val,
      rval, MatrixRelations.LongCommutators.V, typeF4CorootScale_simpleRoot,
      typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem end_four_two :
    wordAction [0,3] (highRoot 4) = highRoot 2 ∧
    wordAction [0,3] (mixedRoot 4) = mixedRoot 2 := by
  change wordAction [0,3] (R 15) = R 9 ∧ wordAction [0,3] (R 14) = R 8
  constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
    norm_num [wordAction, Equiv.Perm.mul_apply, SeedGeneration.reflection_val,
      rval, MatrixRelations.LongCommutators.V, typeF4CorootScale_simpleRoot,
      typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem weyl_conjugate_central (m : ℕ) (i j : Fin 8)
    (hh : wordAction [0,3] (highRoot i) = highRoot j)
    (hl : wordAction [0,3] (mixedRoot i) = mixedRoot j) (a : CoefficientField m) :
    weylLift m .linear * centralElement m i a * (weylLift m .linear)⁻¹ =
      centralElement m j a := by
  apply toSplitGroup_injective m
  simp only [map_mul, map_inv, centralElement_coe, toSplitGroup_weylLift]
  have hf (k : Fin 8) : rootFieldEnd m (longRoot k) = halfFrobenius m := by
    simp only [rootFieldEnd, if_pos (MatrixRelations.longRoot_isLong k), halfFrobenius]
  simp only [centralWord, hf]
  change simpleWord m [0,3] * _ * (simpleWord m [0,3])⁻¹ = _
  calc
    _ = (simpleWord m [0,3] * rootGeneratorInGroup m (highRoot i) a *
        (simpleWord m [0,3])⁻¹) *
      (simpleWord m [0,3] * rootGeneratorInGroup m (mixedRoot i) (halfFrobenius m a) *
        (simpleWord m [0,3])⁻¹) := by group
    _ = _ := by rw [simpleWord_conj_root, simpleWord_conj_root, hh, hl]

theorem weyl_conjugate_plane (m : ℕ) (a b : CoefficientField m) :
    weylLift m .linear * (centralElement m 4 b * centralElement m 2 a) *
      (weylLift m .linear)⁻¹ = centralElement m 4 a * centralElement m 2 b := by
  calc
    _ = (weylLift m .linear * centralElement m 4 b * (weylLift m .linear)⁻¹) *
      (weylLift m .linear * centralElement m 2 a * (weylLift m .linear)⁻¹) := by group
    _ = centralElement m 2 b * centralElement m 4 a := by
      rw [weyl_conjugate_central m 4 2 end_four_two.1 end_four_two.2,
        weyl_conjugate_central m 2 4 end_two_four.1 end_two_four.2]
    _ = _ := (centralElement_commute m b a).eq

private theorem central_eighth (m : ℕ) (a u : CoefficientField m) :
    centralElement m 2 a * mainElement m 7 u =
      mainElement m 7 u * centralElement m 2 a * centralElement m 4 (a*u) := by
  apply toSplitGroup_injective m
  simpa only [map_mul, mainElement_coe, centralElement_coe] using
    ReplacementCentralizerRoots.central_eighth m a u

private theorem central_four_eighth (m : ℕ) (b u : CoefficientField m) :
    Commute (centralElement m 4 b) (mainElement m 7 u) := by
  apply toSplitGroup_injective m
  simpa only [map_mul, mainElement_coe, centralElement_coe] using
    (ReplacementCentralizerRoots.main_central_4 m 7 u b).symm.eq

theorem eighth_conjugate_plane (m : ℕ) (u a b : CoefficientField m) :
    mainElement m 7 u * (centralElement m 4 b * centralElement m 2 a) *
      (mainElement m 7 u)⁻¹ = centralElement m 4 (b+a*u) * centralElement m 2 a := by
  have hs : centralElement m 4 (a*u) * centralElement m 4 (a*u) = 1 := by
    rw [← centralElement_add m 4 (by decide), CharTwo.add_self_eq_zero, centralElement_zero]
  have hrel := central_eighth m a u
  have htwo : mainElement m 7 u * centralElement m 2 a * (mainElement m 7 u)⁻¹ =
      centralElement m 4 (a*u) * centralElement m 2 a := by
    apply mul_right_cancel (b := mainElement m 7 u)
    calc
      _ = mainElement m 7 u * centralElement m 2 a := by group
      _ = (mainElement m 7 u * centralElement m 2 a * centralElement m 4 (a*u)) *
          centralElement m 4 (a*u) := by rw [mul_assoc, hs, mul_one]
      _ = (centralElement m 2 a * mainElement m 7 u) * centralElement m 4 (a*u) := by rw [hrel]
      _ = (centralElement m 4 (a*u) * centralElement m 2 a) * mainElement m 7 u := by
        rw [mul_assoc, (central_four_eighth m (a*u) u).symm.eq,
          ← mul_assoc, ← (centralElement_commute m a (a*u)).eq]
  calc
    _ = centralElement m 4 b *
      (mainElement m 7 u * centralElement m 2 a * (mainElement m 7 u)⁻¹) := by
        rw [← mul_assoc, ← (central_four_eighth m b u).eq]; group
    _ = _ := by rw [htwo, ← mul_assoc, ← centralElement_add m 4 (by decide)]

theorem unipotent_normalizes_plane (m : ℕ) :
    unipotent m ≤ normalizer (Replacement.V m : Set (Model m)) := by
  rw [le_normalizer_iff]
  intro x hx v hv
  obtain ⟨u,c,rfl⟩ := exists_last_root_mul_C m x hx
  obtain ⟨a,b,rfl⟩ := (mem_V_iff m v).mp hv
  have hc : Commute (c : Model m) (centralElement m 4 b * centralElement m 2 a) :=
    (show Commute (centralElement m 4 b * centralElement m 2 a) (c : Model m) from
      C_centralizes_V m c.property _ hv).symm
  have he : (mainElement m 7 u * (c : Model m)) *
      (centralElement m 4 b * centralElement m 2 a) * (mainElement m 7 u * c)⁻¹ =
      mainElement m 7 u * (centralElement m 4 b * centralElement m 2 a) *
        (mainElement m 7 u)⁻¹ := by
    calc
      _ = mainElement m 7 u * ((c : Model m) *
          (centralElement m 4 b * centralElement m 2 a)) *
          (c : Model m)⁻¹ * (mainElement m 7 u)⁻¹ := by group
      _ = _ := by rw [hc.eq]; group
  rw [he, eighth_conjugate_plane]
  exact (mem_V_iff m _).mpr ⟨a,b+a*u,rfl⟩

theorem weyl_normalizes_plane (m : ℕ) :
    weylLift m .linear ∈ normalizer (Replacement.V m : Set (Model m)) := by
  apply mem_normalizer_iff.mpr
  intro v
  constructor
  · intro hv
    obtain ⟨a,b,rfl⟩ := (mem_V_iff m v).mp hv
    rw [weyl_conjugate_plane]
    exact (mem_V_iff m _).mpr ⟨b,a,rfl⟩
  · intro hv
    obtain ⟨a,b,hab⟩ := (mem_V_iff m _).mp hv
    have he := weyl_conjugate_plane m b a
    rw [hab] at he
    have hi : Function.Injective (fun x : Model m =>
        weylLift m .linear * x * (weylLift m .linear)⁻¹) := (MulAut.conj _).injective
    have he' := hi he
    rw [← he']
    exact (mem_V_iff m _).mpr ⟨b,a,rfl⟩

theorem seed_normalizes_plane (m : ℕ) (hm : 0 < m) :
    seed m .linear ≤ normalizer (Replacement.V m : Set (Model m)) := by
  rw [SectionGeometry.BNPair.seed_linear_eq_unipotent_sup_weyl m hm]
  exact sup_le (unipotent_normalizes_plane m) (zpowers_le.mpr (weyl_normalizes_plane m))

/-- Every nonidentity element of the literal root plane is a long-root involution. -/
theorem plane_nonidentity_long (m : ℕ) {v : Model m} (hv : v ∈ Replacement.V m) (hne : v ≠ 1) :
    IsLongRootInvolution v := by
  obtain ⟨a,b,rfl⟩ := (mem_V_iff m v).mp hv
  by_cases ha : a = 0
  · subst a
    simp only [centralElement_zero, mul_one] at hne ⊢
    have hb : b ≠ 0 := by
      intro hb
      exact hne (hb ▸ centralElement_zero m 4)
    exact ⟨b,hb,IsConj.refl _⟩
  · have he := eighth_conjugate_plane m (b/a) a b
    have hba : b+a*(b/a) = 0 := by
      rw [mul_div_cancel₀ b ha, CharTwo.add_self_eq_zero]
    rw [hba,centralElement_zero,one_mul] at he
    have hw := weyl_conjugate_plane m a 0
    simp only [centralElement_zero,mul_one,one_mul] at hw
    refine ⟨a,ha,?_⟩
    exact (isConj_iff.mpr ⟨mainElement m 7 (b/a),he⟩ |>.trans
      (isConj_iff.mpr ⟨weylLift m .linear,hw⟩)).symm

/-- The native short-root curve centralizes the literal long-root plane. -/
theorem shortRoot_centralizes_plane (m : ℕ) (t : CoefficientField m) :
    Replacement.V m ≤ centralizer ({shortRootElement m t} : Set (Model m)) := by
  have h4 (b : CoefficientField m) :
      Commute (shortRootElement m t) (centralElement m 4 b) := by
    apply toSplitGroup_injective m
    simpa only [map_mul, shortRootElement_coe, centralElement_coe] using
      (ReplacementCentralizerRoots.main_central_4 m 3 t b).eq
  have h2 (a : CoefficientField m) :
      Commute (shortRootElement m t) (centralElement m 2 a) := by
    apply toSplitGroup_injective m
    simpa only [map_mul, shortRootElement_coe, centralElement_coe] using
      (ReplacementCentralizerRoots.main_central_2 m 3 (by decide) t a).eq
  intro x hx
  obtain ⟨a,b,rfl⟩ := (mem_V_iff m x).mp hx
  exact mem_centralizer_singleton_iff.mpr ((h4 b).mul_right (h2 a)).symm.eq

/-- The plane is nontrivial at every parameter, including the binary model. -/
theorem plane_ne_bot (m : ℕ) : Replacement.V m ≠ ⊥ := by
  intro h
  have hx : longRootElement m 1 ∈ Replacement.V m := by
    exact (mem_V_iff m _).mpr ⟨0,1,by simp; rfl⟩
  rw [h,mem_bot] at hx
  exact (longRootElement_eq_one_iff m 1).not.mpr one_ne_zero hx

open ConverseParabolics.FullLeviRepresentation

/-- The actual fixed end-node Levi normalizes the literal two-coordinate plane. -/
theorem fixedLevi_normalizes_plane (m : ℕ) (hm : 0 < m)
    (x : fixedLevi (canonicalLocalBlockInput m) .linear) :
    seedLeviHom m x ∈ normalizer (Replacement.V m : Set (Model m)) := by
  apply seed_normalizes_plane m hm
  change toSplitGroup m ((canonicalLocalBlockInput m).modelEquiv x.val) ∈ splitSeed m .linear
  rw [toSplitGroup_apply,LocalBlockInput.modelEquiv_coe]
  exact fixedLevi_le_seed (canonicalLocalBlockInput m) .linear x.property

/-- Conjugation by the actual fixed Levi on the actual long-root plane. -/
def leviPlaneAction (m : ℕ) (hm : 0 < m) :
    fixedLevi (canonicalLocalBlockInput m) .linear →* MulAut (Replacement.V m) :=
  (Replacement.V m).normalizerMonoidHom.comp
    ((seedLeviHom m).codRestrict _ (fixedLevi_normalizes_plane m hm))

/-- The action is nontrivial: the relative Weyl word swaps two independent coordinates. -/
theorem leviPlaneAction_ne_one (m : ℕ) (hm : 0 < m) : leviPlaneAction m hm ≠ 1 := by
  intro he
  let d := canonicalLocalBlockInput m
  let w : fixedLevi d .linear := ⟨relativeWeyl d .linear,relativeWeyl_mem_fixedLevi d .linear⟩
  let v : Replacement.V m := ⟨centralElement m 4 1,(mem_V_iff m _).mpr ⟨0,1,by simp⟩⟩
  have hh := congrArg (fun f => (f w v : Model m)) he
  have hw : seedLeviHom m w = weylLift m .linear :=
    SectionGeometry.BNPair.modelEquiv_relativeWeyl d .linear
  simp only [leviPlaneAction,MonoidHom.comp_apply,normalizerMonoidHom_apply_apply_coe] at hh
  change seedLeviHom m w * centralElement m 4 1 * (seedLeviHom m w)⁻¹ =
    centralElement m 4 1 at hh
  rw [hw] at hh
  have hs := weyl_conjugate_plane m 0 1
  simp only [centralElement_zero,mul_one,one_mul] at hs
  rw [hs] at hh
  have hp : planeHom m (Multiplicative.ofAdd (1,0)) =
      planeHom m (Multiplicative.ofAdd (0,1)) := by
    change centralElement m 4 0 * centralElement m 2 1 =
      centralElement m 4 1 * centralElement m 2 0
    simpa only [centralElement_zero,mul_one,one_mul] using hh
  have hc := congrArg (fun x : Multiplicative (CoefficientField m × CoefficientField m) =>
    x.toAdd.1) (planeHom_injective m hp)
  exact one_ne_zero hc

/-- Simplicity of PSL₂ upgrades its nontrivial literal action to a faithful action. -/
theorem leviPlaneAction_injective (m : ℕ) (hm : 0 < m) :
    Function.Injective (leviPlaneAction m hm) := by
  let := linearQuotient_simple m hm
  let := (LinearProjection.fixedLeviEquivPSL hm (canonicalLocalBlockInput m)).isSimpleGroup
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases (leviPlaneAction m hm).normal_ker.eq_bot_or_eq_top with h | h
  · exact h
  · exact (leviPlaneAction_ne_one m hm (MonoidHom.ker_eq_top_iff.mp h)).elim

/-- PSL₂(q) acts faithfully by conjugation on the literal long-root plane. -/
def linearPlaneAction (m : ℕ) (hm : 0 < m) : LinearQuotient m →* MulAut (Replacement.V m) :=
  (leviPlaneAction m hm).comp
    (LinearProjection.fixedLeviEquivPSL hm (canonicalLocalBlockInput m)).symm.toMonoidHom

theorem linearPlaneAction_injective (m : ℕ) (hm : 0 < m) :
    Function.Injective (linearPlaneAction m hm) :=
  (leviPlaneAction_injective m hm).comp
    (LinearProjection.fixedLeviEquivPSL hm (canonicalLocalBlockInput m)).symm.injective

/-- The induced image is nonsolvable for all q ≥ 8. -/
theorem linearPlaneAction_range_not_solvable (m : ℕ) (hm : 0 < m) :
    ¬ Group.IsSolvable (linearPlaneAction m hm).range := by
  intro hs
  let := hs
  let := linearQuotient_simple m hm
  let := linearQuotient_perfect m hm
  exact Group.IsPerfect.not_isSolvable (LinearQuotient m)
    (Group.isSolvable_of_isSolvable_injective
      (MonoidHom.rangeRestrict_injective_iff.mpr (linearPlaneAction_injective m hm)))

end ReeF4.SourceCompletion.ShortCentralizerGeometry
