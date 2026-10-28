module
public import Theory.Representation.HermitianTensorThree.Involutions
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianCoordinates
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuRankOneSetup
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.SourceCompleteBound

/-!
# Initial Hermitian weak-closure bounds on the original chosen orbit

The literal automizer embedding transfers the inner/outer involution
codimensions 4n and 3n. The component supplies an actual root involution,
so the minimum is attained and m is either 3n or 4n. In particular m > 2,
including n = 1. The genuine E.6.1 setup and the completed E.6.3 theorem
then give m ≤ r and s = m, with no remaining Held-cover or model premise.

If r < 4n, a minimizing automizer involution is necessarily outside the
marked component image. The final tensor application constructs its
coordinates by descent from the original inflated action and keeps the
original Sylow subgroup throughout.

This proves the Hermitian instance of the initial 7.3.2 bounds. The stronger
7.4.1 bound r ≥ 4n, the 7.5.6 bound n ≤ w, selection and k ≤ n, and the
8.2.3–13 exclusion remain with qt-d-1222-nonmathieu-hermitian-exclusion.
In particular these results do not assert the complete Hermitian exclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.4.4(2,6),
E.6.3, Table 7.2.1 and 7.3.2, printed pp.381,245,698
(refs/quasithin.pdf).
-/

public noncomputable section
open scoped Classical
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
variable (n : ℕ) [NeZero n]
  (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
    (overgroupAction n (binaryImage n)))

/-- Exact involution codimensions on the original full automizer. -/
theorem sourceOrbit_hermitian_involution_fixedCodim
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (a : Automizer D.sourceOrbit) (ha : orderOf a = 2) :
    fixedCodim (automizerRepresentation D.sourceOrbit) (zpowers a) =
      if coordinateHom (automizerRepresentation D.sourceOrbit) n
        (D.hermitianOrbitCoordinates n d) a ∈ binaryImage n then 4*n else 3*n := by
  classical
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h
  have hc := fixedCodim_map_equivariant (automizerRepresentation D.sourceOrbit)
    (overgroupAction n (binaryNormalizer n)) j (D.hermitianOrbitCoordinates n d) he (zpowers a)
  rw [MonoidHom.map_zpowers] at hc
  rw [hc,Involutions.overgroup_involution_fixedCodim n (binaryNormalizer n) le_rfl
    (j a) ((orderOf_injective j hj a).trans ha)]
  have hjc : (j a).val = coordinateHom (automizerRepresentation D.sourceOrbit) n
      (D.hermitianOrbitCoordinates n d) a := by
    apply LinearEquiv.ext
    intro v
    rw [coordinateHom_apply]
    exact (congrArg (j a).val ((D.hermitianOrbitCoordinates n d).apply_symm_apply v)).symm.trans
      (he a ((D.hermitianOrbitCoordinates n d).symm v)).symm
  rw [hjc]

include d in
/-- The local minimum is 3n or 4n; the original component supplies attainment. -/
theorem sourceOrbit_hermitian_localM
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    3*n ≤ localM D.sourceOrbit ∧
      (localM D.sourceOrbit = 3*n ∨ localM D.sourceOrbit = 4*n) := by
  have hm : 3*n ≤ localM D.sourceOrbit := by
    apply le_csInf ⟨_, Set.mem_insert _ _⟩
    rintro k (rfl | ⟨a,ha,rfl⟩)
    · rw [(D.hermitianOrbitCoordinates n d).finrank_eq,finrank_binary]
      omega
    · rw [D.sourceOrbit_hermitian_involution_fixedCodim n d h a ha]
      split_ifs <;> omega
  obtain ⟨j,hj,he,hcomp⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h
  obtain ⟨l,hl⟩ := (d.groupEquiv.surjective.comp D.orbitComponentHom_surjective)
    (⟨binaryActionHom n (root n), ⟨root n,rfl⟩⟩ : binaryImage n)
  let a := D.hermitianComponentAutomizer l
  have hjroot : (j a).val = binaryActionHom n (root n) := by
    rw [hcomp]
    exact congrArg Subtype.val hl
  have ha : orderOf a = 2 := by
    rw [← orderOf_injective j hj a,
      ← orderOf_injective (binaryNormalizer n).subtype Subtype.val_injective (j a)]
    change orderOf (j a).val = 2
    rw [hjroot]
    exact Involutions.orderOf_root_image n
  obtain ⟨b,hb,hbm⟩ := moduleM_attained (automizerRepresentation D.sourceOrbit) ⟨a,ha⟩
  have hd := D.sourceOrbit_hermitian_involution_fixedCodim n d h b hb
  change _ = localM D.sourceOrbit at hbm
  rw [hbm] at hd
  refine ⟨hm, ?_⟩
  split_ifs at hd
  · exact Or.inr hd
  · exact Or.inl hd

include d in
/-- Source 7.3.2 for the original orbit, with all E.6.3 premises discharged. -/
theorem sourceOrbit_hermitian_initial_parameters
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    ((3*n : ℕ) : ℕ∞) ≤ globalR D.sourceOrbit ∧
      (localM D.sourceOrbit : ℕ∞) ≤ globalR D.sourceOrbit ∧
      globalS D.sourceOrbit = (localM D.sourceOrbit : ℕ∞) ∧
      2 < globalS D.sourceOrbit ∧
      (localM D.sourceOrbit = 3*n ∨ localM D.sourceOrbit = 4*n) := by
  obtain ⟨hm,hcases⟩ := D.sourceOrbit_hermitian_localM n d h.toHypothesis1221
  have hn := NeZero.pos n
  obtain ⟨hr,hS,hpos⟩ := ChapterE.Section06.FrobeniusReduction.lower_bound_knownSimple
    (D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon) (by omega)
  exact ⟨(ENat.natCast_le_natCast.mpr hm).trans hr,hr,hS,hpos,hcases⟩

/-- Failure of the stronger r-bound has an actual outer involution witness. -/
theorem sourceOrbit_hermitian_outer_involution_of_small_globalR
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hr : globalR D.sourceOrbit < ((4*n : ℕ) : ℕ∞)) :
    localM D.sourceOrbit = 3*n ∧
      ∃ a : Automizer D.sourceOrbit, orderOf a = 2 ∧
        coordinateHom (automizerRepresentation D.sourceOrbit) n
          (D.hermitianOrbitCoordinates n d) a ∉ binaryImage n ∧
        fixedCodim (automizerRepresentation D.sourceOrbit) (zpowers a) = 3*n := by
  obtain ⟨_,hmR,_,_,hcases⟩ := D.sourceOrbit_hermitian_initial_parameters n d h hmany hV hnon
  have hm : localM D.sourceOrbit = 3*n := hcases.resolve_right (fun he => by
    rw [he] at hmR
    exact (not_lt_of_ge hmR) hr)
  refine ⟨hm,?_⟩
  have hmem : localM D.sourceOrbit ∈ insert (Module.finrank (ZMod 2) (Additive D.sourceOrbit))
      {k | ∃ a : Automizer D.sourceOrbit, orderOf a = 2 ∧
        fixedCodim (automizerRepresentation D.sourceOrbit) (zpowers a) = k} :=
    csInf_mem ⟨_,Set.mem_insert _ _⟩
  have hn := NeZero.pos n
  rcases hmem with hdim | ⟨a,ha,hcod⟩
  · rw [(D.hermitianOrbitCoordinates n d).finrank_eq,finrank_binary,hm] at hdim
    omega
  · rw [hm] at hcod
    refine ⟨a,ha,?_,hcod⟩
    intro hinner
    have hc := D.sourceOrbit_hermitian_involution_fixedCodim n d h.toHypothesis1221 a ha
    rw [if_pos hinner,hcod] at hc
    omega

/-- The tensor input yields the initial global bounds on the original orbit. -/
theorem sourceOrbit_hermitian_tensor_initial_parameters
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n) :
    ((3*n : ℕ) : ℕ∞) ≤ globalR D.sourceOrbit ∧
      (localM D.sourceOrbit : ℕ∞) ≤ globalR D.sourceOrbit ∧
      globalS D.sourceOrbit = (localM D.sourceOrbit : ℕ∞) ∧
      2 < globalS D.sourceOrbit ∧
      (localM D.sourceOrbit = 3*n ∨ localM D.sourceOrbit = 4*n) := by
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  exact D.sourceOrbit_hermitian_initial_parameters n d h hmany hV hnon

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
