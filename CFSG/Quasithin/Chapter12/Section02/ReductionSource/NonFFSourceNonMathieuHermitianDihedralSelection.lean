module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceDihedralSelection
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourMovement

/-!
# Odd-component and involution-image selection on the chosen Hermitian orbit

The literal E.2.8 quotient image of the chosen orbit supplies a parameter-one
pair when it has order two. The odd normal-component catalogue rows supply
the same pair through their actual marked quotient models. Solvability of H
is unnecessary. The tensor coordinates force field four and retain the
original actor, fixed subgroup, relative normality and residual identities.

Thus every higher-field H-star subgroup has quotient image of order at least
four and has none of the odd normal-component models. The remaining binary
selection branches and the field-four normalizer/centralizer contradiction
through 8.2.13 are still obligations of the source assembly.
Source: Aschbacher–Smith E.2.7–9, 8.2.2–5 and 8.2.7,
printed pp.218–222,714–718 (1 March 2004 manuscript, refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter8.Section02.Offenders.Parabolic.Construction Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
  (D : ChosenModule T L V)

/-- The original order-two image or odd normal-component model constructs
an actual selected pair; no solvability or family witness is assumed. -/
theorem sourceOrbit_hermitian_selected_one_of_dihedral_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hc : Nat.card (starImage (normalizer (L : Set G)) H D.sourceOrbit) = 2 ∨
      OddNormalComponent H (T : Subgroup G) (normalizer (L : Set G))) :
    ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S := by
  obtain ⟨h28,hchar⟩ := D.sourceOrbit_hermitian_hstar_setup h hmany hV hnon hs hrow hH
  exact exists_selected_one_of_dihedral_source h28
    (generalizedFitting_eq_pCore_of_selfCentralizing 2 hchar) hc
    (D.sourceOrbit_restricted_quadraticRatio_gt_one h.toHypothesis1221 hnon _)
    (D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).ti
    (D.sourceOrbit_normalizer_le h.toHypothesis1221)

/-- Dihedral source selection on the literal tensor, retaining its original
actor, intersection, Sylow and residuals through the field-four reduction. -/
theorem sourceOrbit_hermitian_tensor_dihedral_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hc : Nat.card (starImage (normalizer (L : Set G)) H D.sourceOrbit) = 2 ∨
      OddNormalComponent H (T : Subgroup G) (normalizer (L : Set G)))
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n) :
    ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
      let A := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2
      let U := D.sourceOrbit ⊓ centralizer (A : Set G)
      n = 1 ∧ B.degree = 2 ∧ A ≤ T ∧
      rank (inducedAutomizer D.sourceOrbit A) = 4 ∧ rank U = 4 ∧
      U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      (U.subgroupOf T).Normal ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      I ≤ centralizer (U : Set G) ∧
      I ⊔ (T : Subgroup G) = H ∧ H ≤ normalizer (U : Set G) ∧
      (pResidual 2 H).map H.subtype ≤ centralizer (U : Set G) ∧
      I.pCoreIn 2 = ⁅I.pCoreIn 2,(pResidual 2 I).map I.subtype⁆ ⊔ U ∧
      I.pCoreIn 2 ⊓ centralizer ((pResidual 2 I).map I.subtype : Set G) = U := by
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  have hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs := by
    refine ⟨B,C,⟨eQ⟩,?_⟩
    dsimp only
    rw [hdegree]
    exact ⟨NeZero.pos n,hfield,d.linearEquiv.finrank_eq.trans (finrank_binary n),hmodel⟩
  obtain ⟨I,i,S,s⟩ := D.sourceOrbit_hermitian_selected_one_of_dihedral_source h hmany hV hnon hs hrow hH hc
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h.toHypothesis1221
  obtain ⟨hn,hAT,ha,hu,hU,hUT,hTN,hIC,_,_⟩ := selected_one_fixed_subgroup s
    D.sourceOrbit_weakClosure_setup n (D.hermitianOrbitCoordinates n d) j hj he
  have hnorm := selected_one_hstar_normalizer s hH
    D.sourceOrbit_weakClosure_setup n (D.hermitianOrbitCoordinates n d) j hj he
  have hmove := D.sourceOrbit_hermitian_selected_one_residual_core h.toHypothesis1221 s n d
  exact ⟨I,i,S,s,hn,by omega,hAT,ha,hu,hU,hUT,hTN,hIC,
    selected_generates_hstar s hH,hnorm.1,hnorm.2,hmove⟩

/-- Higher-field original H-star subgroups have noncyclic quotient images
and no odd normal-component row. All additional source witnesses are built
inside the proof. The excluded odd rows include the odd PSL3 TI case. -/
theorem sourceOrbit_hermitian_tensor_hstar_odd_rows_excluded
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n)
    (hn : 1 < n) :
    4 ≤ Nat.card (starImage (normalizer (L : Set G)) H D.sourceOrbit) ∧
      ¬ OddNormalComponent H (T : Subgroup G) (normalizer (L : Set G)) := by
  have hnot : ¬ (Nat.card (starImage (normalizer (L : Set G)) H D.sourceOrbit) = 2 ∨
      OddNormalComponent H (T : Subgroup G) (normalizer (L : Set G))) := by
    intro hc
    obtain ⟨I,i,S,s,hn',_⟩ := D.sourceOrbit_hermitian_tensor_dihedral_source
      h hmany hV hs hnon hH hc B C eQ n hdegree hfield hmodel
    omega
  refine ⟨?_,fun hc => hnot (Or.inr hc)⟩
  let W := starImage (normalizer (L : Set G)) H D.sourceOrbit
  have hVH : D.sourceOrbit ≤ H := D.sourceOrbit_weakClosure_setup.le_sylow.trans hH.1.1.2
  let : IsElementaryAbelian 2 (D.sourceOrbit.subgroupOf H) :=
    IsElementaryAbelian.subgroupOf hVH
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  obtain ⟨r,hr⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_card_eq
  have hne : W ≠ ⊥ := by
    intro he
    obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
      hs B C n hdegree hfield hmodel
    have hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs := by
      refine ⟨B,C,⟨eQ⟩,?_⟩
      dsimp only
      rw [hdegree]
      exact ⟨NeZero.pos n,hfield,d.linearEquiv.finrank_eq.trans (finrank_binary n),hmodel⟩
    obtain ⟨h28,_⟩ := D.sourceOrbit_hermitian_hstar_setup h hmany hV hnon hs hrow hH
    have hle : D.sourceOrbit.subgroupOf H ≤ localCore (normalizer (L : Set G)) H := by
      simpa only [QuotientGroup.ker_mk'] using
        (map_eq_bot_iff (D.sourceOrbit.subgroupOf H)).mp he
    apply h28.outside_core
    have hm := map_mono (f := H.subtype) hle
    rwa [map_subgroupOf_eq_of_le hVH] at hm
  have hlarge := (one_lt_card_iff_ne_bot W).mpr hne
  have hr2 : 2 ≤ r := by
    by_contra! hc
    interval_cases r
    · simp only [pow_zero] at hr
      omega
    · exact hnot (Or.inl (by simpa only [pow_one] using hr))
  change 4 ≤ Nat.card W
  rw [hr]
  exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hr2

/-- The higher-field tensor supplies a generating component in each original
H-star subgroup. Every normal such selected component has a genuine binary
model in the original full-core quotient; the exchanged branch remains explicit. -/
theorem sourceOrbit_hermitian_tensor_higher_hstar_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n)
    (hn : 1 < n) :
    ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      K ⊔ (T : Subgroup G).subgroupOf H = ⊤ ∧
      (K.Normal →
        let X := K.map (QuotientGroup.mk' (localCore (normalizer (L : Set G)) H))
        ClassificationModels.IsBenderModel X ∨
        (∃ f : ℕ, 1 ≤ f ∧ ClassicalGroup.IsPSL X 3 (2^f)) ∨
        (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSp X 2 (2^f)) ∨
        Nonempty (X ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))) := by
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  have hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs := by
    refine ⟨B,C,⟨eQ⟩,?_⟩
    dsimp only
    rw [hdegree]
    exact ⟨NeZero.pos n,hfield,d.linearEquiv.finrank_eq.trans (finrank_binary n),hmodel⟩
  obtain ⟨h28,hchar⟩ := D.sourceOrbit_hermitian_hstar_setup h hmany hV hnon hs hrow hH
  rcases exists_selected_one_or_remaining_component h28
    (generalizedFitting_eq_pCore_of_selfCentralizing 2 hchar)
    (D.sourceOrbit_restricted_quadraticRatio_gt_one h.toHypothesis1221 hnon _)
    (D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).ti
    (D.sourceOrbit_normalizer_le h.toHypothesis1221) with hsel | hrem
  · obtain ⟨I,i,S,s⟩ := hsel
    obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h.toHypothesis1221
    have hne := (selected_one_fixed_subgroup s D.sourceOrbit_weakClosure_setup
      n (D.hermitianOrbitCoordinates n d) j hj he).1
    omega
  · exact hrem

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
