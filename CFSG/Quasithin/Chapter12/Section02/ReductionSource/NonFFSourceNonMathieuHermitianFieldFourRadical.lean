module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourRadical
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianSolvableSelection
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourKernel
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete

/-!
# The natural odd-plane obstruction on the original Hermitian tensor

At the original Sylow-normal rank-four fixed subgroup, a containing
C-component with natural A.3.6 quotient supplies its actual Ξ_p radical.
If its Sylow join lies in the original H-star family, solvability constructs
a parameter-one selected pair there. Saturated-plane uniqueness identifies
its fixed subgroup with the original one. The Chapter 8 section argument
then contradicts the faithful natural extension's minimum dimension.

Both the selected-pair and zero-closure subgroups are treated. Tensor descent
uses the actual chosen orbit and automizer, and full A/C discharge the A.3.6
input and local quotient hypotheses. No section, inversion, pair existence,
Ξ-membership or dimension premise is added to the tensor applications.

The radical join's H-star placement remains explicit. Proving that placement,
handling the nilpotent A.3.6 alternative, and completing the zero-closure and
8.2.8--13 arguments remain with the Hermitian assembly owner. These exports
are conditional natural-branch exclusions, not the completed source 8.2.7.
Source: Aschbacher--Smith 8.2.7, printed pp.717--718,
refs/quasithin.pdf (1 March 2004 manuscript).
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
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem natural_radical_at_actor
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (A K : Subgroup G) [IsElementaryAbelian 2 A]
    (hAT : A ≤ T) (har : rank (inducedAutomizer D.sourceOrbit A) = 4)
    (hu : rank (D.sourceOrbit ⊓ centralizer (A : Set G)) = 4)
    (hTU : (T : Subgroup G) ≤ normalizer
      (D.sourceOrbit ⊓ centralizer (A : Set G) : Set G))
    (hKU : K ≤ normalizer
      (D.sourceOrbit ⊓ centralizer
        (A : Set G) : Set G))
    (hK : (K.subgroupOf (normalizer
      (D.sourceOrbit ⊓ centralizer
        (A : Set G) : Set G))).IsCComponent)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (p : ℕ) [Fact p.Prime]
    (hnat : Chapter1.Section02.A36Natural (Chapter1.XiQuotient K))
    (hd : p ∣ Nat.card (fittingSubgroup (Chapter1.XiQuotient K)))
    (hH : Chapter1.XiP p K ⊔ (T : Subgroup G) ∈
      Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) : False := by
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h.toHypothesis1221
  let e := D.hermitianOrbitCoordinates 1 d
  let U := D.sourceOrbit ⊓ centralizer
    (A : Set G)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le
    (show U ≤ D.sourceOrbit from inf_le_left)
  have hUne : U ≠ ⊥ := by
    intro hz
    change rank U = 4 at hu
    rw [hz,Representation.BinaryOffender.rank_bot] at hu
    omega
  have hlocal : K ∈ Chapter1.L G (T : Subgroup G) := by
    refine ⟨hK.subgroupOf_of_le le_sup_left (sup_le hKU hTU),?_,?_⟩
    · exact ⟨T.subtype le_sup_right,map_subgroupOf_eq_of_le le_sup_right⟩
    · exact ne_bot_of_le_ne_bot hUne
        (le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 U)
          ((show U ≤ D.sourceOrbit from inf_le_left).trans
            (D.sourceOrbit_weakClosure_setup.le_sylow.trans le_sup_right))
          (sup_le hKU hTU))
  have hQ := Chapter1.Section02.uniqueness_local_quotient_sqtk h.simpleQTKE hlocal.2.2
  have hA36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hXi := natural_radical_member hA36 hlocal hQ hTK p hnat hd
  let : Group.IsSolvable (Chapter1.XiP p K) := hXi.isSolvable
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  have hsol : Group.IsSolvable (Chapter1.XiP p K ⊔ (T : Subgroup G) : Subgroup G) :=
    Group.isSolvable_sup_of_normalizes _ _ hXi.invariant
  obtain ⟨I,i,S,s⟩ := D.sourceOrbit_hermitian_selected_of_solvable
    h hmany hV hnon hs hrow hH hsol
  let A' := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2
  let : IsElementaryAbelian 2 (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom) :=
    IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A' := IsElementaryAbelian.of_le
    (show A' ≤ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom from inf_le_left)
  obtain ⟨_,hAT',har',hu',_⟩ := selected_one_fixed_subgroup s
    D.sourceOrbit_weakClosure_setup 1 e j hj he
  have hsame := (field_four_saturated_actors_eq D.sourceOrbit e j hj he T
    D.sourceOrbit_weakClosure_setup A A' hAT hAT' har har' hu hu').2
  have hKU' : K ≤ normalizer
      (D.sourceOrbit ⊓ centralizer
        (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G) : Set G) := by
    exact hKU.trans (congrArg (fun U : Subgroup G => normalizer (U : Set G)) hsame).le
  exact selected_one_natural_radical_exclusion s
    (D.sourceOrbit_hermitian_hstar_setup h hmany hV hnon hs hrow hH).1
    hH D.sourceOrbit_weakClosure_setup (h.simpleQTKE.evenCharacteristic T)
    e j hj he p hA36 hlocal hQ rfl hTK hKU' hnat hd

/-- At the actual selected fixed subgroup, the natural A.3.6 radical cannot
have its original Sylow join in H-star. Selection in that join is constructed. -/
theorem sourceOrbit_hermitian_tensor_natural_radical_exclusion
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n)
    {H₀ I₀ K : Subgroup G} {i₀ : I₀} {S₀ : Sylow 2 I₀}
    (s₀ : Selected H₀ T (normalizer (L : Set G)) D.sourceOrbit I₀ 1 i₀ S₀)
    (hKU : K ≤ normalizer
      (D.sourceOrbit ⊓ centralizer
        (D.sourceOrbit.map (MulAut.conj i₀.val⁻¹).toMonoidHom ⊓ I₀.pCoreIn 2 : Set G) : Set G))
    (hK : (K.subgroupOf (normalizer
      (D.sourceOrbit ⊓ centralizer
        (D.sourceOrbit.map (MulAut.conj i₀.val⁻¹).toMonoidHom ⊓ I₀.pCoreIn 2 : Set G) : Set G))).IsCComponent)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (p : ℕ) [Fact p.Prime]
    (hnat : Chapter1.Section02.A36Natural (Chapter1.XiQuotient K))
    (hd : p ∣ Nat.card (fittingSubgroup (Chapter1.XiQuotient K)))
    (hH : Chapter1.XiP p K ⊔ (T : Subgroup G) ∈
      Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) : False := by
  obtain ⟨hn,_⟩ := D.sourceOrbit_hermitian_tensor_field_four
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel
  subst hn
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree hfield hmodel
  have hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs := by
    refine ⟨B,C,⟨eQ⟩,?_⟩
    dsimp only
    rw [hdegree]
    exact ⟨by decide,hfield,d.linearEquiv.finrank_eq.trans (finrank_binary 1),hmodel⟩
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h.toHypothesis1221
  obtain ⟨_,hAT,har,hu,_,_,hTU,_⟩ := selected_one_fixed_subgroup s₀
    D.sourceOrbit_weakClosure_setup 1 (D.hermitianOrbitCoordinates 1 d) j hj he
  let A := D.sourceOrbit.map (MulAut.conj i₀.val⁻¹).toMonoidHom ⊓ I₀.pCoreIn 2
  let : IsElementaryAbelian 2 (D.sourceOrbit.map (MulAut.conj i₀.val⁻¹).toMonoidHom) :=
    IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le
    (show A ≤ D.sourceOrbit.map (MulAut.conj i₀.val⁻¹).toMonoidHom from inf_le_left)
  exact D.natural_radical_at_actor h hmany hV hs hnon hrow d A K hAT har hu hTU
    hKU hK hTK p hnat hd hH

/-- The same natural-radical obstruction applies to the actual zero-closure
fixed subgroup C_V(W₀(T,V)); the moving whole conjugate and pair are constructed. -/
theorem sourceOrbit_hermitian_zero_natural_radical_exclusion
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n)
    (hw : globalW D.sourceOrbit T = 0)
    (K : Subgroup G)
    (hKU : K ≤ normalizer
      (D.sourceOrbit ⊓ centralizer (indexedWeakClosure D.sourceOrbit T 0 : Set G) : Set G))
    (hK : (K.subgroupOf (normalizer
      (D.sourceOrbit ⊓ centralizer (indexedWeakClosure D.sourceOrbit T 0 : Set G) : Set G))).IsCComponent)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (p : ℕ) [Fact p.Prime]
    (hnat : Chapter1.Section02.A36Natural (Chapter1.XiQuotient K))
    (hd : p ∣ Nat.card (fittingSubgroup (Chapter1.XiQuotient K)))
    (hH : Chapter1.XiP p K ⊔ (T : Subgroup G) ∈
      Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) : False := by
  obtain ⟨hn,_⟩ := D.sourceOrbit_hermitian_tensor_field_four
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel
  subst hn
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree hfield hmodel
  have hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs := by
    refine ⟨B,C,⟨eQ⟩,?_⟩
    dsimp only
    rw [hdegree]
    exact ⟨by decide,hfield,d.linearEquiv.finrank_eq.trans (finrank_binary 1),hmodel⟩
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h.toHypothesis1221
  let e := D.hermitianOrbitCoordinates 1 d
  have hr := (D.sourceOrbit_hermitian_initial_parameters 1 d h hmany hV hnon).1
  have hm := (D.sourceOrbit_hermitian_localM 1 d h.toHypothesis1221).1
  have hFF := D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon
  obtain ⟨_,_,g,hg,hOff,har,_⟩ := field_four_zero_weak_closure D.sourceOrbit e j hj he
    T D.sourceOrbit_weakClosure_setup hFF hr hm hw
  have hmove : ¬ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ≤
      centralizer (D.sourceOrbit : Set G) := by
    intro hc
    exact hOff.1 (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc))
  obtain ⟨hu,hTU,hfixed⟩ := D.sourceOrbit_hermitian_zero_closure_fixed h hmany hV hnon d hw
  have hsame := hfixed g hg hmove
  let A := D.sourceOrbit.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hu' : rank (D.sourceOrbit ⊓ centralizer (A : Set G)) = 4 := by
    rw [hsame]
    exact hu
  have hnorm := congrArg (fun U : Subgroup G => normalizer (U : Set G)) hsame
  have hTU' : (T : Subgroup G) ≤ normalizer
      (D.sourceOrbit ⊓ centralizer (A : Set G) : Set G) := hTU.trans hnorm.ge
  have hKU' : K ≤ normalizer
      (D.sourceOrbit ⊓ centralizer (A : Set G) : Set G) := hKU.trans hnorm.ge
  have hK' : (K.subgroupOf (normalizer
      (D.sourceOrbit ⊓ centralizer (A : Set G) : Set G))).IsCComponent := by
    exact hK.subgroupOf_of_le hKU' hnorm.le
  exact D.natural_radical_at_actor h hmany hV hs hnon hrow d A K hg har hu' hTU'
    hKU' hK' hTK p hnat hd hH

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
