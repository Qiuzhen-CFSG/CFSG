module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourNilpotent
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianSolvableSelection
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourKernel
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourRadicalPlacement

/-!
# Nilpotent radical exclusion on the original Hermitian tensor

At either canonical rank-four fixed subgroup, a nilpotent A.3.6 quotient
with an elementary omega radical gives a radical Sylow join in H-star.
Relative normality of the original residual and its simple SL₂(4) quotient
prove outside placement; Xi-irreducibility proves minimality. Selection in
that actual join gives a parameter-one pair with the same fixed subgroup.
The containing component's action on its binary section now has incompatible
degree bounds, at most ten and at least twenty-four.

The tensor endpoint retains the original action, Sylow, fixed subgroup,
residual kernel and containing normal C-component. It excludes the natural
alternative and proves that in the remaining nilpotent alternative every
odd Fitting core, and every radical quotient, is extraspecial of order p³
and exponent p. Thus all homocyclic exponents are excluded, without assuming
a center--Frattini equality or removing other Fitting primes.

Exclusion of those extraspecial cores, full 8.2.7 quasisimplicity, the zero
weak-closure branch, and the 8.2.8--13 contradiction remain unfinished.
Source: Aschbacher--Smith A.3.6 and 8.2.7, printed pp.43--45,717--718,
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

/-- The source radical's Sylow join belongs to the original H-star family.
Relative normality of the literal residual and its SL₂(4) quotient discharge
outside placement; the elementary omega plane discharges minimality. -/
theorem sourceOrbit_hermitian_nilpotent_elementary_radical_join
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (U K : Subgroup G) [IsElementaryAbelian 2 U]
    (hUV : U ≤ D.sourceOrbit) (hUne : U ≠ ⊥)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hKU : K ≤ normalizer (U : Set G))
    (hK : (K.subgroupOf (normalizer (U : Set G))).IsCComponent)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hRK : Chapter8.Section02.Normalizer.localResidual L U ≤ K)
    (hR : Nonempty (((Chapter8.Section02.Normalizer.localResidual L U) ⧸
      pCore 2 (Chapter8.Section02.Normalizer.localResidual L U)) ≃* SL(2,E 1)))
    (p : ℕ) [Fact p.Prime]
    (hnil : Chapter1.Section02.A36Nilpotent (Chapter1.XiQuotient K))
    [IsElementaryAbelian p (Chapter1.XiQuotient (Chapter1.XiP p K))]
    (hd : p ∣ Nat.card (fittingSubgroup (Chapter1.XiQuotient K))) :
    Chapter1.XiP p K ⊔ (T : Subgroup G) ∈
      Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) := by
  have hlocal : K ∈ Chapter1.L G (T : Subgroup G) := by
    refine ⟨hK.subgroupOf_of_le le_sup_left (sup_le hKU hTU),?_,?_⟩
    · exact ⟨T.subtype le_sup_right,map_subgroupOf_eq_of_le le_sup_right⟩
    · exact ne_bot_of_le_ne_bot hUne
        (le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 U)
          (hUV.trans (D.sourceOrbit_weakClosure_setup.le_sylow.trans le_sup_right))
          (sup_le hKU hTU))
  have hQ := Chapter1.Section02.uniqueness_local_quotient_sqtk h.simpleQTKE hlocal.2.2
  have hA36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  obtain ⟨hp,_,hXi⟩ := nilpotent_radical_member hA36 hlocal hQ hTK p hnil hd
  have hn := nilpotent_not_quasisimple hnil
  have ho : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left (by omega)
  let R := Chapter8.Section02.Normalizer.localResidual L U
  let H := L ⊓ normalizer (U : Set G)
  let er : solvableResidual H ≃* R :=
    (solvableResidual H).equivMapOfInjective H.subtype H.subtype_injective
  let : Group.IsPerfect R := Group.IsPerfect.ofSurjective
    (f := er.toMonoidHom) er.surjective
  let : IsSimpleGroup PSL(2,E 1) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [card_E]; norm_num)
  let : IsSimpleGroup SL(2,E 1) := (Theory.PSL2.sl2QuotientEquiv (E 1)).isSimpleGroup
  let : IsSimpleGroup (R ⧸ pCore 2 R) := hR.some.isSimpleGroup
  have hTR := Chapter8.Section02.Normalizer.normalizes_localResidual L U T
    D.sylow_normalizes_component hTU
  have hMR := Chapter8.Section02.Normalizer.normalizes_localResidual L U
    (normalizer (L : Set G) ⊓ normalizer (U : Set G)) inf_le_left inf_le_right
  have hout := radical_not_le_relative_normalizer hA36 hlocal hQ hTK hTR hRK hKU hMR
    hn ho hd hXi
  exact elementary_radical_join_HStar (p := p) T hXi D.sylow_normalizes_component hout

private theorem nilpotent_elementary_at_actor
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
    (hnil : Chapter1.Section02.A36Nilpotent (Chapter1.XiQuotient K))
    [IsElementaryAbelian p (Chapter1.XiQuotient (Chapter1.XiP p K))]
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
  obtain ⟨_,_,hXi⟩ := nilpotent_radical_member hA36 hlocal hQ hTK p hnil hd
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
  exact selected_one_nilpotent_elementary_exclusion s
    (D.sourceOrbit_hermitian_hstar_setup h hmany hV hnon hs hrow hH).1
    hH D.sourceOrbit_weakClosure_setup (h.simpleQTKE.evenCharacteristic T)
    e j hj he p hA36 hlocal hQ rfl hTK hKU' hnil hd

/-- At the actual selected fixed subgroup, the nilpotent A.3.6 radical cannot
have its original Sylow join in H-star. Selection in that join is constructed. -/
private theorem nilpotent_elementary_tensor_at_selected
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
    (hnil : Chapter1.Section02.A36Nilpotent (Chapter1.XiQuotient K))
    [IsElementaryAbelian p (Chapter1.XiQuotient (Chapter1.XiP p K))]
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
  exact D.nilpotent_elementary_at_actor h hmany hV hs hnon hrow d A K hAT har hu hTU
    hKU hK hTK p hnil hd hH

/-- The same nilpotent elementary-omega obstruction applies to the actual zero-closure
fixed subgroup C_V(W₀(T,V)); the moving whole conjugate and pair are constructed. -/
private theorem nilpotent_elementary_tensor_at_zero
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
    (hnil : Chapter1.Section02.A36Nilpotent (Chapter1.XiQuotient K))
    [IsElementaryAbelian p (Chapter1.XiQuotient (Chapter1.XiP p K))]
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
  exact D.nilpotent_elementary_at_actor h hmany hV hs hnon hrow d A K hg har hu' hTU'
    hKU' hK' hTK p hnil hd hH

/-- The containing component at the original selected fixed subgroup cannot
have an elementary radical quotient in the nilpotent A.3.6 alternative. Radical H-star placement is proved. -/
theorem sourceOrbit_hermitian_selected_component_not_elementary_nilpotent
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
    (hRK : Chapter8.Section02.Normalizer.localResidual L
      (D.sourceOrbit ⊓ centralizer
        (D.sourceOrbit.map (MulAut.conj i₀.val⁻¹).toMonoidHom ⊓ I₀.pCoreIn 2 : Set G)) ≤ K)
    (p : ℕ) [Fact p.Prime]
    (hnil : Chapter1.Section02.A36Nilpotent (Chapter1.XiQuotient K))
    (hd : p ∣ Nat.card (fittingSubgroup (Chapter1.XiQuotient K))) :
    ¬ IsElementaryAbelian p (Chapter1.XiQuotient (Chapter1.XiP p K)) := by
  intro hel
  let := hel
  obtain ⟨hn,_⟩ := D.sourceOrbit_hermitian_tensor_field_four
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel
  subst hn
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree hfield hmodel
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h.toHypothesis1221
  obtain ⟨_,_,_,hu,_,_,hTU,_⟩ := selected_one_fixed_subgroup s₀
    D.sourceOrbit_weakClosure_setup 1 (D.hermitianOrbitCoordinates 1 d) j hj he
  let U := D.sourceOrbit ⊓ centralizer
    (D.sourceOrbit.map (MulAut.conj i₀.val⁻¹).toMonoidHom ⊓ I₀.pCoreIn 2 : Set G)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le
    (show U ≤ D.sourceOrbit from inf_le_left)
  have hUne : U ≠ ⊥ := by
    intro hz
    change rank U = 4 at hu
    rw [hz,Representation.BinaryOffender.rank_bot] at hu
    omega
  have hR := (D.sourceOrbit_hermitian_selected_fixed_residual_kernel h.toHypothesis1221 d s₀).2
  have hH := D.sourceOrbit_hermitian_nilpotent_elementary_radical_join h.toHypothesis1221 U K
    inf_le_left hUne hTU hKU hK hTK hRK hR p hnil hd
  exact D.nilpotent_elementary_tensor_at_selected h hmany hV hs hnon
    B C eQ 1 hdegree hfield hmodel s₀ hKU hK hTK p hnil hd hH

/-- The containing component at the original zero fixed subgroup cannot
have an elementary radical quotient in the nilpotent A.3.6 alternative. Radical H-star placement is proved. -/
theorem sourceOrbit_hermitian_zero_component_not_elementary_nilpotent
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
    (hRK : Chapter8.Section02.Normalizer.localResidual L
      (D.sourceOrbit ⊓ centralizer (indexedWeakClosure D.sourceOrbit T 0 : Set G)) ≤ K)
    (p : ℕ) [Fact p.Prime]
    (hnil : Chapter1.Section02.A36Nilpotent (Chapter1.XiQuotient K))
    (hd : p ∣ Nat.card (fittingSubgroup (Chapter1.XiQuotient K))) :
    ¬ IsElementaryAbelian p (Chapter1.XiQuotient (Chapter1.XiP p K)) := by
  intro hel
  let := hel
  obtain ⟨hn,_⟩ := D.sourceOrbit_hermitian_tensor_field_four
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel
  subst hn
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree hfield hmodel
  obtain ⟨hu,hTU,_⟩ := D.sourceOrbit_hermitian_zero_closure_fixed h hmany hV hnon d hw
  let U := D.sourceOrbit ⊓ centralizer (indexedWeakClosure D.sourceOrbit T 0 : Set G)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le
    (show U ≤ D.sourceOrbit from inf_le_left)
  have hUne : U ≠ ⊥ := by
    intro hz
    change rank U = 4 at hu
    rw [hz,Representation.BinaryOffender.rank_bot] at hu
    omega
  have hR := (D.sourceOrbit_hermitian_zero_fixed_residual_kernel h hmany hV hnon d hw).2
  have hH := D.sourceOrbit_hermitian_nilpotent_elementary_radical_join h.toHypothesis1221 U K
    inf_le_left hUne hTU hKU hK hTK hRK hR p hnil hd
  exact D.nilpotent_elementary_tensor_at_zero h hmany hV hs hnon
    B C eQ 1 hdegree hfield hmodel hw K hKU hK hTK p hnil hd hH


/-- On the original half-field tensor, construct the Sylow-normal rank-four
subgroup and containing normal C-component. Exclude its natural A.3.6 quotient
and force every nilpotent odd core to be extraspecial on either weak-closure
branch. No radical placement premise remains. -/
theorem sourceOrbit_hermitian_tensor_component_nilpotent_radicals
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
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n) :
    n = 1 ∧ B.degree = 2 ∧
      ∃ U : Subgroup G, ∃ hU : IsElementaryAbelian 2 U, letI := hU
        U ≤ D.sourceOrbit ∧ rank U = 4 ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
        let R := Chapter8.Section02.Normalizer.localResidual L U
        R ⊓ centralizer (U : Set G) = R.pCoreIn 2 ∧
        Nonempty ((R ⧸ pCore 2 R) ≃* SL(2,E 1)) ∧
        Group.IsSolvable (L ⊓ centralizer (U : Set G) : Subgroup G) ∧
        ∃ K : Subgroup G, K ≤ normalizer (U : Set G) ∧
          (K.subgroupOf (normalizer (U : Set G))).IsCComponent ∧
          R ≤ K ∧ normalizer (U : Set G) ≤ normalizer (K : Set G) ∧
          ¬ Chapter1.Section02.A36Natural (Chapter1.XiQuotient K) ∧
          (Chapter1.Section02.A36Nilpotent (Chapter1.XiQuotient K) →
            ∀ (p : ℕ) (_ : Fact p.Prime),
              p ∣ Nat.card (fittingSubgroup (Chapter1.XiQuotient K)) →
              Chapter1.Section02.LocalModels.OddExtraspecialThree p
                (pCore p (Chapter1.XiQuotient K)) ∧
              IsExtraspecial p (Chapter1.XiQuotient (Chapter1.XiP p K)) ∧
              Nat.card (Chapter1.XiQuotient (Chapter1.XiP p K)) = p^3 ∧
              Monoid.exponent (Chapter1.XiQuotient (Chapter1.XiP p K)) = p) := by
  obtain ⟨hn,hB⟩ := D.sourceOrbit_hermitian_tensor_field_four
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel
  refine ⟨hn,hB,?_⟩
  subst hn
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree hfield hmodel
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h.toHypothesis1221
  by_cases hw : globalW D.sourceOrbit T = 0
  · let U := D.sourceOrbit ⊓ centralizer (indexedWeakClosure D.sourceOrbit T 0 : Set G)
    let hU : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ D.sourceOrbit from inf_le_left)
    let := hU
    have hr := (D.sourceOrbit_hermitian_initial_parameters 1 d h hmany hV hnon).1
    have hm := (D.sourceOrbit_hermitian_localM 1 d h.toHypothesis1221).1
    obtain ⟨hu,hUT,_⟩ := field_four_zero_closure_fixed D.sourceOrbit
      (D.hermitianOrbitCoordinates 1 d) j hj he T D.sourceOrbit_weakClosure_setup
      (D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon) hr hm hw
    obtain ⟨hk,heq⟩ := D.sourceOrbit_hermitian_zero_fixed_residual_kernel h hmany hV hnon d hw
    obtain ⟨hsol,hR,_⟩ := D.sourceOrbit_hermitian_zero_fixed_centralizer h hmany hV hnon d hw
    have hUne : U ≠ ⊥ := by
      intro hz
      have hu' : rank U = 4 := hu
      rw [hz,Representation.BinaryOffender.rank_bot] at hu'
      omega
    obtain ⟨K,hKU,hK,hRK,hNK⟩ := D.sourceOrbit_hermitian_fixed_overcomponent
      h.toHypothesis1221 U inf_le_left hUne hUT hR
    refine ⟨U,hU,inf_le_left,hu,hUT,hk,heq,hsol,K,hKU,hK,hRK,hNK,?_,?_⟩
    · exact D.sourceOrbit_hermitian_zero_component_not_natural h hmany hV hs hnon
        B C eQ 1 hdegree hfield hmodel hw K hKU hK (hUT.trans hNK) hRK
    · intro hnil p hp hd
      let := hp
      exact nilpotent_core_extraspecial_of_not_elementary K hnil p hd
        (D.sourceOrbit_hermitian_zero_component_not_elementary_nilpotent h hmany hV hs hnon
          B C eQ 1 hdegree hfield hmodel hw K hKU hK (hUT.trans hNK) hRK p hnil hd)
  · have hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs := by
      refine ⟨B,C,⟨eQ⟩,?_⟩
      dsimp only
      rw [hdegree]
      exact ⟨by decide,hfield,d.linearEquiv.finrank_eq.trans (finrank_binary 1),hmodel⟩
    obtain ⟨H,hH,_⟩ := D.sourceOrbit_hermitian_exists_HStar_outside_core h hmany hs hrow
    obtain ⟨_,I,i,S,s⟩ := D.sourceOrbit_hermitian_tensor_selected_of_positive
      h hmany hV hs hnon B C eQ 1 hdegree hfield hmodel (pos_iff_ne_zero.mpr hw) hH
    let A := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2
    let U := D.sourceOrbit ⊓ centralizer (A : Set G)
    let hU : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ D.sourceOrbit from inf_le_left)
    let := hU
    obtain ⟨_,_,_,hu,_,_,hUT,_⟩ := selected_one_fixed_subgroup s
      D.sourceOrbit_weakClosure_setup 1 (D.hermitianOrbitCoordinates 1 d) j hj he
    obtain ⟨hk,heq⟩ := D.sourceOrbit_hermitian_selected_fixed_residual_kernel h.toHypothesis1221 d s
    obtain ⟨hsol,hR,_⟩ := D.sourceOrbit_hermitian_selected_fixed_centralizer h.toHypothesis1221 d s
    have hUne : U ≠ ⊥ := by
      intro hz
      have hu' : rank U = 4 := hu
      rw [hz,Representation.BinaryOffender.rank_bot] at hu'
      omega
    obtain ⟨K,hKU,hK,hRK,hNK⟩ := D.sourceOrbit_hermitian_fixed_overcomponent
      h.toHypothesis1221 U inf_le_left hUne hUT hR
    refine ⟨U,hU,inf_le_left,hu,hUT,hk,heq,hsol,K,hKU,hK,hRK,hNK,?_,?_⟩
    · exact D.sourceOrbit_hermitian_selected_component_not_natural h hmany hV hs hnon
        B C eQ 1 hdegree hfield hmodel s hKU hK (hUT.trans hNK) hRK
    · intro hnil p hp hd
      let := hp
      exact nilpotent_core_extraspecial_of_not_elementary K hnil p hd
        (D.sourceOrbit_hermitian_selected_component_not_elementary_nilpotent h hmany hV hs hnon
          B C eQ 1 hdegree hfield hmodel s hKU hK (hUT.trans hNK) hRK p hnil hd)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
