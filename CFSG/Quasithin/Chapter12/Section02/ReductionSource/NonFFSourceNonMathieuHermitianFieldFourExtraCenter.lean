module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourExtraCenter
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourExtraspecial
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianCentralizers

/-!
# Extraspecial center placement on the original Hermitian tensor

On either canonical four-space, every p-subgroup of M = N_G(L), p > 3,
centralizing that four-space centralizes the original chosen module.
E.6.1 supplies normalization of that module; the literal conjugate-plane
marking supplies the Hermitian pointwise-stabilizer calculation.

B.6.8 also places the center of every extraspecial subgroup of a solvable
original H-star group in M. Combining these deductions with the actual
nilpotent radical and its Sylow supplements puts each center in M intersect
C_G(V), conditional on the actual radical join XT belonging to H-star.
The center has order p, its full normalizer escapes M, and the full odd core
of that normalizer lies in M by 4.4.8.

The tensor endpoint constructs the same original Sylow-normal four-space,
residual kernel, SL₂(4) quotient and containing normal C-component on both
weak-closure branches. It discharges all plane-action and center-placement
callbacks. Extraspecial radical H-star placement and control of the whole
odd normalizer remain to be proved; the elementary-radical H-star theorem
does not discharge the former. Thus 8.2.7 quasisimplicity, zero-closure
exclusion, 8.2.8--13 and the final non-FF contradiction remain unfinished.

Source: Aschbacher--Smith B.6.8(2), H.4.6(3), 4.4.8 and the extraspecial
paragraph of 8.2.7, printed pp.113--114,382,620,718, refs/quasithin.pdf
(1 March 2004 manuscript).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- In the selected branch, a p-subgroup of M fixing the canonical
four-space fixes the original module, for every p > 3. -/
theorem sourceOrbit_hermitian_selected_prime_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S)
    (Z : Subgroup G) {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hZ : IsPGroup p Z)
    (hZM : Z ≤ normalizer (L : Set G))
    (hZU : Z ≤ centralizer (D.sourceOrbit ⊓ centralizer
      (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G) : Set G)) :
    Z ≤ centralizer (D.sourceOrbit : Set G) := by
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h.toHypothesis1221
  obtain ⟨_,hAT,_,hu,_,_,_,_,_,c,hc⟩ := selected_one_fixed_subgroup s
    D.sourceOrbit_weakClosure_setup 1 (D.hermitianOrbitCoordinates 1 d) j hj he
  let A := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2
  let U := D.sourceOrbit ⊓ centralizer (A : Set G)
  have hUne : U ≠ ⊥ := by
    intro hz
    change rank U = 4 at hu
    rw [hz,Representation.BinaryOffender.rank_bot] at hu
    omega
  have hZN : Z ≤ normalizer (D.sourceOrbit : Set G) :=
    (le_inf hZM hZU).trans
      ((D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).localCentralizer_le_normalizer
        hUne (show U ≤ D.sourceOrbit from inf_le_left))
  exact field_four_prime_centralizer_at_actor D.sourceOrbit A Z
    (D.hermitianOrbitCoordinates 1 d) j hj he
    (hAT.trans D.sourceOrbit_weakClosure_setup.normalizes) c hc hp hZ hZN hZU

/-- The same prime centralizer conclusion at the original zeroth weak-closure
fixed subgroup; the zero branch and its entire centralizer kernel are retained. -/
theorem sourceOrbit_hermitian_zero_prime_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (hw : globalW D.sourceOrbit T = 0)
    (Z : Subgroup G) {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hZ : IsPGroup p Z)
    (hZM : Z ≤ normalizer (L : Set G))
    (hZU : Z ≤ centralizer (D.sourceOrbit ⊓ centralizer
      (indexedWeakClosure D.sourceOrbit T 0 : Set G) : Set G)) :
    Z ≤ centralizer (D.sourceOrbit : Set G) := by
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h.toHypothesis1221
  have hr := (D.sourceOrbit_hermitian_initial_parameters 1 d h hmany hV hnon).1
  have hm := (D.sourceOrbit_hermitian_localM 1 d h.toHypothesis1221).1
  obtain ⟨c,hc⟩ := (field_four_zero_closure_quotient D.sourceOrbit
    (D.hermitianOrbitCoordinates 1 d) j hj he T D.sourceOrbit_weakClosure_setup
    (D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon) hr hm hw).1
  obtain ⟨hu,_,_⟩ := D.sourceOrbit_hermitian_zero_closure_fixed h hmany hV hnon d hw
  let U := D.sourceOrbit ⊓ centralizer (indexedWeakClosure D.sourceOrbit T 0 : Set G)
  have hUne : U ≠ ⊥ := by
    intro hz
    change rank U = 4 at hu
    rw [hz,Representation.BinaryOffender.rank_bot] at hu
    omega
  have hZN : Z ≤ normalizer (D.sourceOrbit : Set G) :=
    (le_inf hZM hZU).trans
      ((D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).localCentralizer_le_normalizer
        hUne (show U ≤ D.sourceOrbit from inf_le_left))
  exact field_four_prime_centralizer_at_actor D.sourceOrbit _ Z
    (D.hermitianOrbitCoordinates 1 d) j hj he
    ((indexedWeakClosure_le _ _ _).trans D.sourceOrbit_weakClosure_setup.normalizes)
    c hc hp hZ hZN hZU

/-- B.6.8 on an actual original H-star group places every contained
extraspecial center in N_G(L). Solvability is explicit. -/
theorem sourceOrbit_hermitian_hstar_extraspecial_center
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs)
    {H Y : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hsol : Group.IsSolvable H) (hYH : Y ≤ H)
    {p : ℕ} [Fact p.Prime] [IsExtraspecial p Y] (hp : 3 < p) :
    (center Y).map Y.subtype ≤ normalizer (L : Set G) := by
  have ho : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left (by omega)
  exact extraspecial_center_le_of_solvable_parabolic
    (D.sourceOrbit_hermitian_hstar_setup h hmany hV hnon hs hrow hH).1 hsol hYH ho

private theorem nilpotent_centers_at_four_space
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (U K : Subgroup G) [IsElementaryAbelian 2 U]
    (hUV : U ≤ D.sourceOrbit) (hu : rank U = 4)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hKU : K ≤ normalizer (U : Set G))
    (hK : (K.subgroupOf (normalizer (U : Set G))).IsCComponent)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hRK : Chapter8.Section02.Normalizer.localResidual L U ≤ K)
    (hR : Nonempty (((Chapter8.Section02.Normalizer.localResidual L U) ⧸
      pCore 2 (Chapter8.Section02.Normalizer.localResidual L U)) ≃* SL(2,E 1)))
    (p : ℕ) [Fact p.Prime]
    (hnil : Chapter1.Section02.A36Nilpotent (Chapter1.XiQuotient K))
    (hd : p ∣ Nat.card (fittingSubgroup (Chapter1.XiQuotient K)))
    (hx : IsExtraspecial p (Chapter1.XiQuotient (Chapter1.XiP p K)))
    (hc : Nat.card (Chapter1.XiQuotient (Chapter1.XiP p K)) = p^3)
    (hexp : Monoid.exponent (Chapter1.XiQuotient (Chapter1.XiP p K)) = p)
    (hprime : ∀ Z : Subgroup G, IsPGroup p Z → Z ≤ normalizer (L : Set G) →
      Z ≤ centralizer (U : Set G) → Z ≤ centralizer (D.sourceOrbit : Set G))
    (hjoin : Chapter1.XiP p K ⊔ (T : Subgroup G) ∈
      Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ∀ P : Sylow p (Chapter1.XiP p K),
      let Y := (P : Subgroup (Chapter1.XiP p K)).map (Chapter1.XiP p K).subtype
      let Z := (center Y).map Y.subtype
      Nat.card Z = p ∧ IsCyclic Z ∧ Z ≠ ⊥ ∧
        Z ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) ∧
        ¬ normalizer (Z : Set G) ≤ normalizer (L : Set G) ∧
        (pPrimeCore 2 (normalizer (Z : Set G))).map (normalizer (Z : Set G)).subtype ≤
          normalizer (L : Set G) := by
  obtain ⟨hXi,hcent,_,hout⟩ := D.sourceOrbit_hermitian_nilpotent_radical_centralizer
    h.toHypothesis1221 U K hUV hu hTU hKU hK hTK hRK hR p hnil hd
  have hp := (Chapter1.RadicalStructure.radical_core (Or.inr hnil) hd).2.1
  have ho : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left (by omega)
  let X := Chapter1.XiP p K
  let H := X ⊔ (T : Subgroup G)
  let : Group.IsSolvable X := hXi.isSolvable
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  have hsol : Group.IsSolvable H := Group.isSolvable_sup_of_normalizes _ _ hXi.invariant
  intro P
  let Y := (P : Subgroup X).map X.subtype
  let Z := (center Y).map Y.subtype
  have hq : Chapter1.XiOddQuotient p (Chapter1.XiQuotient X) := Or.inr ⟨hx,hc,hexp⟩
  let e := hXi.ambientSylowQuotientEquiv ho hq P
  let : IsExtraspecial p Y := IsExtraspecial.of_mulEquiv e.symm hx
  have hYU : Y ≤ centralizer (U : Set G) := (map_subtype_le _).trans hcent
  obtain ⟨hZcard,hcyc,hne,hZU,_,hescape⟩ := extraspecial_supplement_center_escape (p := p) hYU (hout P)
  have hZM : Z ≤ normalizer (L : Set G) :=
    D.sourceOrbit_hermitian_hstar_extraspecial_center h hmany hV hnon hs hrow
      hjoin hsol ((map_subtype_le _).trans le_sup_left) hp
  have hZcard : Nat.card Z = p := hZcard
  have hZp : IsPGroup p Z := IsPGroup.of_card (n := 1) (hZcard.trans (pow_one p).symm)
  have hZV := hprime Z hZp hZM hZU
  have hplaced := le_inf hZM hZV
  exact ⟨hZcard,hcyc,hne,hplaced,hescape,
    (D.sourceOrbit_hermitian_oddNormalizer_oddCore 1 d h.toHypothesis1221 hV Z hplaced
      (by rwa [hZcard])).2⟩

/-- On the literal half-field tensor, construct the original four-space,
residual and containing C-component. Every remaining nilpotent radical is
extraspecial. If its actual Sylow join lies in H-star, every Sylow supplement's
actual center lies in M intersect C_G(V), has an escaping normalizer, and has
that normalizer's full odd core contained in M. H-star placement and control
of the whole odd normalizer remain to be proved. -/
theorem sourceOrbit_hermitian_tensor_nilpotent_centers_of_hstar
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
              Monoid.exponent (Chapter1.XiQuotient (Chapter1.XiP p K)) = p ∧
              (Chapter1.XiP p K ⊔ (T : Subgroup G) ∈
                Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
                ∀ P : Sylow p (Chapter1.XiP p K),
                  let Y := (P : Subgroup (Chapter1.XiP p K)).map (Chapter1.XiP p K).subtype
                  let Z := (center Y).map Y.subtype
                  Nat.card Z = p ∧ IsCyclic Z ∧ Z ≠ ⊥ ∧
                    Z ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) ∧
                    ¬ normalizer (Z : Set G) ≤ normalizer (L : Set G) ∧
                    (pPrimeCore 2 (normalizer (Z : Set G))).map (normalizer (Z : Set G)).subtype ≤
                      normalizer (L : Set G))) := by
  obtain ⟨hn,hB⟩ := D.sourceOrbit_hermitian_tensor_field_four
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel
  refine ⟨hn,hB,?_⟩
  subst hn
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree hfield hmodel
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h.toHypothesis1221
  have hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs := by
    refine ⟨B,C,⟨eQ⟩,?_⟩
    dsimp only
    rw [hdegree]
    exact ⟨by decide,hfield,d.linearEquiv.finrank_eq.trans (finrank_binary 1),hmodel⟩
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
      obtain ⟨hfull,hx,hcard,hexp⟩ := nilpotent_core_extraspecial_of_not_elementary K hnil p hd
        (D.sourceOrbit_hermitian_zero_component_not_elementary_nilpotent h hmany hV hs hnon
          B C eQ 1 hdegree hfield hmodel hw K hKU hK (hUT.trans hNK) hRK p hnil hd)
      refine ⟨hfull,hx,hcard,hexp,?_⟩
      apply D.nilpotent_centers_at_four_space h hmany hV hnon hs hrow d U K
        inf_le_left hu hUT hKU hK (hUT.trans hNK) hRK heq p hnil hd hx hcard hexp
      intro Z hZ hZM hZU
      have hp3 := (Chapter1.RadicalStructure.radical_core (Or.inr hnil) hd).2.1
      exact D.sourceOrbit_hermitian_zero_prime_centralizer h hmany hV hnon d hw Z hp3 hZ hZM hZU
  · obtain ⟨H,hH,_⟩ := D.sourceOrbit_hermitian_exists_HStar_outside_core h hmany hs hrow
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
      obtain ⟨hfull,hx,hcard,hexp⟩ := nilpotent_core_extraspecial_of_not_elementary K hnil p hd
        (D.sourceOrbit_hermitian_selected_component_not_elementary_nilpotent h hmany hV hs hnon
          B C eQ 1 hdegree hfield hmodel s hKU hK (hUT.trans hNK) hRK p hnil hd)
      refine ⟨hfull,hx,hcard,hexp,?_⟩
      apply D.nilpotent_centers_at_four_space h hmany hV hnon hs hrow d U K
        inf_le_left hu hUT hKU hK (hUT.trans hNK) hRK heq p hnil hd hx hcard hexp
      intro Z hZ hZM hZU
      have hp3 := (Chapter1.RadicalStructure.radical_core (Or.inr hnil) hd).2.1
      exact D.sourceOrbit_hermitian_selected_prime_centralizer h hmany hV hnon d s Z hp3 hZ hZM hZU

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
