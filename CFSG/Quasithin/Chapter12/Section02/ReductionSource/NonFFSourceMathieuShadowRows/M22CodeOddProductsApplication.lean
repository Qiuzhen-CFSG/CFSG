module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeMultiplicityApplication
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourOddProducts
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelection
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Pair

/-!
# Cubic quotient for every original M22-code degree-one pair

The weak-closure bound gives the rank-five actor and fixed four-space for
the supplied pair. Rank-five uniqueness inside the original Sylow identifies
this fixed space with the one for which the containing-component theorem
was proved. Only those fixed-space component facts are transported: the
pair, conjugator, literal B/U and P/U and their actions remain the supplied
ones. The faithful binary multiplicity action then forces I/O₂(I) ≅ S₃.

The internal M24-pair import reuses its general non-FF normalization and
quadratic-ratio helpers on this original Mathieu orbit.

Source: Aschbacher--Smith 8.2.5--9, printed pp.716--720, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open Chapter8.Section02.HermitianSource Chapter8.Section02.Offenders
open Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.Normalizer Chapter8.Section02.Normalizer.SmallOvergroups
open Chapter8.Section02.MathieuShadowRows MathieuCode.M22Quintet.CocodeTransfer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

set_option maxHeartbeats 1000000 in
/-- The full cubic package belongs to every supplied original degree-one
pair, with its own quintet map, full covering kernel and multiplicity action. -/
theorem sourceOrbit_m22_code_selected_cubic_data
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation)
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S) :
    let A := offenderNormalizer D.sourceOrbit i.val⁻¹
    let U := D.sourceOrbit ⊓ centralizer (A : Set G)
    let B := D.sourceOrbit ⊓ I.pCoreIn 2
    let R := localResidual L U
    A = D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 ∧
      A ≤ T ∧ U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      U = A ⊓ centralizer (D.sourceOrbit : Set G) ∧ I ≤ centralizer (U : Set G) ∧
      rank (inducedAutomizer D.sourceOrbit A) = 5 ∧ rank U = 4 ∧
      (U.subgroupOf T).Normal ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      ⁅R,centralizer (U : Set G)⁆ ≤ R.pCoreIn 2 ∧
      R ≤ normalizer (I : Set G) ∧ R ≤ normalizer (I.pCoreIn 2 : Set G) ∧
      (∃ K : Subgroup G, K ≤ normalizer (U : Set G) ∧
        (K.subgroupOf (normalizer (U : Set G))).IsCComponent ∧ R ≤ K ∧
        normalizer (U : Set G) ≤ normalizer (K : Set G) ∧
        IsQuasisimple (K ⧸ pCore 2 K) ∧ K.pCoreIn 2 ≤ T ∧
        R ⊔ K.pCoreIn 2 ≤ normalizer (I : Set G) ∧
        R ⊔ K.pCoreIn 2 ≤ normalizer (I.pCoreIn 2 : Set G)) ∧
      ∃ f : (L ⊓ normalizer (U : Set G) : Subgroup G) →* M22Quintet.Q,
        f.ker = D.orbitComponentHom.ker.comap
          (inclusion (show (L ⊓ normalizer (U : Set G) : Subgroup G) ≤ L from inf_le_left)) ∧
        M22FiveSection R B U (f.comp (inclusion (localResidual_le L U))) ∧
        M22CodePairProductAction R I D.sourceOrbit U ∧
        M22CodePairAction R I D.sourceOrbit U i (f.comp (inclusion (localResidual_le L U))) ∧
        M22CodePairMultiplicityAction R I D.sourceOrbit U i (f.comp (inclusion (localResidual_le L U))) ∧
        Nonempty ((I ⧸ pCore 2 I) ≃* PSL(2,ZMod 2)) := by
  obtain ⟨a,hinj,hE,_⟩ := D.sourceOrbit_m22_code_full_automizer h.toHypothesis1221 d
  have hrank : primeRank 2 (Automizer D.sourceOrbit) ≤ 5 :=
    (Theory.GroupTheory.primeRank_le_of_injective 2
      (m22PairStabilizerEquivAut.toMonoidHom.comp a)
      (m22PairStabilizerEquivAut.injective.comp hinj)).trans m22_automorphism_twoRank_le_five
  have hpos := D.sourceOrbit_m22_code_globalW_pos h hmany hV hnon d
  obtain ⟨hw,hOff,hA,hAT,hker⟩ := selected_offender_of_parameter_bound s
    D.sourceOrbit_weakClosure_setup (Order.one_le_iff_pos.mpr hpos)
  have hFF := D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon
  have hr := D.sourceOrbit_m22_code_globalR_ge_six h hmany hV hnon d
  obtain ⟨_,hfive,_,hfour,hfix⟩ := code_row_parameters D.sourceOrbit T i.val⁻¹
    D.sourceOrbit_weakClosure_setup hFF hOff hw 5 (by decide) hr hrank hker
  have hv : rank D.sourceOrbit = 10 :=
    (Chapter7.log_card_eq_finrank D.sourceOrbit).trans
      ((D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv).finrank_eq.trans finrank_m22Code)
  rw [hv] at hfour
  have hcent := generated_pair_centralizes_fixed D.sourceOrbit i.val⁻¹ hfix
  rw [s.generate] at hcent
  let A := offenderNormalizer D.sourceOrbit i.val⁻¹
  let U := D.sourceOrbit ⊓ centralizer (A : Set G)
  let R := localResidual L U
  let : IsElementaryAbelian 2 (inducedAutomizer D.sourceOrbit A) :=
    offender_inducedAutomizer_elementary D.sourceOrbit i.val⁻¹
  obtain ⟨I₀,i₀,S₀,s₀,_,hA₀T,_,_,_,hfive₀,_,hU₀T,hTU₀,_,hcomm₀,_,_,
    K,hKU₀,hK₀,hR₀K,hN₀K,hquasi,hQT,_,_⟩ :=
    D.sourceOrbit_m22_code_component_pair h hmany hV hnon d hH
  let A₀ := offenderNormalizer D.sourceOrbit i₀.val⁻¹
  let U₀ := D.sourceOrbit ⊓ centralizer (A₀ : Set G)
  let : IsElementaryAbelian 2 (inducedAutomizer D.sourceOrbit A₀) :=
    offender_inducedAutomizer_elementary D.sourceOrbit i₀.val⁻¹
  have hUU : U = U₀ := (Chapter8.MathieuShadowRows.m22_code_fixed_eq
    D.sourceOrbit T A A₀ T.isPGroup' hAT hA₀T inf_le_right inf_le_right a hinj hfive hfive₀).2
  have hUT : (U.subgroupOf T).Normal := by rw [hUU]; exact hU₀T
  have hTU : (T : Subgroup G) ≤ normalizer (U : Set G) := by rw [hUU]; exact hTU₀
  have hKU : K ≤ normalizer (U : Set G) := by rw [hUU]; exact hKU₀
  have hK : (K.subgroupOf (normalizer (U : Set G))).IsCComponent := by rw [hUU]; exact hK₀
  have hRK : R ≤ K := by
    change localResidual L U ≤ K
    rw [hUU]
    exact hR₀K
  have hNK : normalizer (U : Set G) ≤ normalizer (K : Set G) := by rw [hUU]; exact hN₀K
  have hcomm : ⁅R,centralizer (U : Set G)⁆ ≤ R.pCoreIn 2 := by
    change ⁅localResidual L U, centralizer (U : Set G)⁆ ≤ (localResidual L U).pCoreIn 2
    rw [hUU]
    exact hcomm₀
  obtain ⟨hpair,hcore⟩ := local_factor_normalizes_pair_and_core L K U I D.sourceOrbit
    (T : Subgroup G) i.val i.property s.generate hcent hNK hQT
    D.sourceOrbit_component_normalizes D.sourceOrbit_weakClosure_setup.normalizes hcomm
  have hRI : R ≤ normalizer (I : Set G) := le_sup_left.trans hpair
  have hRP : R ≤ normalizer (I.pCoreIn 2 : Set G) := le_sup_left.trans hcore
  have hcommI : ⁅R,I⁆ ≤ R.pCoreIn 2 := (commutator_mono le_rfl hcent).trans hcomm
  obtain ⟨f,hfk,hsection⟩ := D.sourceOrbit_m22_code_five_section
    h.toHypothesis1221 d s hA hAT hfix hfour hfive
  have hsection' := hsection
  rcases hsection' with ⟨hRB,hRU,hBU,r,eB,hrsur,hrc,hrval,hact,hkernel,hdim⟩
  have hr := hfive
  rw [hA] at hr
  have hprod := selected_m22_code_full_product_action s hfix hcent hr hfour
    hRI hRU hcommI hRB hBU hkernel
  have hpa := selected_m22_code_pair_action s hprod hsection hcommI
  obtain ⟨hm,hc⟩ := selected_m22_code_multiplicity_cubic s hprod hpa hcommI
  exact ⟨hA,hAT,hfix,hfix.trans hker.symm,hcent,hfive,hfour,hUT,hTU,hcomm,hRI,hRP,
    ⟨K,hKU,hK,hRK,hNK,hquasi,hQT,hpair,hcore⟩,f,hfk,hsection,hprod,hpa,hm,hc⟩

/-- Every supplied parameter-one pair has the cubic quotient. -/
theorem sourceOrbit_m22_code_selected_small_quotient
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation)
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S) :
    Nonempty ((I ⧸ pCore 2 I) ≃* PSL(2,ZMod 2)) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,f,_,_,_,_,_,hc⟩ :=
    D.sourceOrbit_m22_code_selected_cubic_data h hmany hV hnon d hH s
  exact hc

/-- On the original M22-code orbit, every odd prime-power rotation inverted
by V⁺ has order three. The earlier-source order-two image premise is the
only additional input; the universal selected-pair premise is discharged. -/
theorem sourceOrbit_m22_code_odd_rotations_of_image_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (himage : Nat.card ((D.sourceOrbit.subgroupOf H).map
      (QuotientGroup.mk' (pCore 2 H))) = 2) :
    let W := (D.sourceOrbit.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))
    (∀ (v r : H ⧸ pCore 2 H), v ∈ W → v ≠ 1 →
      v*r*v⁻¹=r⁻¹ → ∀ (p a : ℕ), p.Prime → p ≠ 2 → 0 < a →
        orderOf r = p^a → orderOf r = 3) ∧
    ∀ (v g : H ⧸ pCore 2 H), v ∈ W → v ≠ 1 →
      ∀ (p a : ℕ), p.Prime → p ≠ 2 → 0 < a →
        orderOf (v*(g⁻¹*v*g)) = p^a → orderOf (v*(g⁻¹*v*g)) = 3 := by
  obtain ⟨h28,hchar⟩ := D.sourceOrbit_m22_code_hstar_setup h hmany hV hnon d hH
  have hrot : ∀ (v r : H ⧸ pCore 2 H),
      v ∈ (D.sourceOrbit.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) → v ≠ 1 →
      v*r*v⁻¹=r⁻¹ → ∀ (p a : ℕ), p.Prime → p ≠ 2 → 0 < a →
        orderOf r = p^a → orderOf r = 3 := by
    intro v r hv hv1 hi p a hp hp2 ha hr
    obtain ⟨I,i,S,s,⟨e⟩⟩ := selected_pair_of_inverted_prime_power h28
      (generalizedFitting_eq_pCore_of_selfCentralizing 2 hchar)
      (D.m24_restricted_quadraticRatio h.toHypothesis1221 hnon _)
      (D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).ti
      (D.sourceOrbit_normalizer_le h.toHypothesis1221) himage hp hp2 ha v r hv hv1 hr hi
    obtain ⟨e3⟩ := D.sourceOrbit_m22_code_selected_small_quotient h hmany hV hnon d hH s
    have horder : Nat.card (I ⧸ pCore 2 I) = 2*p^a := by
      rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card]
    have hthree : Nat.card (I ⧸ pCore 2 I) = 6 := by
      rw [Nat.card_congr (e3.trans
        Theory.SpecificGroups.BinaryDihedral.dihedralThreeEquivPSL2Two.symm).toEquiv,
        DihedralGroup.nat_card]
    exact hr.trans (by omega)
  refine ⟨hrot,?_⟩
  intro v g hv hv1 p a hp hp2 ha hr
  have hv2 : v*v=1 := by
    have hh := pow_card_eq_one' (x := (⟨v,hv⟩ :
      (D.sourceOrbit.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))))
    rw [himage] at hh
    exact congrArg Subtype.val (by simpa only [pow_two] using hh)
  have hvi : v⁻¹=v := inv_eq_of_mul_eq_one_left hv2
  have hi : v*(v*(g⁻¹*v*g))*v⁻¹=(v*(g⁻¹*v*g))⁻¹ := by
    simp only [mul_inv_rev,inv_inv,hvi,←mul_assoc,hv2,one_mul]
  exact hrot v (v*(g⁻¹*v*g)) hv hv1 hi p a hp hp2 ha hr

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
