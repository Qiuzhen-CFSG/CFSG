module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourSolvable
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourOddProducts
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianCoordinates
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceDihedralSelection
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Odd rotations on the original chosen Hermitian module

Every parameter-one pair on the given chosen module has an S₃ or D₁₀
quotient: its own fixed four-space, containing component and faithful
multiplicity action are constructed from the original tensor marking.
The selected positive-closure pair places V⁺ at order two in H/O₂(H).
Its image survives the full maximal core, and the original maximal subgroup
maps onto its exact involution centralizer.

For each odd prime-power rotation inverted by V⁺, the actual pair-lifting
construction preserves its order. Applying the universal selected-pair
calculation forces that order to be three or five, including the literal
products v⁺ · (v⁺)^g. All inputs come from the original chosen module and
half-field tensor data; no parabolic model-list conclusion is assumed.
The nonsolvable model sieve and subsequent chief-section exclusions remain
separate source steps.

Source: Aschbacher–Smith 8.2.9, printed p.720, refs/quasithin.pdf
(1 March 2004 manuscript), using 8.2.5–8 and E.2.7–9.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.Normalizer.SmallOvergroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
set_option backward.isDefEq.respectTransparency false

/-- Every parameter-one pair on the original Hermitian module has the cubic
or quintic quotient. Its own four-space and containing component are constructed. -/
theorem sourceOrbit_hermitian_selected_small_quotient
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
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S) :
    Nonempty ((I ⧸ pCore 2 I) ≃* PSL(2,ZMod 2)) ∨
      Nonempty ((I ⧸ pCore 2 I) ≃* DihedralGroup 5) := by
  obtain ⟨hn,_⟩ := D.sourceOrbit_hermitian_tensor_field_four
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel
  subst hn
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree hfield hmodel
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h.toHypothesis1221
  obtain ⟨_,_,_,hu,_,_,hTU,hIC,_⟩ := selected_one_fixed_subgroup s
    D.sourceOrbit_weakClosure_setup 1 (D.hermitianOrbitCoordinates 1 d) j hj he
  let U := D.sourceOrbit ⊓ centralizer
    (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le
    (show U ≤ D.sourceOrbit from inf_le_left)
  have hUne : U ≠ ⊥ := by
    intro hz
    change rank U = 4 at hu
    rw [hz,Representation.BinaryOffender.rank_bot] at hu
    omega
  obtain ⟨_,hc,_⟩ := D.sourceOrbit_hermitian_selected_fixed_centralizer h.toHypothesis1221 d s
  obtain ⟨K,hKU,hK,hRK,hNK⟩ := D.sourceOrbit_hermitian_fixed_overcomponent
    h.toHypothesis1221 U inf_le_left hUne hTU hc
  obtain ⟨_,hcomm,hRI,hRP⟩ := D.sourceOrbit_hermitian_selected_component_pair_normalizer
    h hmany hV hs hnon B C eQ 1 hdegree hfield hmodel s hKU hK hRK hNK
  have hp := D.sourceOrbit_hermitian_selected_product_action h.toHypothesis1221 d s
    (le_sup_left.trans hRI) hcomm
  have hn := D.sourceOrbit_hermitian_selected_natural_action h.toHypothesis1221 d s
    (le_sup_left.trans hRP)
  have hcommI := (commutator_mono (le_refl _) hIC).trans hcomm
  have hpair := selected_one_natural_pair_action s hp hn hcommI
  exact (selected_one_multiplicity_cases s hp hpair hcommI).2

/-- The full H/O₂(H) has its marked involution-centralizer maximal subgroup.
Every odd prime-power rotation inverted by V⁺ has exact order three or five. -/
theorem sourceOrbit_hermitian_tensor_parabolic_odd_rotations
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
    (hw : 0 < globalW D.sourceOrbit T)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    n = 1 ∧ B.degree = 2 ∧ globalW D.sourceOrbit T = 1 ∧
      ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
        Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
        I.pCoreIn 2 = I ⊓ H.pCoreIn 2 ∧ primeRank 3 H ≤ 1 ∧ primeRank 5 H ≤ 1 ∧
        let W := (D.sourceOrbit.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))
        Nat.card W = 2 ∧
        Nat.card (starImage (normalizer (L : Set G)) H D.sourceOrbit) = 2 ∧
        ((normalizer (L : Set G)).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) =
          centralizer (W : Set (H ⧸ pCore 2 H)) ∧
        (∀ (v r : H ⧸ pCore 2 H), v ∈ W → v ≠ 1 →
          v*r*v⁻¹=r⁻¹ → ∀ (p a : ℕ), p.Prime → p ≠ 2 → 0 < a →
            orderOf r = p^a → orderOf r = 3 ∨ orderOf r = 5) ∧
        ∀ (v g : H ⧸ pCore 2 H), v ∈ W → v ≠ 1 →
          ∀ (p a : ℕ), p.Prime → p ≠ 2 → 0 < a →
            orderOf (v*(g⁻¹*v*g)) = p^a →
              orderOf (v*(g⁻¹*v*g)) = 3 ∨ orderOf (v*(g⁻¹*v*g)) = 5 := by
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  have hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs := by
    refine ⟨B,C,⟨eQ⟩,?_⟩
    dsimp only
    rw [hdegree]
    exact ⟨NeZero.pos n,hfield,d.linearEquiv.finrank_eq.trans (finrank_binary n),hmodel⟩
  obtain ⟨h28,hchar⟩ := D.sourceOrbit_hermitian_hstar_setup h hmany hV hnon hs hrow hH
  obtain ⟨hn,hB,hw1,I,i,S,s,_,_,_,_,_,K,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,
    h3,h5,_,_,himage,hPQ,_⟩ :=
    D.sourceOrbit_hermitian_tensor_selected_parabolic_core
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw hH
  have hVH := h28.le_sylow.trans h28.le_ambient
  let : IsElementaryAbelian 2 (D.sourceOrbit.subgroupOf H) := IsElementaryAbelian.subgroupOf hVH
  obtain ⟨R,hR,hP,hM⟩ := h28.minimal
  obtain ⟨_,_,hcore,hout⟩ := intrinsic_source_data h28 R hR hP hM
  have hstar := (parabolic_involution_star_transport R hP (D.sourceOrbit.subgroupOf H)
    hcore hout himage).1
  have hmax : ChapterB.minimalParabolicMax R hP ≤
      normalizer (D.sourceOrbit.subgroupOf H : Set H) := by
    rw [←hM,←subgroupOf_normalizer_eq hVH]
    intro x hx
    exact D.sourceOrbit_hstar_intersection_normalizes h hmany hV hnon hH ⟨x.property,hx⟩
  have hcent := parabolic_maximal_image_involution_centralizer R hP
    (D.sourceOrbit.subgroupOf H) hmax himage
  rw [←hM] at hcent
  have hstar2 : Nat.card (starImage (normalizer (L : Set G)) H D.sourceOrbit) = 2 := by
    change Nat.card ((D.sourceOrbit.subgroupOf H).map
      (QuotientGroup.mk' ((normalizer (L : Set G)).subgroupOf H).normalCore)) = 2
    have hj : ChapterB.minimalParabolicCore R hP =
        ((normalizer (L : Set G)).subgroupOf H).normalCore := by
      change (ChapterB.minimalParabolicMax R hP).normalCore = _
      rw [←hM]
    let e := QuotientGroup.quotientMulEquivOfEq hj
    have he : ((D.sourceOrbit.subgroupOf H).map
        (QuotientGroup.mk' (ChapterB.minimalParabolicCore R hP))).map e.toMonoidHom =
        (D.sourceOrbit.subgroupOf H).map
          (QuotientGroup.mk' ((normalizer (L : Set G)).subgroupOf H).normalCore) := by
      rw [map_map]
      congr 1
    exact (Nat.card_congr ((e.subgroupMap _).trans
      (MulEquiv.subgroupCongr he)).toEquiv).symm.trans hstar
  have hrot : ∀ (v r : H ⧸ pCore 2 H),
      v ∈ (D.sourceOrbit.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) → v ≠ 1 →
      v*r*v⁻¹=r⁻¹ → ∀ (p a : ℕ), p.Prime → p ≠ 2 → 0 < a →
        orderOf r = p^a → orderOf r = 3 ∨ orderOf r = 5 := by
    intro v r hv hv1 hi p a hp hp2 ha hr
    obtain ⟨I',i',S',s',⟨e⟩⟩ := selected_pair_of_inverted_prime_power h28
      (generalizedFitting_eq_pCore_of_selfCentralizing 2 hchar)
      (D.sourceOrbit_restricted_quadraticRatio_gt_one h.toHypothesis1221 hnon _)
      (D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).ti
      (D.sourceOrbit_normalizer_le h.toHypothesis1221) himage hp hp2 ha v r hv hv1 hr hi
    have hc : Nat.card (I' ⧸ pCore 2 I') = 2*p^a := by
      rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card]
    rcases D.sourceOrbit_hermitian_selected_small_quotient
        h hmany hV hs hnon B C eQ n hdegree hfield hmodel s' with he3 | he5
    · obtain ⟨e3⟩ := he3
      have hthree : Nat.card (I' ⧸ pCore 2 I') = 6 := by
        rw [Nat.card_congr (e3.trans
          Theory.SpecificGroups.BinaryDihedral.dihedralThreeEquivPSL2Two.symm).toEquiv,
          DihedralGroup.nat_card]
      exact Or.inl (hr.trans (by omega))
    · obtain ⟨e5⟩ := he5
      have hfive : Nat.card (I' ⧸ pCore 2 I') = 10 := by
        rw [Nat.card_congr e5.toEquiv,DihedralGroup.nat_card]
      exact Or.inr (hr.trans (by omega))

  refine ⟨hn,hB,hw1,I,i,S,s,hPQ,h3,h5,himage,hstar2,hcent,hrot,?_⟩
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
