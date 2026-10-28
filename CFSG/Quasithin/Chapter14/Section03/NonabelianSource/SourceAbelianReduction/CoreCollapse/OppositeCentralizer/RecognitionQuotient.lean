module

public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.RecognitionCover
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup

/-!
# Recognizing the actual opposite-centralizer quotient

The marked component catalogue now selects G₂(2)′. The original quotient
C_G(w)/⟨w⟩ acts faithfully on this normal component. Its image contains the
inner automorphisms of order 6048 and has order divisible by 64, hence is the
full automorphism group of order 12096. The actual binary G₂ conjugation
isomorphism identifies this original quotient with the octonion group G₂(2).
No splitting of the whole centralizer is used.

Source: Aschbacher--Smith 14.3.22, printed p.999; refs/quasithin.pdf.
The actual binary automorphism theorem retains its imported ATLAS attribution.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G]
open Recognition Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.Candidates.ComponentStructure
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hc : CyclicTIInput F (sourceResidual M Mc)) {z d a : G}
    (s : CubicTriple F (sourceResidual M Mc) z d a)

include hG hempty hM hu hmany hcard e hnot hne hgP hgH hs hc s


/-- The two original local markings select the genuine G₂(2) derived component. -/
theorem source_triple_binary_derived_component
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    let C := ResidualFusion.C (tripleProduct d a)
    ∃ (D : Subgroup C) (α : MulAut D), IsComponent C D ∧
      (∀ x : D, ((α x : C) : G) = z * (x : G) * z⁻¹) ∧
      Nonempty (D ≃* commutator (Atlas.G2.Model (ZMod 2))) ∧
      α ∈ (MulAut.conj (G := D)).range ∧ orderOf α = 2 := by
  obtain ⟨D,α,P,hD,hα,hm,hi,ho,_⟩ := source_triple_final_three_marked_component
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  refine ⟨D,α,hD,hα,?_,hi,ho⟩
  cases hm with
  | five hm => exact (source_triple_not_alternatingFive
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hα hi ho hm).elim
  | two_cover hn hz hm => exact (source_triple_not_linearThreeFour_cover
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hn hz hm).elim
  | g2 hm => exact hm

/-- The faithful original quotient action contains all inner automorphisms.
Its Sylow order 64 forces it to be the full automorphism group of G₂(2)′,
hence the actual binary G₂ group. -/
theorem source_triple_quotient_recognition
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    Nonempty ((ResidualFusion.C (tripleProduct d a) ⧸ ResidualFusion.W (tripleProduct d a)) ≃*
      Atlas.G2.Model (ZMod 2)) := by
  let C := ResidualFusion.C (tripleProduct d a)
  let W := ResidualFusion.W (tripleProduct d a)
  obtain ⟨D,α,hD,hα,⟨eD⟩,hi,ho⟩ := source_triple_binary_derived_component
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  let := Atlas.G2.isSimple_commutator_binary
  let : IsSimpleGroup D := eD.isSimpleGroup
  let := hD.2
  have hzD : center D = ⊥ := center_eq_bot_of_simple_perfect
  have hDc : Nat.card D = 6048 := (Nat.card_congr eD.toEquiv).trans
    Atlas.G2.LieAutomorphismExtensions.card_binaryDerived
  have h16 : 16 ∣ Nat.card D := by rw [hDc]; norm_num
  let := source_triple_centerless_component_normal
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hzD h16
  obtain ⟨ρ,hρ,hρact⟩ := source_triple_normal_component_action
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hzD hα hi ho
  let eA := (MulAut.congr eD).trans Atlas.G2.LieAutomorphismExtensions.binaryAutomorphismEquiv.symm
  have hAc : Nat.card (MulAut D) = 12096 := (Nat.card_congr eA.toEquiv).trans
    Atlas.G2.LieAutomorphismExtensions.card_binaryFull
  have hin : (MulAut.conj (G := D)).range ≤ ρ.range := by
    rintro _ ⟨x,rfl⟩
    refine ⟨QuotientGroup.mk' W x,?_⟩
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact hρact x y
  have hinner : Nat.card ((MulAut.conj (G := D)).range) = 6048 := by
    rw [←Nat.card_congr (MonoidHom.ofInjective
      (MulAut.conj_injective_of_center_eq_bot hzD)).toEquiv,hDc]
  have hd : 6048 ∣ Nat.card ρ.range := hinner ▸ card_dvd_of_le hin
  obtain ⟨S,M₁,hS,hSc,_⟩ := source_triple_component_catalogue
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hw := (source_triple_local_geometry
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself).involution
  have hcore := source_triple_twoCore_eq
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have h64 := (S.mapSurjective (f := QuotientGroup.mk' W)
    (QuotientGroup.mk'_surjective _)).toSubgroup.card_subgroup_dvd_card
  rw [quotient_sylow_card hw hcore S hSc] at h64
  have h64r : 64 ∣ Nat.card ρ.range := by
    rw [←Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv]
    exact h64
  have hfull : 12096 ∣ Nat.card ρ.range := by
    have hh := Nat.lcm_dvd hd h64r
    norm_num at hh
    exact hh
  have hsur : Function.Surjective ρ := by
    apply MonoidHom.range_eq_top.mp
    apply eq_top_of_card_eq _
    apply Nat.dvd_antisymm
    · exact ρ.range.card_subgroup_dvd_card
    · rwa [hAc]
  exact ⟨(MulEquiv.ofBijective ρ ⟨hρ,hsur⟩).trans eA⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
