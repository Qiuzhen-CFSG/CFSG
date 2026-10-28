module
public import CFSG.Quasithin.ChapterI.Section06To08.TIThompsonPair
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterFusionGeometrySource

/-!
# The Thompson-subgroup endgame for central involution fusion

The original centerless single-block hypotheses supply the TI property,
involution cover, and two-member maximum elementary family. Once the
commutator product of the conjugate span is placed in a conjugate of R,
the TI span and weak closure force the outside involution into R.

The product placement is the preceding source construction, retained here
as an explicit interface for the assembly proof.

Source: Aschbacher–Smith, original 2.4.21, printed p.536.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The original central-involution branch is impossible once its elementary
span and commutator product have been placed in a conjugate of R. All TI,
point-cover, elementary-pair, and Thompson premises come from the source setup. -/
theorem source_centerless_conjugate_product_exclusion
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype) = ⊥)
    (a g h : G) (haT : a∈(T : Subgroup G))
    (haR : a∉elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))
    (ha : a∈(distinguishedZ d).conjBy g)
    (V : Subgroup G) (hV : IsElementaryAbelian 2 V)
    (hc : Nat.card V = Nat.card (sourceModule (d.block.map d.H.subtype)))
    (hspan : V=conjugateSpanBy ((distinguishedZ d).conjBy g)
      ⁅elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype),zpowers a⁆)
    (hprod : ⁅elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype),zpowers a⁆ ⊔ V =
      (elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)).conjBy h) : False := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := elementaryAbelianMaxJ S
  let U := sourceModule (d.block.map d.H.subtype)
  have hL' := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) = R :=
    (d.single_natural_global_source hG T hST hsingle hL').2.1.symm
  obtain ⟨x,hxT,hxS⟩ := SetLike.exists_of_lt hST
  have hpair := ((source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique).2.2.2 x hxT hxS).2.2
  have hTI := source_distinguished_TI d hG T hST hsingle hL hM hTM hunique
  have hcover := source_centerless_involution_conjugate_cover d hG T hST hsingle hL hM hTM hunique hz
  have hU := source_module_maximum_elementary d hG T hST hsingle hL hM hTM hunique
  have hVmax : V∈elementaryAbelianMaxSubgroups (⊤ : Subgroup G) :=
    ⟨le_top,hV,fun B hB hBE => (hU.2.2 B hB hBE).trans hc.ge⟩
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (d.lemma_2_4_8_1 hG T hST hsingle hL').2.2
  have hK : ⁅R,zpowers a⁆≤R := le_normalizer_iff_commutator_le_left.mp
    (zpowers_le.mpr (hTR haT))
  have ha1 : a≠1 := fun he => haR (he ▸ R.one_mem)
  let : IsElementaryAbelian 2 (distinguishedZ d) :=
    (source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique).1
  let : IsElementaryAbelian 2 ((distinguishedZ d).conjBy g) := IsElementaryAbelian.map _
  have ha2 : a^2=1 := elemPow_eq_one_of_isElementaryAbelian a ha
  apply ChapterI.Section06To08.IsTISubgroup.not_conjugate_product_of_maxJ_pair
    T U (U.conjBy x⁻¹) (distinguishedZ d) V a g h hpair hTI ha ha1 ha2
  · rwa [hJT]
  · rwa [hJT]
  · rwa [hJT]
  · exact hVmax
  · rwa [hJT]
  · rwa [hJT]
end CFSG.Quasithin.Chapter2.LinearShadows.Single
