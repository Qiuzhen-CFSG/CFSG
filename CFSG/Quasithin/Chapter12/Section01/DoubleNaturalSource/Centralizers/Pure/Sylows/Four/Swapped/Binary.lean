module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Swapped.Input
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.BinaryResidual

/-!
# Excluding all binary swapped factors, including A₅

The actual component-orbit quotient is a square of binary PSL₂ factors.
The solvable Sylow overgroup lies in the product of its Borels. Its
normal Sylow and the original core interval identify the marked interval
with the full quotient Sylow. The cubic plane and the three-rank bound
then force preservation of the parabolic join and its two-residual.
Perfect residual lifting recovers normalization of the original X.
Generation by the escaping Sylow and XT contradicts the strict normal
closure of X. The argument applies at field order four, so A₅ is included.

Consequently each remaining obstruction has an odd-prime PSL₂ factor;
its non-A₅ quotient gives genuine moved-component maximality and an
original Fundamental Setup. These are reductions, not the ambient Sylow
conclusion. The original fixed-subgroup MS premise remains explicit, with
`qt-rank-two-ms93` and final owner `qt-d-double-natural-centralizers`.
The remaining odd case and the pure-point closure stay with this task.
The intrinsic calculation adapts the proved BinaryThreeAction/Even
application of the Chapter 1 binary residual-preservation theorem.
Source: Aschbacher--Smith 12.1.4, pp.790--791; the Borel calculation is
1.3.4, p.510, and residual lifting is also used in 10.2.5, p.748.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi
open Chapter1 Chapter1.XiEmbedding InvariantThree
variable {G : Type*} [Group G] [Finite G]

/-- The original residual is preserved in every binary rank-one square,
including PSL₂(4); the core interval uses the original ambient subgroups. -/
theorem normalizes_of_binary_swapped (T : Sylow 2 G) {X A H I U : Subgroup G}
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) X A H I)
    (hUT : U ≤ (T : Subgroup G)) (hcore : (X ⊔ (T : Subgroup G)).pCoreIn 2 ≤ U)
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 (2^n)) :
    H ⊓ normalizer (U : Set G) ≤ normalizer (X : Set G) := by
  let K := componentOrbit I (T : Subgroup G)
  have hi := hs.toLocalInput
  have hKH : K ≤ H := SwappedSylow.orbit_le_overgroup hs.toSwappedInput
  have hHKn : H ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKH).mp hs.orbit_normal
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hi.overgroup
  have hTK := hTH.trans hHKn
  have hXK : X ≤ K := hi.le_of_complement_le hs.complement_le_orbit hHKn
  have hAK : A ≤ K := hs.complement_le_orbit
  obtain ⟨S,hS⟩ := component_quotient_sylow hs.sylow_two hKH hs.orbit_normal
  let hA := fun (Y : Type _) [Group Y] [Finite Y] => ChapterA.Section02.theoremA_knownSimple (G := Y)
  let hC := fun (Y : Type _) [Group Y] [Finite Y] => ChapterA.Section02.theoremC_knownSimple (G := Y)
  obtain ⟨hindex,hmodel⟩ := SwappedSylow.nonnormal_model_of_theoremsAC hA hC hs.toSwappedInput
  have hsimple := SwappedFactorsProof.quotient_simple hs.toSwappedInput hmodel
  obtain ⟨e⟩ := SwappedFactorsProof.quotient_product
    ChapterA.Section03.CComponentCommutation.universal_A_3_7 hs.toSwappedInput hindex hsimple
  have hpc := hi.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput e)
  let : IsElementaryAbelian 3 A := hpc.1
  let ep := complementEquiv hi hAK
  let : IsElementaryAbelian 3 (quotientImage K A) :=
    IsElementaryAbelian.of_surjective ep.toMonoidHom ep.surjective
  have hcard : Nat.card (quotientImage K A) = 9 :=
    (Nat.card_congr ep.toEquiv).symm.trans hpc.2
  have hrank : primeRank 3 (XiQuotient K) ≤ 2 :=
    (SwappedSylow.orbit_quotient_sqtk hs.toSwappedInput).stronglyQuasithin 3 (by decide) (by decide)
  let : Group.IsSolvable (quotientImage K A ⊔ (S : Subgroup (XiQuotient K)) : Subgroup _) := by
    rw [hS]
    exact SwappedSylow.quotient_solvable hs.toSwappedInput
  have hcT : K.pCoreIn 2 ≤ (T : Subgroup G) := by
    have h1 := pCoreIn_mono_of_normalizes (p := 2)
      (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left) (sup_le K.le_normalizer hTK)
    have h2 := pCoreIn_le_sylow (K ⊔ (T : Subgroup G))
      (T.subtype (show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right))
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right)] using h1.trans h2
  let J := X ⊔ ((T : Subgroup G) ⊓ K)
  have hJN : X ⊔ (T : Subgroup G) ≤ normalizer (J : Set G) := by
    apply sup_le ((show X ≤ J from le_sup_left).trans J.le_normalizer)
    exact (le_inf hi.invariant
      ((le_inf (T : Subgroup G).le_normalizer hTK).trans
        inf_normalizer_le_normalizer_inf)).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hJU : J.pCoreIn 2 ≤ U :=
    (pCoreIn_mono_of_normalizes (sup_le le_sup_left (inf_le_left.trans le_sup_right)) hJN).trans hcore
  have hquotcore : (quotientImage K X ⊔ quotientImage K (T : Subgroup G)).pCoreIn 2 ≤
      quotientImage K U := by
    let F := X.subgroupOf K ⊔ (T : Subgroup G).subgroupOf K
    have hF : F.map K.subtype = J := by
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hXK,subgroupOf_map_subtype]
    have hc : F.pCoreIn 2 ≤ U.subgroupOf K := by
      apply map_le_iff_le_comap.mp
      rw [map_pCoreIn_of_injective 2 F K.subtype K.subtype_injective,hF]
      exact hJU
    have hh := map_mono (f := QuotientGroup.mk' (pCore 2 K)) hc
    rw [map_pCoreIn_of_ker_isPGroup _ (by
      rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)] at hh
    simpa only [F,quotientImage,Subgroup.map_sup] using hh
  have hres : (pResidual 2 (quotientImage K X ⊔ quotientImage K (T : Subgroup G) :
      Subgroup (XiQuotient K))).map
      (quotientImage K X ⊔ quotientImage K (T : Subgroup G)).subtype = quotientImage K X := by
    have hp : IsPPerfect 2 (X.subgroupOf K) := hi.perfect.of_surjective
      (subgroupOfEquivOfLe hXK).symm.toMonoidHom (subgroupOfEquivOfLe hXK).symm.surjective
    have hnormal : (T : Subgroup G).subgroupOf K ≤ normalizer (X.subgroupOf K : Set K) := by
      rw [←subgroupOf_normalizer_eq hXK]
      exact comap_mono hi.invariant
    have he := embedded_pResidual_join_pGroup (X.subgroupOf K) ((T : Subgroup G).subgroupOf K)
      hp T.isPGroup'.comap_subtype hnormal
    have hh := congrArg (Subgroup.map (QuotientGroup.mk' (pCore 2 K))) he
    rw [map_embedded_pResidual,Subgroup.map_sup] at hh
    exact hh
  have hjoin : quotientImage K A ⊔ (S : Subgroup (XiQuotient K)) =
      quotientImage K X ⊔ quotientImage K (T : Subgroup G) := by
    have hcX : X.pCoreIn 2 ≤ (T : Subgroup G) := le_sup_left.trans hi.normalizer_factor.symm.le
    have he : A ⊔ ((T : Subgroup G) ⊓ K) = J := by
      apply le_antisymm (sup_le_sup_right (le_sup_right.trans hi.complement.le) _)
      apply sup_le _ le_sup_right
      rw [←hi.complement]
      exact sup_le ((le_inf hcX ((pCoreIn_le 2 X).trans hXK)).trans le_sup_right) le_sup_left
    have hs := congrArg (fun F : Subgroup G => F.subgroupOf K) he
    change _ = (X ⊔ ((T : Subgroup G) ⊓ K)).subgroupOf K at hs
    rw [subgroupOf_sup hAK inf_le_right,subgroupOf_sup hXK inf_le_right] at hs
    have hTi : ((T : Subgroup G) ⊓ K).subgroupOf K = (T : Subgroup G).subgroupOf K := by
      ext x
      exact and_iff_left x.property
    rw [hTi] at hs
    rw [hS]
    simpa only [quotientImage,Subgroup.map_sup] using
      congrArg (Subgroup.map (QuotientGroup.mk' (pCore 2 K))) hs
  have hUS : quotientImage K U ≤ (S : Subgroup (XiQuotient K)) := by
    rw [hS]
    exact map_mono (comap_mono hUT)
  intro g hg
  let a := pCoreNormalizerAction 2 K ⟨g,hHKn hg.1⟩
  have ha : (quotientImage K U).map a.toMonoidHom = quotientImage K U :=
    pCoreNormalizerAction_preserves_image 2 K U ⟨g,hHKn hg.1⟩ hg.2
  have hpres := SwappedSylow.binary_pair_preserves_join hn hm e S (quotientImage K A)
    (quotientImage K U) hcard hrank (hjoin.symm ▸ hquotcore) hUS a ha
  have himage : (quotientImage K X).map a.toMonoidHom = quotientImage K X := by
    rw [←hres,←hjoin,map_embedded_pResidual,hpres]
  exact mem_normalizer_of_pCoreNormalizerAction_preserves_image K X hXK hi.perfect
    (hcT.trans hi.invariant) ⟨g,hHKn hg.1⟩ himage
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Binary rank-one squares, including A₅, cannot occur. Every remaining
obstruction has an odd-prime factor, genuine maximality and a Fundamental Setup. -/
theorem doubleNatural_four_pure_odd_swapped_of_many_of_omega_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      omegaCenterIn (B.pointSylow w) ⊓ centralizer (L : Set G) ≠ ⊥ →
      let X := PureFourXi.residual T L
      ∃ P : Sylow 2 G, B.pointSylow w < (P : Subgroup G) ∧
        (P : Subgroup G) ≤ B.pointCentralizer w ∧
        (P : Subgroup G) ⊓ normalizer (L : Set G) = B.pointSylow w ∧
        (P : Subgroup G) ≤ normalizer (B.pointSylow w : Set G) ∧
        (B.pointSylow w).relIndex (T : Subgroup G) = 2 ∧
        let H := (P : Subgroup G) ⊔ (X ⊔ (T : Subgroup G))
        H ∈ HOver G ((X ⊔ (T : Subgroup G) : Subgroup G) : Set G) ∧
        H ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
        ¬ H ≤ normalizer (L : Set G) ∧
        ∃ A : Sylow 3 X, ∃ K : Subgroup G,
          SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) X
            ((A : Subgroup X).map X.subtype) H K ∧
          conjugateSpanBy X H = componentOrbit K (T : Subgroup G) ∧
          X < componentOrbit K (T : Subgroup G) ∧
          (∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (XiQuotient K) 2 p) ∧
          ¬ ClassicalGroup.IsPSL (XiQuotient K) 2 4 ∧
          K ∈ Chapter1.LStar G (T : Subgroup G) ∧
          K ∈ MainForward.faithfulLocalComponents T ∧
          Nonempty (Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T K) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf hne
  obtain ⟨P,hlt,hPC,hPM,hPN,hiT,hH,hHN,hout,A,K,hs,he,hstrict⟩ :=
    D.doubleNatural_four_pure_swapped_input_of_many_of_omega_fixed h hmany B S w hw hp hfix hf hne
  let X := PureFourXi.residual T L
  let H := (P : Subgroup G) ⊔ (X ⊔ (T : Subgroup G))
  have hc : (X ⊔ (T : Subgroup G)).pCoreIn 2 ≤ B.pointSylow w := by
    rw [(D.doubleNatural_four_pure_xi_of_many h hmany B S w hw hp hfix hf).2.1]
    exact D.doubleNatural_four_pure_normalizer_core_le_of_many h hmany B S w hw hp hfix hf
  have hnot (n : ℕ) (hn : 2 ≤ n)
      (hm : ClassicalGroup.IsPSL (XiQuotient K) 2 (2^n)) : False := by
    have hNX := PureFourXi.normalizes_of_binary_swapped T hs inf_le_left hc hn hm
    have hHX : H ≤ normalizer (X : Set G) :=
      sup_le ((le_inf le_sup_left hPN).trans hNX)
        (sup_le X.le_normalizer hs.invariant)
    exact hstrict.not_ge (he ▸ conjugateSpanBy_le le_rfl hHX)
  have hA5 : ¬ ClassicalGroup.IsPSL (XiQuotient K) 2 4 := hnot 2 (by decide)
  let hA := fun (Y : Type _) [Group Y] [Finite Y] => ChapterA.Section02.theoremA_knownSimple (G := Y)
  let hC := fun (Y : Type _) [Group Y] [Finite Y] => ChapterA.Section02.theoremC_knownSimple (G := Y)
  obtain ⟨_,_,hm⟩ := SwappedSylow.embedding_of_theoremsAC hA hC hs
  have hodd : ∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (XiQuotient K) 2 p := by
    rcases hm with ⟨n,hn,_,hm⟩ | hm
    · have hn0 : n ≠ 0 := by
        intro hn0
        obtain ⟨F,_,_,hF,_⟩ := hm
        have hh := Finite.one_lt_card (α := F)
        simp only [hn0,pow_zero] at hF
        omega
      have hn2 : 2 ≤ n := by obtain ⟨k,hk⟩ := hn; omega
      exact (hnot n hn2 hm).elim
    · exact hm
  have hKL := mem_L_of_cComponent hH.1 hs.sylow_two hs.component.1 hs.component.2
  have hmove : K < conjugateSpanBy K (T : Subgroup G) := by
    refine lt_of_le_of_ne (le_conjugateSpanBy K (T : Subgroup G)) ?_
    intro heq
    have hn := le_normalizer_conjugateSpanBy K (T : Subgroup G)
    rw [←heq] at hn
    exact hs.not_invariant hn
  have hmax := Chapter1.Section02.MovedMaximality.moved_local_mem_LStar
    h.simpleQTKE T hKL hmove hA5
  have hfaith := (Terminal.lemma_1_3_9_two_source h.simpleQTKE T
    (D.doubleNatural_four_pure_xi_faithful_of_many h hmany B S w hw hp hfix hf) hKL hstrict.le).2
  exact ⟨P,hlt,hPC,hPM,hPN,hiT,hH,hHN,hout,A,K,hs,he,hstrict,hodd,hA5,hmax,hfaith,
    Chapter3.Section02.source_exists_fundamentalSetup h.simpleQTKE T K hmax hfaith.2 hs.quasisimple⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
