module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Swapped.Odd
public import Theory.SpecificGroups.PSL2.SmallSylowRadical

/-!
# The nonzero residual radical excludes the full-intersection odd case

The original cubic complement generates the residual radical by
commutators. In the product of two small-congruence PSL₂ groups, the
actual factor exchange forces this radical image to be either trivial or
the full quotient Sylow. In the latter case the cubic plane fills its
normalizer, and preservation of the marked full intersection preserves
the original two-residual. This contradicts its strict normal closure.

Thus every remaining contrary ambient-Sylow configuration has
O₂(X) contained in O₂(⟨K^T⟩), full marked quotient Sylow intersection,
and a factor PSL₂(p) with p congruent to three or five modulo eight.
The actual component, full swapped input, maximality and Fundamental Setup
are retained. This is a precise remaining case, not a proof of the Sylow
statement or of pure fusion. Its exclusion and the point-core/closure
argument remain with this task. The original fixed-subgroup MS premise
stays with `qt-rank-two-ms93` and final `qt-d-double-natural-centralizers`.
The intrinsic calculation adapts BinaryThreeAction/OddSmallRadical to the
same quotient and point-Sylow conventions used throughout this family.
Source: Aschbacher--Smith 12.1.4, pp.790--791; compare 10.2.5, p.748.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi
open Chapter1 Chapter1.XiEmbedding InvariantThree
variable {G : Type*} [Group G] [Finite G]

/-- In a small odd-prime square with full quotient intersection, a nonzero
original residual radical determines the entire Sylow normalizer. -/
theorem normalizes_of_small_odd_swapped_positive (T : Sylow 2 G) {X A H I U : Subgroup G}
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) X A H I)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hmod : p % 8 = 3 ∨ p % 8 = 5)
    (hfull : quotientImage (componentOrbit I (T : Subgroup G)) U =
      quotientImage (componentOrbit I (T : Subgroup G)) (T : Subgroup G))
    (hpos : quotientImage (componentOrbit I (T : Subgroup G)) (X.pCoreIn 2) ≠ ⊥) :
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
  have hTC : (T : Subgroup G) ≤ normalizer (X.pCoreIn 2 : Set G) :=
    hs.invariant.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  obtain ⟨e,a,b,hswap⟩ := swapped_quotient_subgroup T hs (X.pCoreIn 2) hTC
  have hpc := hi.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput e)
  let ep := complementEquiv hi hAK
  have hcard : Nat.card (quotientImage K A) = 9 :=
    (Nat.card_congr ep.toEquiv).symm.trans hpc.2
  have hc : ⁅quotientImage K (X.pCoreIn 2),quotientImage K A⁆ =
      quotientImage K (X.pCoreIn 2) := by
    have hCK : X.pCoreIn 2 ≤ K := (pCoreIn_le 2 X).trans hXK
    have hc : ⁅(X.pCoreIn 2).subgroupOf K,A.subgroupOf K⁆ = (X.pCoreIn 2).subgroupOf K := by
      apply map_injective K.subtype_injective
      rw [map_commutator,map_subgroupOf_eq_of_le hCK,map_subgroupOf_eq_of_le hAK]
      exact hi.core_commutator.symm
    change ⁅((X.pCoreIn 2).subgroupOf K).map _,(A.subgroupOf K).map _⁆ =
      ((X.pCoreIn 2).subgroupOf K).map _
    rw [←map_commutator,hc]
  have hCS : quotientImage K (X.pCoreIn 2) ≤ (S : Subgroup (XiQuotient K)) := by
    rw [hS]
    exact map_mono (subgroupOf_mono K hi.core_le_two_group)
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hm
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p,1,hp,ho,by decide,by simpa using hF⟩
  have h8 := Theory.PSL2.not_eight_dvd_card_of_small_mod_eight (hF ▸ ho) (hF ▸ hmod)
  have hCF : quotientImage K (X.pCoreIn 2) = (S : Subgroup (XiQuotient K)) :=
    (Theory.PSL2.small_pair_radical_eq_or_bot eF e hodd h8 S
      (quotientImage K (X.pCoreIn 2)) (quotientImage K A) hCS
      (hi.odd_complement.isPGroup.of_equiv ep) hcard hc
      (SylowNormalizerAction.projection_card_eq_of_swapped _ a b hswap)).resolve_left hpos
  rw [hCF] at hc
  have hAN : quotientImage K A ≤ normalizer (S : Set (XiQuotient K)) :=
    le_normalizer_iff_commutator_le_left.mpr hc.le
  have hnormal := Theory.PSL2.small_pair_normalizer_eq_join (e.trans (eF.prodCongr eF))
    hodd h8 S (quotientImage K A) (hi.odd_complement.isPGroup.of_equiv ep) hcard hAN
  have hcT : K.pCoreIn 2 ≤ (T : Subgroup G) := by
    have h1 := pCoreIn_mono_of_normalizes (p := 2)
      (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left) (sup_le K.le_normalizer hTK)
    have h2 := pCoreIn_le_sylow (K ⊔ (T : Subgroup G))
      (T.subtype (show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right))
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right)] using h1.trans h2
  let J := X ⊔ ((T : Subgroup G) ⊓ K)
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
  intro g hg
  let a := pCoreNormalizerAction 2 K ⟨g,hHKn hg.1⟩
  have ha : (S : Subgroup (XiQuotient K)).map a.toMonoidHom = S := by
    rw [hS,←hfull]
    exact pCoreNormalizerAction_preserves_image 2 K U ⟨g,hHKn hg.1⟩ hg.2
  have hN : (normalizer (S : Set (XiQuotient K))).map a.toMonoidHom =
      normalizer (S : Set (XiQuotient K)) := by
    change (normalizer ((S : Subgroup (XiQuotient K)) : Set (XiQuotient K))).map _ = _
    rw [map_equiv_normalizer_eq,ha]
    simp only [Sylow.coe_coe]
  have himage : (quotientImage K X).map a.toMonoidHom = quotientImage K X := by
    rw [←hres,←hjoin,←hnormal,map_embedded_pResidual,hN]
  exact mem_normalizer_of_pCoreNormalizerAction_preserves_image K X hXK hi.perfect
    (hcT.trans hi.invariant) ⟨g,hHKn hg.1⟩ himage
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Every remaining swapped obstruction has full quotient Sylow intersection
and its original residual radical lies in the component-orbit two-core. -/
theorem doubleNatural_four_pure_collapsed_swapped_of_many_of_omega_fixed
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
          (∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (XiQuotient K) 2 p ∧
            (p % 8 = 3 ∨ p % 8 = 5)) ∧
          quotientImage (componentOrbit K (T : Subgroup G)) (B.pointSylow w) =
            quotientImage (componentOrbit K (T : Subgroup G)) (T : Subgroup G) ∧
          X.pCoreIn 2 ≤ (componentOrbit K (T : Subgroup G)).pCoreIn 2 ∧
          ¬ ClassicalGroup.IsPSL (XiQuotient K) 2 4 ∧
          K ∈ Chapter1.LStar G (T : Subgroup G) ∧
          K ∈ MainForward.faithfulLocalComponents T ∧
          Nonempty (Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T K) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf hne
  obtain ⟨P,hlt,hPC,hPM,hPN,hiT,hH,hHN,hout,A,K,hs,he,hstrict,hodd,hfull,hA5,hmax,hfaith,hFS⟩ :=
    D.doubleNatural_four_pure_small_odd_swapped_of_many_of_omega_fixed h hmany B S w hw hp hfix hf hne
  let X := PureFourXi.residual T L
  let H := (P : Subgroup G) ⊔ (X ⊔ (T : Subgroup G))
  let Y := componentOrbit K (T : Subgroup G)
  have hzero : quotientImage Y (X.pCoreIn 2) = ⊥ := by
    by_contra hpos
    obtain ⟨p,hp',ho,hm,hmod⟩ := hodd
    have hNX := PureFourXi.normalizes_of_small_odd_swapped_positive T hs hp' ho hm hmod hfull hpos
    have hHX : H ≤ normalizer (X : Set G) :=
      sup_le ((le_inf le_sup_left hPN).trans hNX)
        (sup_le X.le_normalizer hs.invariant)
    exact hstrict.not_ge (he ▸ conjugateSpanBy_le le_rfl hHX)
  have hcore : X.pCoreIn 2 ≤ Y.pCoreIn 2 := by
    have hXY : X.pCoreIn 2 ≤ Y := (pCoreIn_le 2 X).trans hstrict.le
    have hk : (X.pCoreIn 2).subgroupOf Y ≤ pCore 2 Y := by
      have hh := (Subgroup.map_eq_bot_iff _).mp hzero
      rwa [QuotientGroup.ker_mk'] at hh
    intro x hx
    exact mem_map_of_mem Y.subtype (hk (show (⟨x,hXY hx⟩ : Y) ∈ (X.pCoreIn 2).subgroupOf Y from hx))
  exact ⟨P,hlt,hPC,hPM,hPN,hiT,hH,hHN,hout,A,K,hs,he,hstrict,hodd,hfull,hcore,hA5,hmax,hfaith,hFS⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
