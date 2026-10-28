module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Swapped.ModuleGeometry
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.XiModule

/-!
# The original module as a normal subgroup of the containing cores

The strengthened containment W <= O₂(X) puts W inside every core in the
checked interval. All these cores normalize W through the original LT
action, and their nontrivial radical image excludes commutativity. Since
W is elementary, its fixed subgroup in each core is exactly its intersection
with that core's central omega subgroup; this intersection has order sixteen.

The final application preserves the full original contrary-Sylow witness,
the literal swapped quotient, core indices and Fundamental Setup. It proves
nonabelianity also for O₂(X) and O₂(K₀), strengthening the earlier exclusion
of an abelian O₂(H). It does not exclude the remaining nonabelian case.
That exclusion and the ambient Sylow, core, fusion and closure assembly stay
with qt-d-double-natural-pure-fusion. The explicit fixed-subgroup premise
remains with qt-rank-two-ms93 and final qt-d-double-natural-centralizers.
Source: Aschbacher--Smith 12.1.4, printed pp.790--791, and H.9.3(4), p.391.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {B : DoubledBranch T L V 4}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
  (S : B.SourceModel)

include S in
/-- The original W is a normal subgroup of every nonabelian core in the interval. -/
theorem four_core_interval_orbit_normal
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hWT : componentOrbit V (T : Subgroup G) ≤ (T : Subgroup G))
    (hm : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (componentOrbit V (T : Subgroup G) : Set G))
    {R : Subgroup G} (hlo : (PureFourXi.residual T L).pCoreIn 2 ≤ R)
    (hhi : R ≤ (PureFourXi.normalizerJoin T L).pCoreIn 2) :
    componentOrbit V (T : Subgroup G) ≤ R ∧
      ((componentOrbit V (T : Subgroup G)).subgroupOf R).Normal ∧
      ¬ IsMulCommutative R := by
  have hWR := (S.four_orbit_le_xi_core hTM hWT hm).trans hlo
  have hRW : R ≤ normalizer (componentOrbit V (T : Subgroup G) : Set G) := by
    rw [B.orbit_eq]
    exact (hhi.trans ((pCoreIn_le 2 _).trans
      (inf_le_right.trans (sup_le L.le_normalizer hTM)))).trans
        (le_normalizer_componentOrbit _ _)
  refine ⟨hWR,(normal_subgroupOf_iff_le_normalizer hWR).mpr hRW,?_⟩
  intro hr
  let := hr
  exact S.four_xi_core_moves hTM hWT hm
    (hlo.trans ((le_centralizer R).trans (centralizer_le hWR)))

include S in
/-- Its intersection with the actual central omega subgroup has order sixteen. -/
theorem four_core_interval_central_omega_card
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hWT : componentOrbit V (T : Subgroup G) ≤ (T : Subgroup G))
    (hm : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (componentOrbit V (T : Subgroup G) : Set G))
    {R : Subgroup G} (hlo : (PureFourXi.residual T L).pCoreIn 2 ≤ R)
    (hhi : R ≤ (PureFourXi.normalizerJoin T L).pCoreIn 2) :
    Nat.card (componentOrbit V (T : Subgroup G) ⊓ omegaCenterIn R : Subgroup G) = 16 := by
  let W := componentOrbit V (T : Subgroup G)
  have hWR := (S.four_orbit_le_xi_core hTM hWT hm).trans hlo
  have he : W ⊓ omegaCenterIn R = W ⊓ centralizer (R : Set G) := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1,((mem_omegaCenterIn_iff R x).mp hx.2).2.1⟩
    · intro hx
      refine ⟨hx.1,(mem_omegaCenterIn_iff R x).mpr ⟨hWR hx.1,hx.2,?_⟩⟩
      exact elemPow_eq_one_of_isElementaryAbelian x hx.1
  rw [he]
  exact S.four_core_interval_fixed_card hTM hWT hm hlo hhi
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel


namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter1 Chapter1.XiEmbedding
open ChapterH.NaturalDual.SourceFourActors
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original doubled module is normal inside each nonabelian containing core,
with its literal central omega intersection of order sixteen. -/
theorem doubleNatural_four_pure_normal_core_module_of_many_of_omega_fixed
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
            (p % 8 = 3 ∨ p % 8 = 5) ∧ (p % 24 = 11 ∨ p % 24 = 13)) ∧
          quotientImage (componentOrbit K (T : Subgroup G)) (B.pointSylow w) =
            quotientImage (componentOrbit K (T : Subgroup G)) (T : Subgroup G) ∧
          X.pCoreIn 2 ≤ (componentOrbit K (T : Subgroup G)).pCoreIn 2 ∧
          (¬ (componentOrbit K (T : Subgroup G)).pCoreIn 2 ≤
            centralizer (componentOrbit V (T : Subgroup G) : Set G)) ∧
          (¬ H.pCoreIn 2 ≤ centralizer (componentOrbit V (T : Subgroup G) : Set G)) ∧
          ⁅(componentOrbit K (T : Subgroup G)).pCoreIn 2,
            ((A : Subgroup X).map X.subtype)⁆ = X.pCoreIn 2 ∧
          ¬ ClassicalGroup.IsPSL (XiQuotient K) 2 4 ∧
          K ∈ Chapter1.LStar G (T : Subgroup G) ∧
          K ∈ MainForward.faithfulLocalComponents T ∧
          Nonempty (Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T K) ∧
          let Y := componentOrbit K (T : Subgroup G)
          let R := (X ⊔ ((T : Subgroup G) ⊓ Y)).pCoreIn 2
          Y.pCoreIn 2 ≤ R ∧ R ≤ (T : Subgroup G) ⊓ Y ∧
          (Y.pCoreIn 2).relIndex R = 4 ∧ R.relIndex ((T : Subgroup G) ⊓ Y) = 4 ∧
          ((Y.pCoreIn 2).subgroupOf (L ⊔ (T : Subgroup G))).map
            (B.joinActionProjection D.sylow_normalizes_component) =
            A0 S.setup ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective) ∧
          ((H.pCoreIn 2).subgroupOf (L ⊔ (T : Subgroup G))).map
            (B.joinActionProjection D.sylow_normalizes_component) =
            A0 S.setup ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective) ∧
          (centralizer (componentOrbit V (T : Subgroup G) : Set G)).relIndex (Y.pCoreIn 2) = 16 ∧
          (centralizer (componentOrbit V (T : Subgroup G) : Set G)).relIndex (H.pCoreIn 2) = 16 ∧
          Nat.card (componentOrbit V (T : Subgroup G) ⊓ centralizer (Y.pCoreIn 2 : Set G) : Subgroup G) = 16 ∧
          Nat.card (componentOrbit V (T : Subgroup G) ⊓ centralizer (H.pCoreIn 2 : Set G) : Subgroup G) = 16 ∧
          componentOrbit V (T : Subgroup G) ≤ H.pCoreIn 2 ∧
          ¬ IsMulCommutative (H.pCoreIn 2) ∧
          componentOrbit V (T : Subgroup G) ≤ X.pCoreIn 2 ∧
          componentOrbit V (T : Subgroup G) ≤ Y.pCoreIn 2 ∧
          ((componentOrbit V (T : Subgroup G)).subgroupOf (Y.pCoreIn 2)).Normal ∧
          ((componentOrbit V (T : Subgroup G)).subgroupOf (H.pCoreIn 2)).Normal ∧
          (¬ IsMulCommutative (X.pCoreIn 2)) ∧
          (¬ IsMulCommutative (Y.pCoreIn 2)) ∧
          Nat.card (componentOrbit V (T : Subgroup G) ⊓ omegaCenterIn (Y.pCoreIn 2) : Subgroup G) = 16 ∧
          Nat.card (componentOrbit V (T : Subgroup G) ⊓ omegaCenterIn (H.pCoreIn 2) : Subgroup G) = 16 := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf hne
  obtain ⟨P,hlt,hPC,hPM,hPN,hiT,hH,hHN,hout,A,K,hs,he,hstrict,hodd,hfull,hcore,
      hmoveY,hmoveH,hcomm,hA5,hmax,hfaith,hFS,hQR,hRT,hidx1,hidx2,himageY,himageH,
      hindexY,hindexH,hfixedY,hfixedH,hWH,hnonH⟩ :=
    D.doubleNatural_four_pure_core_interval_of_many_of_omega_fixed
      h hmany B S w hw hp hfix hf hne
  let X := PureFourXi.residual T L
  let H := (P : Subgroup G) ⊔ (X ⊔ (T : Subgroup G))
  let Y := componentOrbit K (T : Subgroup G)
  have hb := PureFourXi.swapped_containing_core_bounds T hs
  have hXT := (D.doubleNatural_four_pure_xi_of_many h hmany B S w hw hp hfix hf).2.1
  have hhiH : H.pCoreIn 2 ≤ (PureFourXi.normalizerJoin T L).pCoreIn 2 := hXT ▸ hb.2
  have hhiY := hb.1.trans hhiH
  have hloH := hcore.trans hb.1
  have hWT := (D.doubledOrbit_E322 h).le_sylow
  have hmove := (D.doubleNatural_four_pure_thompson_moves_of_many h hmany B S w hw hp hfix hf).2
  have hWX := S.four_orbit_le_xi_core D.sylow_normalizes_component hWT hmove
  have hy := S.four_core_interval_orbit_normal D.sylow_normalizes_component hWT hmove hcore hhiY
  have hh := S.four_core_interval_orbit_normal D.sylow_normalizes_component hWT hmove hloH hhiH
  have hxx := S.four_core_interval_orbit_normal D.sylow_normalizes_component hWT hmove
    (le_refl (X.pCoreIn 2)) (hcore.trans hhiY)
  exact ⟨P,hlt,hPC,hPM,hPN,hiT,hH,hHN,hout,A,K,hs,he,hstrict,hodd,hfull,hcore,
    hmoveY,hmoveH,hcomm,hA5,hmax,hfaith,hFS,hQR,hRT,hidx1,hidx2,himageY,himageH,
    hindexY,hindexH,hfixedY,hfixedH,hWH,hnonH,hWX,hy.1,hy.2.1,hh.2.1,hxx.2.2,hy.2.2,
    S.four_core_interval_central_omega_card D.sylow_normalizes_component hWT hmove hcore hhiY,
    S.four_core_interval_central_omega_card D.sylow_normalizes_component hWT hmove hloH hhiH⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
