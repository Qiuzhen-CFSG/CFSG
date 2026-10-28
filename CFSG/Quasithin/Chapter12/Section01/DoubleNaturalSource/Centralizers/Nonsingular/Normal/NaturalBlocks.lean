module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Normal.LocalKernel
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Normal.Blocks
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.NaturalCentrality
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2BorelGeometry
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport

/-!
# The natural-block exclusion from the original odd actor

In the normal-residual branch, Q is Sylow in the section centralizer Y
and W centralizes Q. Every subgroup of Y intersected with M fixes W by
`LocalKernel`. Thus a nontrivial odd subgroup of a natural block lying in
M fixes W. The natural-block odd fixed-point theorem then forces the whole
block to centralize W, hence to lie in M. The Borel form constructs the
odd actor from the actual intrinsic Sylow normalizer.

Cartan or Borel placement is still an explicit premise; its source proof
remains with qt-d-double-natural-centralizers. `LocalSource` applies this
to the escaping block and retains final discharge with the same owner.
Source: Aschbacher--Smith, 12.1.1, printed pp.788--789.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement IsMulCommutative
open BinaryLinear.OuterCyclic BinaryNaturalDual.ModelOrbits.AutomorphismModel
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter4 ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- A natural block with a nontrivial odd actor in M is contained in M. -/
theorem doubleNatural_normal_natural_block_le_of_odd_actor
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
      ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      ∀ K : Subgroup G,
        K ≤ sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w) →
        IsBlock (K.subgroupOf
          (sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w))) →
        ∀ k, IsL2EvenBlock K k → ∀ A : Subgroup G,
          A ≤ K → A ≤ normalizer (L : Set G) → Odd (Nat.card A) → A ≠ ⊥ →
          K ≤ normalizer (L : Set G) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hc hn K hKY hK k hnat A hAK hAM hodd hA
  let H := B.pointCentralizer w
  let Y := sectionCentralizerIn H (B.pointResidual w)
  let W := componentOrbit V (T : Subgroup G)
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hAY : A ≤ Y := hAK.trans hKY
  have hAW : A ≤ centralizer (W : Set G) := by
    apply le_trans _ (S.nonsingular_local_sectionCentralizer_le_orbitCentralizer w hw.nonsingular)
    exact le_inf (le_inf hAM (hAY.trans inf_le_left)) (hAY.trans inf_le_right)
  obtain ⟨P,hP⟩ := D.doubleNatural_adapted_normal_sectionCentralizer_sylow h B S w hw hn
  have hQY : Q ≤ Y := hP.symm.le.trans (map_subtype_le _)
  have hWQ : W ≤ Q := by
    dsimp only [Q]
    rw [←D.doubledOrbit_sylow_centralizer h]
    exact le_inf (D.doubledOrbit_E322 h).le_sylow
      (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hWY := hWQ.trans hQY
  have hQW : Q ≤ centralizer (W : Set G) := by
    dsimp only [Q]
    rw [←D.doubledOrbit_sylow_centralizer h]
    exact inf_le_right
  have htype : IsL2EvenBlock (K.subgroupOf Y) k :=
    hnat.of_mulEquiv (subgroupOfEquivOfLe hKY).symm
  have hodd' : Odd (Nat.card (A.subgroupOf Y)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hAY).toEquiv]
  have hA' : A.subgroupOf Y ≠ ⊥ := by
    intro he
    apply hA
    have hh := congrArg (map Y.subtype) he
    simpa only [map_subgroupOf_eq_of_le hAY,Subgroup.map_bot] using hh
  have hWK : W ≤ centralizer (K : Set G) := by
    intro z hz
    let zY : Y := ⟨z,hWY hz⟩
    have hz2 : zY^2=1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian z hz)
    have hzP : zY ∈ centralizer (P : Set Y) := by
      intro p hp
      apply Subtype.ext
      exact ((hQW (hP.le (mem_map_of_mem Y.subtype hp))) z hz).symm
    have hzA : zY ∈ centralizer (A.subgroupOf Y : Set Y) := by
      intro a ha
      exact Subtype.ext (hAW ha z hz).symm
    have hfix := htype.centralizes_of_sylow_and_odd_fixed P
      (doubleNatural_normal_sectionCentralizer_characteristic B w hc hn)
      (K.subgroupOf Y) hK (A.subgroupOf Y) (comap_mono hAK) hodd' hA' zY hz2 hzP hzA
    intro x hx
    exact congrArg Subtype.val (hfix ⟨x,hKY hx⟩ hx)
  exact (le_centralizer_iff.mp hWK).trans
    ((Subgroup.centralizer_le_normalizer _).trans_eq (D.doubledOrbit_normalizer_eq h B.orbit_eq))

/-- The source Borel placement constructs the odd actor and excludes an outside natural block. -/
theorem doubleNatural_normal_natural_block_le_of_borel
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
      ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      ∀ K : Subgroup G,
        K ≤ sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w) →
        IsBlock (K.subgroupOf
          (sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w))) →
        ∀ k, IsL2EvenBlock K k → ∀ P : Sylow 2 K,
          (normalizer (P : Set K)).map K.subtype ≤ normalizer (L : Set G) →
          K ≤ normalizer (L : Set G) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hc hn K hKY hK k hnat P hPM
  obtain ⟨A,hAP,ho,ha⟩ := hnat.exists_odd_borel_subgroup P
  apply D.doubleNatural_normal_natural_block_le_of_odd_actor h B S w hw hc hn K hKY hK k hnat
    (A.map K.subtype) (map_subtype_le _) ((map_mono hAP).trans hPM)
  · rwa [card_map_of_injective K.subtype_injective]
  · exact fun he => ha ((map_eq_bot_iff_of_injective _ K.subtype_injective).mp he)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
