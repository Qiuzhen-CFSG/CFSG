module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceRankOneMatchingParabolics
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.UnitaryFiveCentered

/-!
# Centered residuals on the original chosen orbit

The covering residual has its two-core inside O₂(L), so it centralizes the
unchanged chosen orbit. For the unitary marking, the actual PSU₅(4) component
then contradicts the centered commutator calculation. This proves the
abelian odd-normalizer conclusion when the residual has a unique maximal
two-local overgroup. The arbitrary-odd and Hall applications use the existing
source reductions with the same original T and section-centralizer kernel.

Residual uniqueness and the Suzuki centered-module contradiction remain
separate obligations; this module does not assert the full source theorem.
Source: Aschbacher--Smith 4.4.12--14, printed pp.621--625, applied to 12.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original chosen orbit centralizes the two-core of the fixed residual,
using the inclusion-induced core quotient isomorphism. This applies to both
family markings without changing the module. -/
theorem sourceOrbit_oddActorResidual_core_centralizes
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) :
    D.sourceOrbit ≤ centralizer ((oddActorResidual L A).pCoreIn 2 : Set G) := by
  have hsect := (le_sectionCentralizer_iff A L).mp
    (hA.trans (D.sourceOrbit_relative_centralizer_le_sectionCentralizer h hV))
  have hAV : A ≤ centralizer (V : Set G) := hV ▸ hA.trans inf_le_right
  have hdata := chosen_oddActorResidual_cover h D A hsect.1 hsect.2 ho hAV
  have hFL : oddActorResidual L A ≤ L := (oddActorResidual_le L A).trans inf_le_left
  obtain ⟨e,he⟩ := exists_pCoreQuotientEquiv_of_cover hFL hdata.1.subset
  have hc : (oddActorResidual L A).pCoreIn 2 ≤ L.pCoreIn 2 := by
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨inclusion hFL x,?_,rfl⟩
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' (pCore 2 L)) (inclusion hFL x) = 1
    have hxq : QuotientGroup.mk' (pCore 2 (oddActorResidual L A)) x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr hx
    rw [← he, hxq, map_one]
  have hLC : L.pCoreIn 2 ≤ centralizer (V : Set G) :=
    (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le L.le_normalizer D.sylow_normalizes_component)).trans D.core_centralizes
  rw [← hV]
  exact le_centralizer_iff.mp (hc.trans hLC)

/-- The PSU₅(4) centered-module contradiction closes the unitary component
branch. Residual uniqueness is the only additional ambient premise. -/
theorem sourceOrbit_unitary_abelian_odd_control_of_unique
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2 ^ s))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    normalizer (A : Set G) ≤ normalizer (L : Set G) := by
  by_contra hout
  obtain ⟨_,K,hK,_,_,_,hm,_,hf,_⟩ :=
    D.sourceOrbit_unitary_five_component_of_unique h hV hs hs2 hq A hne hA ho hu hout
  let J := K.map (normalizer (A : Set G)).subtype
  let a := (K.equivMapOfInjective (normalizer (A : Set G)).subtype Subtype.val_injective).symm
  let z : (J ⧸ center J) ≃* (K ⧸ center K) := QuotientGroup.congr _ _ a (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr a ⟨x,hx⟩).property
    · intro y hy
      exact ⟨a.symm y,(centerCongr a.symm ⟨y,hy⟩).property,a.apply_symm_apply y⟩)
  let := D.orbitComponent_quasisimple h.toHypothesis1221
  let : IsSimpleGroup (D.orbitComponent ⧸ center D.orbitComponent) := IsQuasisimple.simple
  let : Group.IsPerfect (D.orbitComponent ⧸ center D.orbitComponent) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (center D.orbitComponent))
      (QuotientGroup.mk'_surjective _)
  have hsect := (le_sectionCentralizer_iff A L).mp
    (hA.trans (D.sourceOrbit_relative_centralizer_le_sectionCentralizer h.toHypothesis1221 hV))
  have hAV : A ≤ centralizer (V : Set G) := hV ▸ hA.trans inf_le_right
  have hdata := chosen_oddActorResidual_cover h.toHypothesis1221 D A hsect.1 hsect.2 ho hAV
  let eQ := Classical.choice (D.sourceOrbit_covering_central_quotient h.toHypothesis1221
    ((oddActorResidual_le L A).trans inf_le_left) hdata.1.subset)
  let F := oddActorResidual L A
  let π : F →* (D.orbitComponent ⧸ center D.orbitComponent) :=
    eQ.toMonoidHom.comp ((QuotientGroup.mk' (center (F ⧸ pCore 2 F))).comp
      (QuotientGroup.mk' (pCore 2 F)))
  have hπ : Function.Surjective π := eQ.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  exact no_unitary_five_centered_residual (map_subtype_le K) hf
    (hV ▸ hdata.2.2.1) (hV ▸ D.ne_bot) (hV ▸ hdata.2.1)
    (D.sourceOrbit_oddActorResidual_core_centralizes h.toHypothesis1221 hV A hA ho)
    (Group.IsPerfect.not_isSolvable (D.orbitComponent ⧸ center D.orbitComponent))
    π hπ hs2 hq hu (hm.of_mulEquiv z)

/-- Remark 4.4.2 extends the proved unitary abelian branch to all odd actors.
The uniform residual-uniqueness input is retained for final source assembly. -/
theorem sourceOrbit_unitary_odd_control_of_residual_uniqueness
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2 ^ s))
    (hu : ∀ A : Subgroup G, A ≠ ⊥ →
      A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) →
      Odd (Nat.card A) → IsMulCommutative A →
      UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (X : Subgroup G) (hne : X ≠ ⊥)
    (hX : X ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card X)) : normalizer (X : Set G) ≤ normalizer (L : Set G) := by
  apply odd_normalizer_control_of_abelian (W := D.sourceOrbit) ?_ X hne hX ho
  intro A hn hA hodd hc
  let := hc
  exact D.sourceOrbit_unitary_abelian_odd_control_of_unique h hV hs hs2 hq A hn hA hodd
    (hu A hn hA hodd hc)

/-- The original-T Hall application uses the action kernel on L/O₂(L).
It now requires residual uniqueness instead of assuming odd-normalizer control. -/
theorem sourceOrbit_unitary_hall_faithful_of_residual_uniqueness
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2 ^ s))
    (hu : ∀ A : Subgroup G, A ≠ ⊥ →
      A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) →
      Odd (Nat.card A) → IsMulCommutative A →
      UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < ChapterE.generationParameter H)
    (B : Subgroup H) (hBM : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup ChapterE.Section06.FixedPointBounds.ParabolicCartan.oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H))) :
    B.map H.subtype ⊓ sectionCentralizer L = ⊥ := by
  apply D.sourceOrbit_hall_faithful_of_abelian_odd_control h hmany hV hnon ?_
    hH hlarge B hBM hHall
  intro A hn hA hodd hc
  let := hc
  exact D.sourceOrbit_unitary_abelian_odd_control_of_unique h hV hs hs2 hq A hn hA hodd
    (hu A hn hA hodd hc)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
