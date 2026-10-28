module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledSymplecticCartan
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSymplecticOddAction

/-!
# The original nonbinary Cartan bound and odd-local reduction

The seed marking identifies the central quotient of L/O₂(L) with the
full nonbinary symplectic group. Its perfectness makes descent of the
whole normalizer action faithful. Thus the literal quotient-conjugation
image has Cartan parameter at most n. The existing generation comparison
then forces a nonfaithful Hall actor, carrying its original H-star
subgroup and the full pushing-up or component configuration.

The exclusion of these configurations is still required for Hall
faithfulness and the upper bound on w; this is not the completed row.
Source: Aschbacher--Smith 4.4.3--14 and 7.3.4--5,
printed pp.619--625 and 699, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource ChapterE ChapterE.Section06.FixedPointBounds Chapter4 Chapter4.Section04
open Chapter7.NormalizedSource Theory.SpecificGroups.SymplecticFour
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

theorem sourceOrbit_symplectic_quotientAction_nPrime_le
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (Representation.restrictScalars (k := ZMod 2)
        (symplecticNatural (k := F.Carrier) 2)))) :
    nPrime (normalizerPCoreQuotientAction L).range ≤ F.degree := by
  let := h.quasisimple
  obtain ⟨m⟩ := hmodel
  let : Nontrivial (Sp F.Carrier) := m.groupEquiv.symm.toEquiv.nontrivial
  let r := m.groupEquiv.toMonoidHom.comp D.componentQuotientHom
  have hr : Function.Surjective r := m.groupEquiv.surjective.comp D.componentQuotientHom_surjective
  have hk : r.ker = center (L ⧸ pCore 2 L) := by
    have hh := IsQuasisimple.comap_center_of_surjective r hr
    rw [EvenProjective.center_eq_bot,MonoidHom.comap_bot] at hh
    exact hh
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective r hr)
  exact doubledSymplectic_centralCover_nPrime_le F.card_eq hn e _
    (Chapter7.NormalizedSource.MathieuGeneration.inner_le_quotientAction_range L)

theorem sourceOrbit_symplectic_oddLocal_obstruction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (Representation.restrictScalars (k := ZMod 2)
        (symplecticNatural (k := F.Carrier) 2)))) :
      ∃ (H : Subgroup G), H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      F.degree < generationParameter H ∧
      ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
        IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ Chapter4.sectionCentralizer L ∧
        A ≤ centralizer (D.sourceOrbit : Set G) ∧
        (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
        ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
    ((∃ J P : Subgroup G,
      J ∈ muStar (normalizer (L : Set G)) L
        (coveringOvergroup (normalizer (L : Set G)) L (oddActorResidual L A)) ∧
      PushLE L (oddActorResidual L A) J ∧
      IsMaximalTwoLocal P ∧ J ≤ P ∧ ¬ P ≤ normalizer (L : Set G) ∧
      IsSQTK KnownSimple.IsKnownSimple P ∧ D.sourceOrbit ≤ J.pCoreIn 2 ∧
      J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L) ∨
    (∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ⁅K,D.sourceOrbit.subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧ IsQuasithin K ∧ KnownSimple.IsKnownSimple (K ⧸ center K) ∧
      (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))) ∧
      D.sourceOrbit.subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))))) := by
  exact (D.sourceOrbit_symplectic_cartan_or_oddLocal_obstruction h hd hmany hnon F hn hmodel).resolve_left
    (not_lt_of_ge (D.sourceOrbit_symplectic_quotientAction_nPrime_le h F hn hmodel))

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
