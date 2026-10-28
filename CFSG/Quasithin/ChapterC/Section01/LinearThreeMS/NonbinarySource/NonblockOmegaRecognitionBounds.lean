module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.OmegaRecognitionBounds
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NonblockInitialFixed

/-!
# Central-omega recognition bounds in the original nonblock configuration

Original 4.3.8--10 supplies C_Q(K)=1, so the intrinsic displacement gap
and offender bounds apply to the actual central omega and source Sylow
intersection. One maximum elementary subgroup supplies a minimal quadratic
offender of order at most 2^(2n), preserving every Irr⁺ constituent and
injecting into the literal initial action.

A nontrivial kernel of that initial projection forces central-omega degree
at least 6n. Below that degree the whole central omega equals the initial
moved subgroup and is natural over the original field. Thus at field four
the kernel requires degree at least twelve, while the supplied offender
has order at most sixteen and fixed codimension at most four.

The original c, chosen module, constrained hypothesis, field size and full
quotient marking are retained. No central-omega degree bound is assumed in
the final dichotomy. Its large branch, the passage from central omega to
the whole center and the common marking of upper sections remain required
for C.1.34 and MSData. No Hypothesis1223 is used.
Source: Aschbacher--Smith B.1.5, K.3.2, C.1.34 and original 4.3.8--10,
printed pp.69--70,454--456,136--137,616--617.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.OmegaRecognitionBounds
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open ChapterC.LinearThreeMS.NonbinarySource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {F : Type} [Field F] [Finite F] [CharP F 2]
variable (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
  (hf : generalizedFitting c.K = pCore 2 c.K)
  (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
  (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))

/-- The actual source Sylow supplies one bounded minimal offender on the
whole central omega; it preserves every constituent and the initial marking. -/
theorem source_exists_bounded_minimal_offender :
    let hm := msPair_of_quotient c D hf n (by omega) hF e
    let J := (K c ⊔ c.I.pCoreIn 2 : Subgroup G)
    let E := CentralSections.coreOmegaLayer (K := K c) (R := c.I.pCoreIn 2)
    letI := CentralSections.coreOmegaLayer_normal hm hn
    letI := CentralSections.coreOmegaLayer_elementary (K := K c) (R := c.I.pCoreIn 2)
    let H := J ⧸ centralizer (E : Set J)
    let q := QuotientGroup.mk' (centralizer (E : Set J))
    let B := (q.comp ((K c).subgroupOf J).subtype).range
    let rho := CentralSections.coreOmegaRepresentation hm hn
    ∃ A ∈ elementaryAbelianMaxSubgroups ((S c).subgroupOf J), ∃ X ≤ A.map q,
      IsMinimalBestOffender rho X ∧ IsQuadratic rho X ∧
      weight rho X = weight rho (A.map q) ∧ ⁅B,X⁆ = B ∧
      X ⊓ centralizer (B : Set H) = ⊥ ∧
      Function.Injective ((NoncoreOffenders.toInitial hm hn E
        (CentralSections.coreOmegaLayer_centralizer_le hm hn)).comp X.subtype) ∧
      Nat.card X ≤ 2^(2*n) ∧ rank X ≤ 2*n ∧ fixedCodim rho X ≤ 2*n ∧
      ∀ I, IsIrrPlus rho B I → X ≤ subspaceStabilizer rho I := by
  let := CentralSections.coreOmegaLayer_normal
    (msPair_of_quotient c D hf n (by omega) hF e) hn
  have hfixed : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using
      (InitialFixed.source_fixed_factors D hf hn hF e).2.1
  exact MovingBounds.exists_bounded_minimal_offender
    (msPair_of_quotient c D hf n (by omega) hF e) hn hfixed _
    (comap_mono (c.core_sylow.le.trans inf_le_left))

/-- A nontrivial whole-action kernel requires at least twice the natural
degree on the actual central omega of the original Q. -/
theorem source_kernel_degree_bound :
    let hm := msPair_of_quotient c D hf n (by omega) hF e
    let E := CentralSections.coreOmegaLayer (K := K c) (R := c.I.pCoreIn 2)
    letI := CentralSections.coreOmegaLayer_normal hm hn
    letI := CentralSections.coreOmegaLayer_elementary (K := K c) (R := c.I.pCoreIn 2)
    let f := NoncoreOffenders.toInitial hm hn E
      (CentralSections.coreOmegaLayer_centralizer_le hm hn)
    f.ker ≠ ⊥ → 6*n ≤ Module.finrank (ZMod 2) (Additive E) := by
  let := CentralSections.coreOmegaLayer_normal
    (msPair_of_quotient c D hf n (by omega) hF e) hn
  have hfixed : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using
      (InitialFixed.source_fixed_factors D hf hn hF e).2.1
  exact MovingBounds.kernel_nontrivial_degree_lower_bound
    (msPair_of_quotient c D hf n (by omega) hF e) hn hfixed

include D hf hn hF e in
/-- The original central omega is natural, or has order at least 2^(6n).
This actual subgroup dichotomy has no additional module premise. -/
theorem source_omega_natural_or_large :
    (∃ a : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F),
      HasSectionModel (K c)
        (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (Q c))
        ⊥ (linearThreeActor a) (specialLinearNatural 3)) ∨
      2^(6*n) ≤ Nat.card
        (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (Q c)) := by
  have hfixed : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using
      (InitialFixed.source_fixed_factors D hf hn hF e).2.1
  simpa only [ms_commutator_eq] using SmallOmega.omega_natural_or_card_large
    (msPair_of_quotient c D hf n (by omega) hF e) hn hfixed

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.OmegaRecognitionBounds
