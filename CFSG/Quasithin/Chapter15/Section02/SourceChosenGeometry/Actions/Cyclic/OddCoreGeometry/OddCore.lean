module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Actions.Cyclic.Inputs
public import Theory.GroupTheory.CyclicSylowOddCoreCommutator

/-!
# The odd-core clause for the restricted cyclic actions

The literal action image has order six, ten or twenty. Its cyclic Sylow
has an odd complement of prime order; triviality of the two-core then
forces every nontrivial offender image to move the whole complement.
The existing common-image theorem supplies uniqueness inside the original
Sylow image. No new representation or involution marking is chosen.

Restricted-model recognition remains an explicit hypothesis, discharged
by the final action-plane assembly (qt-e-152-action-plane).
Source: Aschbacher--Smith 15.2.13(2), printed pp.1111--1112,
combined manuscript of 1 March 2004, refs/quasithin.pdf.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterD CFSG.Quasithin.ChapterD.UniqueFactor
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.Cyclic
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem restricted_card {T : Sylow 2 G} {M Mc V : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (hr : RestrictedModels h) :
    Nat.card (internalActionImage M V h.prepared.normalized) = 6 ∨
      Nat.card (internalActionImage M V h.prepared.normalized) = 10 ∨
      Nat.card (internalActionImage M V h.prepared.normalized) = 20 := by
  let := h.prepared.elementary
  rcases hr with ⟨_,⟨e⟩⟩ | ⟨_,he⟩
  · left
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  · rcases he with he | he
    · obtain ⟨e⟩ := he
      exact Or.inr (Or.inl ((Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card))
    · obtain ⟨e⟩ := he
      exact Or.inr (Or.inr ((Nat.card_congr e.toEquiv).trans
        BenderSuzuki.MatrixGroups.suzukiZero_card))

/-- The odd core of the actual restricted image is moved by each source actor. -/
theorem Preceding.oddCore_commutator {T : Sylow 2 G} {M Mc V H B : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : Preceding h H)
    (hr : RestrictedModels h) (hB : B ∈ sigmaOutside (T : Subgroup G) H) :
    pPrimeCore 2 (internalActionImage M V h.prepared.normalized) =
      ⁅pPrimeCore 2 (internalActionImage M V h.prepared.normalized),
        actor M V B h.prepared.normalized⁆ := by
  let := h.prepared.elementary
  let D := internalActionImage M V h.prepared.normalized
  let P : Sylow 2 D := (T.subtype h.maximal.1.2).mapSurjective
    (actionHom M V h.prepared.normalized).rangeRestrict_surjective
  have hP : IsCyclic P := sylow_image_cyclic h d.alternatives d.non_omega
  have hc := restricted_card hr
  have heven : 2 ∣ Nat.card D := by
    rcases hc with hc | hc | hc <;> rw [hc] <;> decide
  have hprime : (Nat.card (pPrimeCore 2 D)).Prime := by
    have hcount := (P.isComplement'_pPrimeCore_of_isCyclic hP heven).card_mul_card
    have hPc := P.card_eq_multiplicity
    rcases hc with hc | hc | hc
    all_goals
      rw [hc] at hPc hcount
      norm_num [show (Nat.factorization 6) 2 = 1 from by decide +kernel,
        show (Nat.factorization 10) 2 = 1 from by decide +kernel,
        show (Nat.factorization 20) 2 = 2 from by decide +kernel] at hPc
      rw [hPc] at hcount
      have hh : Nat.card (pPrimeCore 2 D) = 3 ∨ Nat.card (pPrimeCore 2 D) = 5 := by omega
      rcases hh with hh | hh <;> rw [hh] <;> decide
  have hcore : pCore 2 D = ⊥ := by
    change pCore 2 (internalActionImage M V h.prepared.normalized) = ⊥
    rw [←chosenNormalizer_actionImage_eq T h.maximal.1.2 h.prepared.normalized]
    exact chosenNormalizer_actionImage_reduced T h.maximal.1.2 h.prepared.le_selected
      h.prepared.normalized h.prepared.seed_span
  exact oddCore_commutator_eq_of_cyclic_sylow P hP heven hcore hprime _
    (map_mono (comap_mono (d.actor_le_sylow hB))) (d.planes B hB).1.1

/-- The unique order-two subgroup of the literal Sylow image has the source
odd-core characterization, and all outside offenders have this image. -/
theorem Preceding.common_image_oddCore {T : Sylow 2 G} {M Mc V H : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : Preceding h H) (hr : RestrictedModels h) :
    ∃ B₀ : Subgroup (internalActionImage M V h.prepared.normalized),
      B₀ ≤ actor M V (T : Subgroup G) h.prepared.normalized ∧ Nat.card B₀ = 2 ∧
      pPrimeCore 2 (internalActionImage M V h.prepared.normalized) =
        ⁅pPrimeCore 2 (internalActionImage M V h.prepared.normalized),B₀⁆ ∧
      (∀ A : Subgroup (internalActionImage M V h.prepared.normalized),
        A ≤ actor M V (T : Subgroup G) h.prepared.normalized → Nat.card A = 2 → A = B₀) ∧
      ∀ B ∈ sigmaOutside (T : Subgroup G) H, actor M V B h.prepared.normalized = B₀ := by
  let := h.prepared.elementary
  obtain ⟨B₀,hBP,hcard,hunique,hplane⟩ := d.common_plane
  obtain ⟨B,hB⟩ := d.nonempty
  refine ⟨B₀,hBP,hcard,?_,hunique,fun C hC => (hplane C hC).1⟩
  rw [←(hplane B hB).1]
  exact d.oddCore_commutator hr hB

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.Cyclic
