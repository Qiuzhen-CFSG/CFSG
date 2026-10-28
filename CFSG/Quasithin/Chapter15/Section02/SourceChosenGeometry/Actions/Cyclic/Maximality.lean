module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Actions
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.Action
public import BenderSuzuki.MatrixGroups.SuzukiZero
/-!
# Sylow maximality in the three surviving cyclic models

The restricted models below are a conclusion interface, not an assumed source
theorem. Their actual group isomorphisms give orders six, ten and twenty.
The Sylow image has prime index three or five, hence is maximal. Applying
the ambient centralizer theorem gives Mc = C_G(Z) and the original
intersection and centralizer product. The first two models have Sylow order two.

Source: Aschbacher--Smith 15.2.13(1)(i) and 15.2.14(1),(5),
printed pp.1111--1112, combined manuscript of 1 March 2004, refs/quasithin.pdf.
-/

public section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open CFSG.Quasithin.ChapterD CFSG.Quasithin.ChapterD.UniqueFactor
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.Cyclic
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The surviving whole-action models, with their original J-hat row. -/
@[expose] def RestrictedModels {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V) : Prop :=
  letI := h.prepared.elementary
  let D := internalActionImage M V h.prepared.normalized
  let ρ := imageRepresentation M V h.prepared.normalized
  (Jhat ρ = ⊤ ∧ Nonempty (D ≃* Equiv.Perm (Fin 3))) ∨
    (Nonempty (Jhat ρ ≃* DihedralGroup 5) ∧
      (Nonempty (D ≃* DihedralGroup 5) ∨
        Nonempty (D ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)))

omit [Finite G] in
private theorem coatom_of_prime_index (A : Subgroup G) (hi : Nat.Prime A.index) :
    IsCoatom A := by
  refine ⟨fun ht => by have hh := hi.ne_one; exact hh (by simp [ht]), fun B hAB => ?_⟩
  have hm := relIndex_mul_index hAB.le
  have hp : (A.relIndex B * B.index).Prime := hm ▸ hi
  rcases Nat.prime_mul_iff.mp hp with ⟨_,hB⟩ | ⟨_,hrel⟩
  · exact index_eq_one.mp hB
  · exact (hAB.not_ge (relIndex_eq_one.mp hrel)).elim

private theorem small_sylow_isCoatom (P : Sylow 2 G)
    (hc : Nat.card G = 6 ∨ Nat.card G = 10 ∨ Nat.card G = 20) :
    IsCoatom (P : Subgroup G) := by
  have hcard := P.card_eq_multiplicity
  have hi := (P : Subgroup G).card_mul_index
  apply coatom_of_prime_index
  rcases hc with hc | hc | hc
  all_goals
    rw [hc] at hcard hi
    norm_num [show (Nat.factorization 6) 2 = 1 from by decide +kernel,
      show (Nat.factorization 10) 2 = 1 from by decide +kernel,
      show (Nat.factorization 20) 2 = 2 from by decide +kernel] at hcard
    rw [hcard] at hi
    have hh : (P : Subgroup G).index = 3 ∨ (P : Subgroup G).index = 5 := by omega
    rcases hh with hh | hh <;> rw [hh] <;> decide

/-- The literal Sylow image is maximal in each surviving model. -/
theorem sylow_image_isCoatom {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hr : RestrictedModels h) :
    IsCoatom (actor M V (T : Subgroup G) h.prepared.normalized) := by
  let := h.prepared.elementary
  let f := (actionHom M V h.prepared.normalized).rangeRestrict
  let P : Sylow 2 (internalActionImage M V h.prepared.normalized) :=
    (T.subtype h.maximal.1.2).mapSurjective
    (actionHom M V h.prepared.normalized).rangeRestrict_surjective
  change IsCoatom (P : Subgroup (internalActionImage M V h.prepared.normalized))
  apply small_sylow_isCoatom
  rcases hr with ⟨_,⟨e⟩⟩ | ⟨_,he⟩
  · left
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  · rcases he with he | he
    · obtain ⟨e⟩ := he
      right; left
      rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card]
    · obtain ⟨e⟩ := he
      right; right
      exact (Nat.card_congr e.toEquiv).trans BenderSuzuki.MatrixGroups.suzukiZero_card

/-- The S₃ and D₁₀ rows have Sylow image of order two. -/
theorem sylow_image_card_two {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V)
    (hm : Nonempty (internalActionImage M V h.prepared.normalized ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty (internalActionImage M V h.prepared.normalized ≃* DihedralGroup 5)) :
    Nat.card (actor M V (T : Subgroup G) h.prepared.normalized) = 2 := by
  let P : Sylow 2 (internalActionImage M V h.prepared.normalized) :=
    (T.subtype h.maximal.1.2).mapSurjective
    (actionHom M V h.prepared.normalized).rangeRestrict_surjective
  change Nat.card P = 2
  rw [P.card_eq_multiplicity]
  rcases hm with he | he
  all_goals obtain ⟨e⟩ := he
  all_goals rw [Nat.card_congr e.toEquiv]
  · have hc : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
    rw [hc,show (Nat.factorization 6) 2 = 1 from by decide +kernel]
    rfl
  · have hc : Nat.card (DihedralGroup 5) = 10 := by
      exact DihedralGroup.nat_card
    rw [hc,show (Nat.factorization 10) 2 = 1 from by decide +kernel]
    rfl

/-- Original 15.2.14(1),(5) in the recognized cyclic rows. -/
theorem centralizers_of_restricted_models {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hfull : V = localModule T M)
    (hr : RestrictedModels h) :
    Mc = centralizer (centralInvolutions T : Set G) ∧
      M ⊓ Mc = M ⊓ centralizer (centralInvolutions T : Set G) ∧
      M ⊓ centralizer (centralInvolutions T : Set G) =
        (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G) :=
  h.centralizers_of_sylow_image_coatom hfull (sylow_image_isCoatom h hr)
end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.Cyclic
