module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.ResidualPlaneAssembly

/-!
# The surviving equality row of the chosen-action argument

When the offender plane equals the central involution subgroup, its centralizer
has the required unique maximal overgroup directly from the source hypothesis.
The checked terminal contradiction therefore excludes this row without using
any residual identity. The full Sylow image in the S3 and dihedral-ten models
puts them in this row, so these models and the marked cubic action are excluded.

In the remaining case the partner span equals the original residual, the
plane centralizer has index two in T, and the action is Sz(2) or Omega. The
partner must have an element of order nine, since its absence would supply
the one residual identity needed by the terminal theorem. The original global
H-star wreath quotients remain explicit; this does not prove their recognition
or the remaining order-nine exclusion.

Source: Aschbacher--Smith, 15.2.12--15 and 15.2.27--28,
printed pp.1111--1112 and 1119--1120.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChosenGeometry ChosenGeometry.Cyclic
open ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B : Subgroup G}

/-- The equal-plane case has uniqueness directly from the original partner hypothesis; no residual identity is needed. -/
theorem source_chosen_contradiction_of_seed_eq
    (h : ChosenSmallSource T M Mc V) (d : ResidualInput h H B)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* Wreath))
    (he : centralInvolutions T = ⁅V,B⁆) : False := by
  apply source_chosen_contradiction_of_residual_input_and_uniqueness h d hquotient
  rw [←he,inf_eq_right.mpr d.partner_eq_centralizer.ge]
  exact h.partner

/-- The terminal theorem leaves only the equality residual row with the index-two Sz(2) or Omega action. -/
theorem source_chosen_index_two_equality_row
    (h : ChosenSmallSource T M Mc V) (d : ResidualInput h H B)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* Wreath)) :
    letI := h.prepared.elementary
    partnerSpan H Mc = residual H ∧
      (Nonempty (internalActionImage M V h.prepared.normalized ≃*
          BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
        SourceCases.Omega (imageRepresentation M V h.prepared.normalized)) ∧
      Nat.card (centralInvolutions T) = 2 ∧
      (planeCentralizer T ⁅V,B⁆).relIndex (T : Subgroup G) = 2 := by
  let := h.prepared.elementary
  have he : partnerSpan H Mc = residual H := by
    by_contra hn
    exact source_chosen_contradiction_of_one_residual_identity h d hquotient
      (d.residual_equality_of_ne hn)
  refine ⟨he,?_⟩
  rcases d.source_plane_alternatives with hz | hi
  · exact (source_chosen_contradiction_of_seed_eq h d hquotient hz.2).elim
  · exact hi

/-- The surviving partner has an element of order nine. Excluding this element remains a source obligation. -/
theorem source_chosen_order_nine_of_wreath_quotients
    (h : ChosenSmallSource T M Mc V) (d : ResidualInput h H B)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* Wreath)) :
    ∃ x : Mc, orderOf x = 9 := by
  by_contra hn
  have h9 : ∀ x : Mc, orderOf x ≠ 9 := by
    intro x hx
    exact hn ⟨x,hx⟩
  exact source_chosen_contradiction_of_one_residual_identity h d hquotient
    (d.residual_equality_of_no_order_nine (fun _ => h9))

/-- Both action models with Sylow image of order two lie in the excluded equal-plane case. -/
theorem source_chosen_contradiction_of_small_sylow_action
    (h : ChosenSmallSource T M Mc V) (d : ResidualInput h H B)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* Wreath))
    (hs : letI := h.prepared.elementary
      Nonempty (internalActionImage M V h.prepared.normalized ≃* Equiv.Perm (Fin 3)) ∨
        Nonempty (internalActionImage M V h.prepared.normalized ≃* DihedralGroup 5)) :
    False := by
  let := h.prepared.elementary
  obtain ⟨hA,hq⟩ := d.actor_quadratic_of_plane
  have hle : actor M V B h.prepared.normalized ≤
      actor M V (T : Subgroup G) h.prepared.normalized :=
    map_mono (comap_mono d.offender_le_sylow)
  have he := equal_plane_of_full_sylow_image h d.full d.offender_le_sylow hA hq
    (eq_of_le_of_card_ge hle ((sylow_image_card_two h hs).le.trans
      (quadratic_fixed_eq_moved h _ hA hq).1.ge))
  exact source_chosen_contradiction_of_seed_eq h d hquotient he.2

/-- The marked cubic action is impossible once the actual residual input and global wreath quotients are supplied. -/
theorem source_chosen_contradiction_of_marked_cubic_residual_input
    (h : ChosenSmallSource T M Mc V) (d : ResidualInput h H B)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* Wreath))
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        ChapterD.CyclicSource.DihedralMarking l 3 2) : False := by
  let := h.prepared.elementary
  obtain ⟨l,hd⟩ := hd
  have hc := Nat.card_congr hd.dihedral.some.toEquiv
  rw [DihedralGroup.nat_card] at hc
  rcases d.restricted_models_or_omega with (⟨_,h3⟩ | ⟨h5,_⟩) | ho
  · exact source_chosen_contradiction_of_small_sylow_action h d hquotient (Or.inl h3)
  · have h5c := Nat.card_congr h5.some.toEquiv
    rw [DihedralGroup.nat_card] at h5c
    omega
  · rw [ho.1,card_top] at hc
    have ho' : Nat.card (internalActionImage M V h.prepared.normalized) = 36 :=
      (Nat.card_congr ho.2.2.2.1.some.toEquiv).trans (by
        rw [Nat.card_prod]
        norm_num [Nat.card_eq_fintype_card,Fintype.card_perm])
    omega

end CFSG.Quasithin.Chapter15.Section02
