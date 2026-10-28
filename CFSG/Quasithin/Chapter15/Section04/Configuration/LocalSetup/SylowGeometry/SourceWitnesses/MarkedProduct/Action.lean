module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.PairGeometry
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.Normalizers
public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# The original orthogonal source action

Retain the actual action of M on W=[V(M),X], its faithful cubic quotient
representation, and the pointwise coordinate map. The image of the original X
is exactly the independent plane-rotation group. The family commutator identity
forces a nontrivial Thompson image, and source irreducibility forces a genuine
plane exchange in T. These are inputs to the full marked XS quotient.

Source: Aschbacher–Smith, 15.4.12(6), printed pp.1160–1161.
-/

@[expose] public section
open Subgroup Stellmacher
open OrthogonalFourBinary OrthogonalFourBinary.TerminalLines OrthogonalFourBinary.SylowGeometry
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct
open FamilySource FamilySource.ModuleStructure
open FamilySource.ModuleStructure.BinaryNormalizer FamilySource.ModuleStructure.BaumannPair
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M X : Subgroup G}

structure SourceAction (T : Sylow 2 G) (M X : Subgroup G) where
  member_le : X ≤ M
  coordinates : movedModule (T : Subgroup G) M X ≃* ModelSpace
  actor : M →* OrthogonalFourBinary.IsometryGroup
  cubic_actor : image M X →* MulAut (movedModule (T : Subgroup G) M X)
  cubic_faithful : Function.Injective cubic_actor
  cubic_conjugation : ∀ (x : X) (w : movedModule (T : Subgroup G) M X),
    (cubic_actor (memberProjection M X member_le x) w : G) =
      (x : G) * (w : G) * (x : G)⁻¹
  rotation_image : cubic_actor.range.map (MulAut.congr coordinates).toMonoidHom = modelRotations
  intertwines : ∀ (m : M) (w : movedModule (T : Subgroup G) M X),
    (coordinates.symm (vectorAction (actor m) (coordinates w)) : G) =
      (m : G) * (w : G) * (m : G)⁻¹
  cubic_image : (X.subgroupOf M).map actor = rotations
  baumann_base : (ChapterB.baumann (T : Subgroup G)).subgroupOf M ≤ base.comap actor

theorem exists_sourceAction (h : Input K T M X 2) : Nonempty (SourceAction T M X) := by
  obtain ⟨c,γ,ρ,hi,hρ,hc,hγ,hbase⟩ := h.double_orthogonal_baumann
  have he : vectorAction.comp (γ.comp (inclusion h.member_le)) =
      (MulAut.congr c).toMonoidHom.comp (ρ.comp (memberProjection M X h.member_le)) := by
    apply MonoidHom.ext
    intro x
    apply MulEquiv.ext
    intro v
    let w := c.symm v
    apply c.symm.injective
    apply Subtype.ext
    have ha := hγ (inclusion h.member_le x) w
    rw [c.apply_symm_apply] at ha
    change _ = (c.symm (c (ρ (memberProjection M X h.member_le x) (c.symm v))) : G)
    rw [c.symm_apply_apply]
    exact ha.trans (hρ x w).symm
  have hsur : Function.Surjective (memberProjection M X h.member_le) :=
    memberProjection_surjective M X h.member_le
  have him : (X.subgroupOf M).map γ = rotations := by
    apply Subgroup.map_injective vectorAction_injective
    rw [← inclusion_range h.member_le, MonoidHom.map_range, MonoidHom.map_range]
    rw [he, MonoidHom.range_comp, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr hsur, ← MonoidHom.range_eq_map, hc]
    change (vectorAction.comp rotationHom).range = _
    rw [MonoidHom.range_comp]
    rfl
  exact ⟨⟨h.member_le,c,γ,ρ,hi,hρ,hc,hγ,him,fun b hb => (base_iff _).mpr (hbase ⟨b,hb⟩)⟩⟩

theorem SourceAction.thompson_image_ne_bot (d : SourceAction T M X)
    (h : Input K T M X 2) :
    ((elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf M).map d.actor ≠ ⊥ := by
  intro hj
  have hJM : elementaryAbelianMaxJ (T : Subgroup G) ≤ M :=
    (sSup_le fun A hA => hA.1).trans h.sylow_le
  have hh : ⁅X.subgroupOf M, (elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf M⁆ =
      X.subgroupOf M := by
    apply map_injective M.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le h.member_le,
      map_subgroupOf_eq_of_le hJM, YFamily.commutator_eq h.member]
  have he := congrArg (Subgroup.map d.actor) hh
  rw [map_commutator, hj, commutator_bot_right, d.cubic_image] at he
  have hc : Nat.card rotations = 9 := by
    rw [rotations, ← Nat.card_congr (MonoidHom.ofInjective rotationHom_injective).toEquiv,
      Nat.card_eq_fintype_card]
    decide
  rw [← he, card_bot] at hc
  omega

theorem SourceAction.exists_swap (d : SourceAction T M X) (h : Input K T M X 2) :
    ∃ t : (T : Subgroup G), (codeEquiv.symm (d.actor (inclusion h.sylow_le t))).2.2 = true := by
  by_contra! hn
  let W := movedModule (T : Subgroup G) M X
  let : IsElementaryAbelian 2 W := h.moved_elementary
  let : IsElementaryAbelian 3 (image M X) := h.image_structure.1
  let _ := MulDistribMulAction.compHom W d.cubic_actor
  let _ : FaithfulSMul (image M X) W := ⟨fun {a b} he => d.cubic_faithful (MulEquiv.ext he)⟩
  have hA : Nat.card (image M X) = 9 := by simpa using h.image_structure.2
  have hW : Nat.card W = 16 := by simpa using h.moved_card
  obtain ⟨P⟩ := exists_factorPair (W := W) hA hW
  have hnX := (normal_subgroupOf_iff_le_normalizer h.member_le).mp h.normal
  have hinv : ∀ t : (T : Subgroup G),
      (P.line false).map (imageConjugation M X hnX (inclusion h.sylow_le t)).toMonoidHom = P.line false := by
    intro t
    apply factorPair_map_eq_of_noninterchanging_coordinates d.cubic_actor d.cubic_faithful
      d.coordinates d.rotation_image
      (imageConjugation M X hnX (inclusion h.sylow_le t))
      (moduleConjugation M W h.moved_normalized (inclusion h.sylow_le t))
      (source_intertwining M X W d.member_le hnX h.moved_normalized d.cubic_actor
        d.cubic_conjugation (inclusion h.sylow_le t))
      (d.actor (inclusion h.sylow_le t)) _ (Bool.eq_false_of_not_eq_true (hn t)) P false
    intro w
    apply d.coordinates.symm.injective
    rw [d.coordinates.symm_apply_apply]
    exact Subtype.ext (d.intertwines (inclusion h.sylow_le t) w).symm
  rcases h.image_irreducible (P.line false) hinv with he | he
  · have hc := P.card false
    rw [he, card_bot] at hc
    omega
  · have hc := P.card false
    rw [he, card_top, hA] at hc
    omega

theorem source_member_core_ne_bot (h : Input K T M X 2) : X.pCoreIn 2 ≠ ⊥ :=
  FamilySource.member_core_ne_bot (h.ambient.evenCharacteristic T M h.maximal h.sylow_le)
    h.member h.member_le h.normal

theorem source_member_quotient_card (h : Input K T M X 2) :
    Nat.card (X ⧸ pCore 2 X) = 9 := by simpa using h.quotient_card

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct
