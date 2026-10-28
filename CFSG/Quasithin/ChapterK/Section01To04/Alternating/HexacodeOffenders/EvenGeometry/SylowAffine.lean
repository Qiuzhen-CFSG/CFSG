module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.HexacodeOffenders.EvenGeometry.SylowDisplacement
import all CFSG.Quasithin.ChapterK.Section01To04.Alternating.HexacodeOffenders.EvenGeometry.Sylow
public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetStabilizer
public import Theory.GroupTheory.SemidirectElementaryQuotient
public import Theory.ElementaryAbelian.EightQuotientRank
public import Theory.Representation.BinaryGroupAction

/-!
# Elementary quotients of the native even affine Sylow

An elementary subgroup of order 64 meeting the translations in order 16
projects onto the plane four-group. Its translation intersection is therefore
the entire fixed plane. All Sylow displacements lie in this plane, and the
mixed commutator with the plane four-group is the whole derived subgroup.
Consequently a normal such subgroup contains every square.

The internal import of the frozen Sylow owner is used only for its finite
word coordinates in the proof of the actor square calculation.
-/

public section
open Atlas.Codes Representation Subgroup Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterK.Alternating.HexacodeOffenders.EvenGeometry.SylowModel

local notation "φ" => MonoidHom.comp (MonoidHom.comp hexAffineAction hexSign.ker.subtype) sylowGroup.subtype
local notation "P" => Multiplicative hexacode ⋊[φ] sylowGroup
local notation "ι" => (SemidirectProduct.inl : Multiplicative hexacode →* P)
local notation "π" => (SemidirectProduct.rightHom : P →* sylowGroup)

private theorem translation_card (W : Subgroup P)
    (hI : Nat.card (W ⊓ (ι).range : Subgroup P) = 16) :
    Nat.card (W.comap ι) = 16 := by
  rw [←Subgroup.card_map_of_injective (K := W.comap ι) (f := ι) SemidirectProduct.inl_injective,
    Subgroup.map_comap_eq, inf_comm]
  exact hI

private theorem translation_fixed (W : Subgroup P) [IsElementaryAbelian 2 W]
    (v : W.comap ι) :
    v.val.toAdd ∈ fixedSpace Hexacode.evenAction ((W.map π).map sylowGroup.subtype) := by
  intro a
  obtain ⟨d,hd,ha⟩ := a.property
  obtain ⟨w,hw,hd⟩ := hd
  have hc := congrArg (fun x : W => x.val.left)
    (mul_comm (⟨w,hw⟩ : W) ⟨ι v.val,v.property⟩)
  change w.left * φ w.right v.val = v.val * φ 1 w.left at hc
  rw [map_one, MulAut.one_apply, mul_comm v.val w.left] at hc
  have he := congrArg Multiplicative.toAdd (mul_left_cancel hc)
  change Hexacode.evenAction a.val v.val.toAdd = v.val.toAdd
  rw [←ha,←hd]
  exact he

private theorem actor_projection_plane (W : Subgroup P) [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 64) (hI : Nat.card (W ⊓ (ι).range : Subgroup P) = 16) :
    (W.map π).map sylowGroup.subtype = planeGroup := by
  have hp := IsElementaryAbelian.card_inf_ker_mul_card_map W π
  rw [←SemidirectProduct.range_inl_eq_ker_rightHom,hI,hW] at hp
  have hc : Nat.card ((W.map π).map sylowGroup.subtype) = 4 := by
    rw [Subgroup.card_map_of_injective sylowGroup.subtype_injective]
    omega
  let : IsElementaryAbelian 2 (W.map π) := IsElementaryAbelian.map π
  have hA : IsElementaryAbelian 2 ((W.map π).map sylowGroup.subtype) :=
    IsElementaryAbelian.map sylowGroup.subtype
  have hle : (W.map π).map sylowGroup.subtype ≤ sylowGroup := by
    rintro _ ⟨d,_,rfl⟩
    exact d.property
  rcases fourGroup_exhaustion _ hA hle hc with h | h
  · let j : W.comap ι → fixedSpace Hexacode.evenAction lineGroup := fun v =>
      ⟨v.val.toAdd, h ▸ translation_fixed W v⟩
    have hj : Function.Injective j := by
      intro v w hvw
      apply Subtype.ext
      change v.val.toAdd = w.val.toAdd
      exact congrArg (fun x => x.val) hvw
    have hcard := Nat.card_le_card_of_injective j hj
    have hline : Nat.card (fixedSpace Hexacode.evenAction lineGroup) = 4 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),lineFixed_finrank,Nat.card_zmod]
      decide
    rw [translation_card W hI,hline] at hcard
    omega
  · exact h

private theorem fixed_plane_translation (W : Subgroup P) [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 64) (hI : Nat.card (W ⊓ (ι).range : Subgroup P) = 16)
    (v : hexacode) (hv : v ∈ fixedSpace Hexacode.evenAction planeGroup) :
    ι (Multiplicative.ofAdd v) ∈ W := by
  have h := actor_projection_plane W hW hI
  let j : W.comap ι → fixedSpace Hexacode.evenAction planeGroup := fun w =>
    ⟨w.val.toAdd, h ▸ translation_fixed W w⟩
  have hj : Function.Injective j := by
    intro v w hvw
    apply Subtype.ext
    change v.val.toAdd = w.val.toAdd
    exact congrArg (fun x => x.val) hvw
  have hplane : Nat.card (fixedSpace Hexacode.evenAction planeGroup) = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),planeFixed_finrank,Nat.card_zmod]
    decide
  obtain ⟨w,hw⟩ := (hj.bijective_of_nat_card_le (by
    rw [hplane,translation_card W hI])).surjective ⟨v,hv⟩
  have he : w.val = Multiplicative.ofAdd v :=
    Multiplicative.toAdd.injective (congrArg Subtype.val hw)
  exact he ▸ w.property

private theorem actor_squares (d : sylowGroup) : d^2 ∈ _root_.commutator sylowGroup := by
  have hmap := sylowGroup.map_subtype_commutator
  rw [sylow_commutator_self_eq] at hmap
  have hz : (d.val)^2 ∈ zpowers z := by
    obtain ⟨p,hp⟩ := d.property
    rw [←hp,pow_two,←word_mul]
    rcases p with ⟨a,b,c⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      simp [mulBits,word,mem_zpowers]
  rw [←hmap] at hz
  obtain ⟨e,he,hee⟩ := hz
  have hee' : e = d^2 := Subtype.ext hee
  exact hee' ▸ he

/-- Every square in the native even affine Sylow belongs to a normal
elementary subgroup of order 64 whose translation intersection has order 16. -/
theorem affine_squares_mem (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 64) (hI : Nat.card (W ⊓ (ι).range : Subgroup P) = 16) :
    ∀ x : P, x^2 ∈ W := by
  let : IsElementaryAbelian 2 (Multiplicative hexacode) := BinaryGroupAction.elementary
  apply Theory.GroupTheory.semidirect_squares_mem_of_mixed_commutator φ W
  · intro d v
    have he : φ d v * v⁻¹ =
        Multiplicative.ofAdd (Hexacode.evenAction d.val v.toAdd-v.toAdd) := by
      apply Multiplicative.toAdd.injective
      change Hexacode.evenAction d.val v.toAdd + -v.toAdd =
        Hexacode.evenAction d.val v.toAdd-v.toAdd
      exact (sub_eq_add_neg _ _).symm
    rw [he]
    exact fixed_plane_translation W hW hI
      (Hexacode.evenAction d.val v.toAdd-v.toAdd)
      (sylow_displacement_mem_planeFixed d.val d.property v.toAdd)
  · apply Subgroup.map_injective sylowGroup.subtype_injective
    rw [Subgroup.map_commutator,←MonoidHom.range_eq_map,Subgroup.range_subtype,
      actor_projection_plane W hW hI,sylowGroup.map_subtype_commutator,
      sylow_commutator_plane_eq,sylow_commutator_self_eq]
  · exact actor_squares

end CFSG.Quasithin.ChapterK.Alternating.HexacodeOffenders.EvenGeometry.SylowModel
