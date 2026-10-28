module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.LocalModels.Quotient
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.EarlierCore.ComponentSetup
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.NaturalSetup

/-!
# The literal Sylow flag in the original natural coordinates

The images of V₁,V₂,V₃ under the prescribed natural-module equivalence
are nested spaces of dimensions one, two and three. Their full inverse
images are exactly the original subgroup flag, both for the ordinary
model and for the covered natural-map convention. Thus no abstract flag
is substituted for the selected source subgroups.

Source: Aschbacher–Smith, Notation 13.2.1, printed p.877.
-/

@[expose] public section

open Subgroup BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)

/-- The original subgroup image as an F₂-subspace in the fixed natural coordinates. -/
noncomputable def local_flag_image (A : Subgroup G) :
    Submodule (ZMod 2) (natural (Fin 6)) :=
  AddSubgroup.toZModSubmodule 2
    (AddSubgroup.toSubgroup.symm ((A.subgroupOf V).map d.coordinate.toMonoidHom))

theorem local_flag_mem_image (A : Subgroup G) (w : natural (Fin 6)) :
    w ∈ local_flag_image d A ↔
      ∃ v : V, v.val ∈ A ∧ (d.coordinate v).toAdd = w := Iff.rfl

theorem local_flag_image_dim (A : Subgroup G) (hA : A ≤ V) (n : ℕ)
    (hc : Nat.card A = 2 ^ n) :
    Module.finrank (ZMod 2) (local_flag_image d A) = n := by
  have hcard : Nat.card (local_flag_image d A) = Nat.card A := by
    change Nat.card ((A.subgroupOf V).map d.coordinate.toMonoidHom) = Nat.card A
    rw [Subgroup.card_map_of_injective d.coordinate.injective]
    exact Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),
    Nat.card_eq_fintype_card, ZMod.card, hc] at hcard
  exact Nat.pow_right_injective (by decide : 1 < 2) hcard

theorem local_flag_image_mono (A B : Subgroup G) (h : A ≤ B) :
    local_flag_image d A ≤ local_flag_image d B := by
  intro x hx
  obtain ⟨v,hv,rfl⟩ := (local_flag_mem_image d A x).mp hx
  exact (local_flag_mem_image d B _).mpr ⟨v,h hv,rfl⟩

theorem local_flag_preimage (A : Subgroup G) (hA : A ≤ V) :
    A = ((local_flag_image d A).toAddSubgroup.toSubgroup.comap
      d.coordinate.toMonoidHom).map V.subtype := by
  apply le_antisymm
  · intro x hx
    let v : V := ⟨x,hA hx⟩
    refine ⟨v, ?_,rfl⟩
    exact (local_flag_mem_image d A _).mpr ⟨v,hx,rfl⟩
  · rintro x ⟨v,hv,rfl⟩
    obtain ⟨w,hw,he⟩ := (local_flag_mem_image d A _).mp hv
    have heq : w = v := d.coordinate.injective he
    exact heq ▸ hw

theorem local_flag_preimage_simple (A : Subgroup G) (hA : A ≤ V) :
    A = TransvectionParabolic.EarlierCore.flagPreimage d.coordinate (local_flag_image d A) :=
  local_flag_preimage d A hA

theorem local_flag_preimage_cover (A : Subgroup G) (hA : A ≤ V) :
    A = ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.flagPreimage
      d.coordinate.toMonoidHom (local_flag_image d A) :=
  local_flag_preimage d A hA

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion

end
