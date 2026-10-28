module
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks.Action

/-!
# Original subgroup coordinates and fixed vectors

Natural coordinates preserve cardinality, containment and joins of the
original subgroups of V. Fixation of their coordinate subspaces means
centralization of those actual subgroups. These transports retain the
literal conjugation map in the two-block construction of13.5.6,p.917.
-/

@[expose] public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks
open Section08.SourceCompletion Section07.NaturalAction
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
variable {G:Type*} [Group G] [Finite G] {T:Sylow 2 G}
  {L V V₁ V₂ V₃ M G₁:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)

theorem image_card (A : Subgroup G) (hA:A≤V) : Nat.card (image d A)=Nat.card A := by
  change Nat.card ((A.subgroupOf V).map d.coordinate.toMonoidHom)=Nat.card A
  rw [card_map_of_injective d.coordinate.injective]
  exact Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv

theorem image_mono {A B:Subgroup G} (h:A≤B) : image d A ≤ image d B := by
  rintro w ⟨v,hv,rfl⟩
  exact ⟨v,h hv,rfl⟩

theorem image_sup (A B:Subgroup G) (hA:A≤V) (hB:B≤V) :
    image d (A⊔B)=image d A⊔image d B := by
  simp only [image,subgroupOf_sup hA hB,Subgroup.map_sup,OrderIso.map_sup]

theorem centralizes_of_fixes (A X:Subgroup G) (hA:A≤L⊔(T:Subgroup G)) (hX:X≤V)
    (hf:∀a∈(actor d A hA).range,∀v∈image d X,naturalRepresentation (Fin 6) a v=v) :
    A≤centralizer (X:Set G) := by
  intro a ha x hx
  let xV:V:=⟨x,hX hx⟩
  have h := hf (actor d A hA ⟨a,ha⟩) ⟨⟨a,ha⟩,rfl⟩
    (d.coordinate xV).toAdd ((mem_image d X _).mpr ⟨xV,hx,rfl⟩)
  change naturalRepresentation (Fin 6) (permutation d ⟨a,hA ha⟩)
    (d.coordinate xV).toAdd=(d.coordinate xV).toAdd at h
  rw [←conjugation d ⟨a,hA ha⟩ xV] at h
  have he := congrArg Subtype.val (d.coordinate.injective h)
  change a*x*a⁻¹=x at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm
end CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks
