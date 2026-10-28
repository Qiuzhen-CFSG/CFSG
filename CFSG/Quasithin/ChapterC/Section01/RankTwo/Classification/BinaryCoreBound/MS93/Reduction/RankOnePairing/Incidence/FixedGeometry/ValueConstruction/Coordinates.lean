module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.Model
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.Values
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Duality

/-!
# Faithful coordinates for the fixed value spaces

The natural factor with trivial denominator is an actual isomorphism on Z.
The full component image extends its conjugation formula to every element
of M. Consequently local centralizers become pointwise matrix fixed spaces,
and ambient conjugates become images under the same marked natural action.
No local normalizer is replaced by a full parabolic preimage.

Source: Meierfrankenfeld--Stellmacher (1993), (1.7)(i), printed p.847.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.FixedGeometry.ValueConstruction
open Subgroup
universe u
variable {M : Type u} [Group M] {e : Extension (M := M)} {Z : Subgroup M}

/-- Coordinates of an ambient subgroup, restricted to the specified natural Z. -/
def coordinateImage (n : NaturalFactor e.projection (component e.projection e.flag) Z ⊥)
    (A : Subgroup M) : Subgroup VectorGroup :=
  (A.subgroupOf Z).map n.coordinates

variable (n : NaturalFactor e.projection (component e.projection e.flag) Z ⊥)

@[simp] theorem coordinates_mem_image (A : Subgroup M) (z : Z) :
    n.coordinates z ∈ coordinateImage n A ↔ (z : M) ∈ A := by
  constructor
  · rintro ⟨x, hx, he⟩
    have hxz : x = z := n.equivOfBot.injective he
    exact hxz ▸ hx
  · intro hz
    exact ⟨z, hz, rfl⟩

@[simp] theorem coordinateImage_bot : coordinateImage n ⊥ = ⊥ := by
  simp only [coordinateImage, bot_subgroupOf, Subgroup.map_bot]

@[simp] theorem coordinateImage_self : coordinateImage n Z = ⊤ := by
  rw [coordinateImage, subgroupOf_self, map_top_of_surjective _ n.surjective]

theorem coordinateImage_inf (A B : Subgroup M) :
    coordinateImage n (A ⊓ B) = coordinateImage n A ⊓ coordinateImage n B := by
  exact (congrArg (Subgroup.map n.coordinates) (comap_inf A B Z.subtype)).trans
    (map_inf _ _ n.coordinates n.equivOfBot.injective)

theorem coordinateImage_le_iff {A B : Subgroup M} (hAZ : A ≤ Z) :
    coordinateImage n A ≤ coordinateImage n B ↔ A ≤ B := by
  constructor
  · intro h a ha
    exact (coordinates_mem_image n B ⟨a, hAZ ha⟩).mp
      (h ((coordinates_mem_image n A ⟨a, hAZ ha⟩).mpr ha))
  · intro h
    exact map_mono (comap_mono h)

theorem coordinateImage_eq_bot_iff {A : Subgroup M} (hAZ : A ≤ Z) :
    coordinateImage n A = ⊥ ↔ A = ⊥ := by
  rw [← le_bot_iff, ← coordinateImage_bot n, coordinateImage_le_iff n hAZ, le_bot_iff]

theorem card_coordinateImage {A : Subgroup M} (hAZ : A ≤ Z) :
    Nat.card (coordinateImage n A) = Nat.card A := by
  rw [coordinateImage, card_map_of_injective n.equivOfBot.injective]
  exact Nat.card_congr (subgroupOfEquivOfLe hAZ).toEquiv

variable [Finite M] [Z.Normal]
    (hL : (component e.projection e.flag).map e.projection = ⊤)
include hL

/-- The original arbitrary marking controls every ambient conjugation. -/
theorem coordinates_conj (m : M) (z : Z) :
    n.coordinates (MulAut.conjNormal m z) =
      vectorAction (n.marking (e.projection m)) (n.coordinates z) := by
  apply Multiplicative.toAdd.injective
  exact Duality.natural_action_all e hL n m z (MulAut.conjNormal m z) rfl

theorem coordinateImage_conjugate (A : Subgroup M) (hAZ : A ≤ Z) (m : M) :
    coordinateImage n (conjugate m A) =
      (coordinateImage n A).map (vectorAction (n.marking (e.projection m))).toMonoidHom := by
  have hs : (conjugate m A).subgroupOf Z =
      (A.subgroupOf Z).map (MulAut.conjNormal m).toMonoidHom := by
    ext z
    constructor
    · rintro ⟨x, hx, he⟩
      exact ⟨⟨x, hAZ hx⟩, hx, Subtype.ext he⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  change ((conjugate m A).subgroupOf Z).map n.coordinates = _
  rw [hs, map_map, coordinateImage, map_map]
  congr 1
  apply MonoidHom.ext
  intro z
  exact coordinates_conj n hL m z

/-- A centralizer condition is exactly pointwise fixation in the matrix image. -/
theorem centralizer_iff_fixedSpace (Q : Subgroup M) (z : Z) :
    (z : M) ∈ centralizer (Q : Set M) ↔
      n.coordinates z ∈ fixedSpace ((Q.map e.projection).map n.marking.toMonoidHom) := by
  constructor
  · intro hc a ha
    obtain ⟨q, ⟨m, hm, rfl⟩, rfl⟩ := ha
    change vectorAction (n.marking (e.projection m)) (n.coordinates z) = n.coordinates z
    rw [← coordinates_conj n hL m z]
    apply congrArg n.coordinates
    apply Subtype.ext
    change m * (z : M) * m⁻¹ = (z : M)
    rw [hc m hm, mul_inv_cancel_right]
  · intro hf m hm
    have hv := hf _ (mem_map_of_mem n.marking.toMonoidHom
      (mem_map_of_mem e.projection hm))
    change vectorAction (n.marking (e.projection m)) (n.coordinates z) = n.coordinates z at hv
    rw [← coordinates_conj n hL m z] at hv
    have he := congrArg Subtype.val (n.equivOfBot.injective hv)
    exact mul_inv_eq_iff_eq_mul.mp he

theorem coordinateImage_centralizer (Q : Subgroup M) :
    coordinateImage n (Z ⊓ centralizer (Q : Set M)) =
      fixedSpace ((Q.map e.projection).map n.marking.toMonoidHom) := by
  ext v
  obtain ⟨z, rfl⟩ := n.surjective v
  rw [coordinates_mem_image]
  exact (and_iff_right z.property).trans (centralizer_iff_fixedSpace n hL Q z)

/-- Local core images identify the two literal value spaces. -/
theorem coordinateImage_localFixed (f : LocalFacts e Z) (j : Bool) :
    coordinateImage n (localFixed e Z j) = modelValues n.marking e.flag j := by
  rw [localFixed, coordinateImage_centralizer n hL, f.core_image]
  rfl

/-- The fixed-case hypothesis survives faithfully in the same marked model. -/
theorem model_fixed_ne_bot (f : LocalFacts e Z) (i : Bool)
    (h : Z ⊓ centralizer (localResidual (localParabolic e i) : Set M) ≠ ⊥) :
    fixedSpace (markedParabolic n.marking e.flag i) ≠ ⊥ := by
  have he := coordinateImage_centralizer n hL (localResidual (localParabolic e i))
  rw [f.residual_image] at he
  intro hz
  apply h
  exact (coordinateImage_eq_bot_iff n inf_le_left).mp (he.trans hz)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.FixedGeometry.ValueConstruction
