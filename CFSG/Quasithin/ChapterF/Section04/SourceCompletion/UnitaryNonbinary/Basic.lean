module
public import Theory.GroupTheory.Amalgam.GeneratedCompletion
public import Mathlib.Algebra.Group.End
public import Mathlib.GroupTheory.Subgroup.Center

/-!+# Source extensions of a marked unitary pair

The ambient group is a subgroup of the automorphism group of the concrete
projective group. Its two endpoints have the prescribed intersections with
the inner automorphisms, and the whole overlap supplements the inner group.
These are the algebraic clauses of Aschbacher–Smith F.4.3, printed p.274.
No completion recognition or geometry is stored in this data.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
open Subgroup Theory.GroupTheory
variable {B : Type*} [Group B]

/-- The actual inner automorphism subgroup. -/
abbrev inner (B : Type*) [Group B] : Subgroup (MulAut B) :=
  (MulAut.conj : B →* MulAut B).range

/-- Preservation of each native parabolic conjugacy class separately. -/
def PreservesTypes (P₀ P₁ : Subgroup B) (a : MulAut B) : Prop :=
  (∃ b : B, P₀.map a.toMonoidHom = P₀.map (MulAut.conj b).toMonoidHom) ∧
  (∃ b : B, P₁.map a.toMonoidHom = P₁.map (MulAut.conj b).toMonoidHom)

/-- A faithful diagram-preserving extension with its whole marked overlap.
The native parabolics and base group are parameters, not conclusion fields. -/
structure SourceExtension (P₀ P₁ : Subgroup B) where
  carrier : Subgroup (MulAut B)
  left : Subgroup (MulAut B)
  right : Subgroup (MulAut B)
  left_le : left ≤ carrier
  right_le : right ≤ carrier
  contains_inner : inner B ≤ carrier
  preserves_types : ∀ a ∈ carrier, PreservesTypes P₀ P₁ a
  left_inner : left ⊓ inner B = P₀.map MulAut.conj
  right_inner : right ⊓ inner B = P₁.map MulAut.conj
  factor : ∀ a ∈ carrier, ∃ b : B, ∃ d ∈ left ⊓ right, a = MulAut.conj b * d

namespace SourceExtension
variable {P₀ P₁ : Subgroup B} (E : SourceExtension P₀ P₁)

abbrev middle : Subgroup (MulAut B) := E.left ⊓ E.right

/-- Both maps are the literal inclusions from the whole intersection. -/
def amalgam : RankTwoAmalgam E.left E.middle E.right :=
  .ofSubgroups _ _ _ inf_le_left inf_le_right

/-- Native parabolics generate the full extension, including the outer part. -/
theorem endpoints_generate (hgen : P₀ ⊔ P₁ = ⊤) : E.left ⊔ E.right = E.carrier := by
  apply le_antisymm (sup_le E.left_le E.right_le)
  have hi : inner B ≤ E.left ⊔ E.right := by
    rw [show inner B = (⊤ : Subgroup B).map MulAut.conj from
      MonoidHom.range_eq_map _, ← hgen, Subgroup.map_sup]
    exact sup_le (E.left_inner ▸ inf_le_left.trans le_sup_left)
      (E.right_inner ▸ inf_le_left.trans le_sup_right)
  intro a ha
  obtain ⟨b, d, hd, rfl⟩ := E.factor a ha
  exact (E.left ⊔ E.right).mul_mem (hi ⟨b, rfl⟩) ((show E.left ≤ E.left ⊔ E.right from le_sup_left) hd.1)

/-- The canonical inclusion of the base into the extension. -/
def baseHom : B →* E.carrier :=
  (MulAut.conj : B →* MulAut B).codRestrict E.carrier
    (fun b => E.contains_inner ⟨b, rfl⟩)

theorem baseHom_injective (hi : Function.Injective (MulAut.conj : B →* MulAut B)) :
    Function.Injective E.baseHom := by
  intro b c h
  exact hi (congrArg Subtype.val h)

/-- The complete overlap intersects the inner group in the native overlap. -/
theorem middle_inner (hi : Function.Injective (MulAut.conj : B →* MulAut B)) :
    E.middle ⊓ inner B = (P₀ ⊓ P₁).map MulAut.conj := by
  rw [map_inf _ _ _ hi, ← E.left_inner, ← E.right_inner]
  ext a
  exact ⟨fun h => ⟨⟨h.1.1,h.2⟩,h.1.2,h.2⟩,
    fun h => ⟨⟨h.1.1,h.2.1⟩,h.1.2⟩⟩

theorem conj_mem_left_iff (hi : Function.Injective (MulAut.conj : B →* MulAut B))
    (b : B) : MulAut.conj b ∈ E.left ↔ b ∈ P₀ := by
  constructor
  · intro h
    have hh : MulAut.conj b ∈ P₀.map MulAut.conj := E.left_inner ▸ ⟨h, ⟨b, rfl⟩⟩
    exact (mem_map_iff_mem hi).mp hh
  · intro h
    exact (E.left_inner.symm ▸ (show MulAut.conj b ∈ P₀.map MulAut.conj from ⟨b,h,rfl⟩)).1

theorem conj_mem_right_iff (hi : Function.Injective (MulAut.conj : B →* MulAut B))
    (b : B) : MulAut.conj b ∈ E.right ↔ b ∈ P₁ := by
  constructor
  · intro h
    have hh : MulAut.conj b ∈ P₁.map MulAut.conj := E.right_inner ▸ ⟨h, ⟨b, rfl⟩⟩
    exact (mem_map_iff_mem hi).mp hh
  · intro h
    exact (E.right_inner.symm ▸ (show MulAut.conj b ∈ P₁.map MulAut.conj from ⟨b,h,rfl⟩)).1

/-- Factorization restricts to each endpoint, retaining the same whole overlap. -/
theorem left_factor (hi : Function.Injective (MulAut.conj : B →* MulAut B))
    (a : MulAut B) (ha : a ∈ E.left) :
    ∃ b ∈ P₀, ∃ d ∈ E.middle, a = MulAut.conj b * d := by
  obtain ⟨b,d,hd,he⟩ := E.factor a (E.left_le ha)
  refine ⟨b, (E.conj_mem_left_iff hi b).mp ?_,d,hd,he⟩
  have hh := E.left.mul_mem ha (E.left.inv_mem hd.1)
  rwa [he, mul_inv_cancel_right] at hh

theorem right_factor (hi : Function.Injective (MulAut.conj : B →* MulAut B))
    (a : MulAut B) (ha : a ∈ E.right) :
    ∃ b ∈ P₁, ∃ d ∈ E.middle, a = MulAut.conj b * d := by
  obtain ⟨b,d,hd,he⟩ := E.factor a (E.right_le ha)
  refine ⟨b, (E.conj_mem_right_iff hi b).mp ?_,d,hd,he⟩
  have hh := E.right.mul_mem ha (E.right.inv_mem hd.2)
  rwa [he, mul_inv_cancel_right] at hh

/-- The model completion lives in the full extension carrier. -/
def completion (hgen : P₀ ⊔ P₁ = ⊤) :
    RankTwoAmalgam.FaithfulCompletion E.amalgam (G := E.carrier) where
  left := inclusion E.left_le
  right := inclusion E.right_le
  compatible := rfl
  left_injective := inclusion_injective _
  right_injective := inclusion_injective _
  middle_injective := fun _ _ h => Subtype.ext (congrArg (fun a : E.carrier => a.val) h)
  generated := by
    apply map_injective E.carrier.subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_range, MonoidHom.map_range,
      ← MonoidHom.range_eq_map, range_subtype]
    change E.left.subtype.range ⊔ E.right.subtype.range = E.carrier
    rw [range_subtype, range_subtype, E.endpoints_generate hgen]

/-- Faithfulness does not imply this equality in general; here it follows
from the literal intersection used in the model extension. -/
theorem completion_overlap (hgen : P₀ ⊔ P₁ = ⊤) :
    (E.completion hgen).left.range ⊓ (E.completion hgen).right.range =
      (E.completion hgen).middle.range := by
  change (inclusion E.left_le).range ⊓ (inclusion E.right_le).range =
    ((inclusion E.left_le).comp (inclusion inf_le_left)).range
  rw [inclusion_range, inclusion_range]
  change E.left.comap E.carrier.subtype ⊓ E.right.comap E.carrier.subtype =
    (inclusion (inf_le_left.trans E.left_le)).range
  rw [inclusion_range, ← comap_inf]
  rfl

end SourceExtension
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
