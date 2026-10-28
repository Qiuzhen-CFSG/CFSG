module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.M22Shadow.SixDimensional.TransvectionCase.Marked

/-!
# Interfaces between recognition and the local section comparison

The seven-point model is an equivariant isomorphism for the faithful image
of actual conjugation. The natural local section is an explicit action of
A₅ in the image of N_L(V), with an intertwining isomorphism to the natural
SL₂(4) module. Neither interface asserts that its data exist.

The two constructions can be carried out independently. Recognition must
produce the former from the full G.6.4 alternatives; the preceding local
action supplies the latter. The marked first transvection centralizes this
local image because its lift belongs to T_C. No lift of A₅ into M is used.

Source: Aschbacher–Smith, proof of Lemma 16.4.7, printed p.1187.
-/

@[expose] public section

open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow.SixDimensional.TransvectionCase
open Subgroup Matrix BinaryPermutation BinaryPermutation.SevenPointChiefFactor
variable {G : Type*} [Group G]
variable (L : Subgroup G) (g r z : G) [IsElementaryAbelian 2 (shadowSpace L r z)]

/-- A genuine model for the whole faithful image and its module. -/
structure SevenPointModel where
  groupEquiv : image L g r z ≃* Equiv.Perm Seven
  moduleEquiv : Space L r z ≃ₗ[ZMod 2] core Seven
  intertwines : ∀ a v, moduleEquiv (a.val v) =
    coreRepresentation Seven (groupEquiv a) (moduleEquiv v)

/-- The image of the actual relative local normalizer N_L(V). -/
noncomputable def localImage : Subgroup (BinaryLinear.GL (Space L r z)) :=
  ((linearAction L g r z).comp (inclusion (localNormalizer_le (L := L) (g := g)
    (r := r) (z := z)))).range

theorem localImage_le_image : localImage L g r z ≤ image L g r z := by
  rintro a ⟨n, rfl⟩
  exact ⟨inclusion localNormalizer_le n, rfl⟩

/-- The natural four-dimensional local section, expressed in the faithful
image. Local membership permits choosing lifts one element at a time and
does not assert the existence of a homomorphic lift. -/
structure NaturalLocalSection (F : Type*) [Field F] [CharP F 2] where
  field_card : Nat.card F = 4
  actor : Five →* image L g r z
  actor_injective : Function.Injective actor
  actor_local : ∀ a, (actor a).val ∈ localImage L g r z
  W : Submodule (ZMod 2) (Space L r z)
  U : Submodule (ZMod 2) W
  linearActor : Five →* Matrix.SpecialLinearGroup (Fin 2) F
  linearActor_injective : Function.Injective linearActor
  sectionEquiv : (W ⧸ U) ≃+ (Fin 2 → F)
  intertwines : ∀ a (w : W), ∃ w' : W,
    (actor a).val w.val = w'.val ∧
      sectionEquiv (U.mkQ w') = (linearActor a).val *ᵥ sectionEquiv (U.mkQ w)

variable {L g r z}

/-- The two actual group elements commute before passing to the faithful
image. This is the local compatibility needed in the seven-point model. -/
theorem MarkedTransvections.commutes_localImage {T : Sylow 2 G}
    (d : MarkedTransvections T L g r z)
    {a : BinaryLinear.GL (Space L r z)} (ha : a ∈ localImage L g r z) :
    Commute (linearAction L g r z d.first) a := by
  obtain ⟨n, rfl⟩ := ha
  have hc : Commute d.first (inclusion localNormalizer_le n) := by
    apply Subtype.ext
    exact (d.first_mem.2 n n.property.1).symm
  exact hc.map (linearAction L g r z)

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow.SixDimensional.TransvectionCase
