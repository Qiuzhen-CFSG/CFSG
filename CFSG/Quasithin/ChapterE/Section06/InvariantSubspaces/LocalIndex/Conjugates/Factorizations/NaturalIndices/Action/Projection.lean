module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices.Coordinates

/-!
# The actual block quotient in ambient coordinates

The intrinsic commutator group is identified with its image under the block's
subtype inclusion. Composing that identification with the quotient map and a
block module model gives a surjective projection whose kernel is exactly the
ambient centralizer of the block. The model's intertwining law retains literal
conjugation by each internal actor.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.7 and C.1.12,
printed pp.123–124; the natural action used in C.5.6 (*), printed p.156.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices
open Subgroup
variable {G : Type*} [Group G]

/-- The intrinsic commutator layer and its literal image in the ambient group. -/
noncomputable def intrinsicModuleEquiv (L : Subgroup G) : ChapterC.blockU L ≃* U L :=
  (ChapterC.blockU L).equivMapOfInjective L.subtype L.subtype_injective

@[simp] theorem intrinsicModuleEquiv_coe (L : Subgroup G) (v : ChapterC.blockU L) :
    (intrinsicModuleEquiv L v : G) = ((v : L) : G) := rfl

/-- The intrinsic central layer is exactly the ambient centralizer on U. -/
theorem intrinsicModuleEquiv_mem_centralizer (L : Subgroup G) (v : ChapterC.blockU L) :
    (intrinsicModuleEquiv L v : G) ∈ centralizer (L : Set G) ↔
      v ∈ ChapterC.blockFixed L := by
  change (∀ y ∈ L, y * ((v : L) : G) = ((v : L) : G) * y) ↔ (v : L) ∈ center L
  rw [mem_center_iff]
  constructor
  · intro hh y
    exact Subtype.ext (hh y y.property)
  · intro hh y hy
    exact congrArg Subtype.val (hh ⟨y, hy⟩)

/-- A trivial intrinsic central layer gives a trivial ambient centralizer on U. -/
theorem centralizer_iff_eq_one_of_blockFixed_eq_bot {L : Subgroup G}
    (hz : ChapterC.blockFixed L = ⊥) (v : U L) :
    (v : G) ∈ centralizer (L : Set G) ↔ v = 1 := by
  obtain ⟨w, rfl⟩ := (intrinsicModuleEquiv L).surjective v
  rw [intrinsicModuleEquiv_mem_centralizer, hz, mem_bot,
    (intrinsicModuleEquiv L).map_eq_one_iff]

variable {V : Type*} [Group V]

/-- Transport of the actual quotient map through a prescribed quotient model. -/
noncomputable def quotientProjection (L : Subgroup G) (e : ChapterC.BlockModule L ≃* V) :
    U L →* V :=
  e.toMonoidHom.comp ((QuotientGroup.mk' (ChapterC.blockFixed L)).comp
    (intrinsicModuleEquiv L).symm.toMonoidHom)

@[simp] theorem quotientProjection_intrinsic (L : Subgroup G)
    (e : ChapterC.BlockModule L ≃* V) (v : ChapterC.blockU L) :
    quotientProjection L e (intrinsicModuleEquiv L v) =
      e (QuotientGroup.mk' (ChapterC.blockFixed L) v) := by
  simp [quotientProjection]

/-- The projection onto the model is surjective, including for nontrivial covers. -/
theorem quotientProjection_surjective (L : Subgroup G) (e : ChapterC.BlockModule L ≃* V) :
    Function.Surjective (quotientProjection L e) :=
  e.surjective.comp ((QuotientGroup.mk'_surjective _).comp
    (intrinsicModuleEquiv L).symm.surjective)

/-- No central layer is discarded when identifying the projection's kernel. -/
theorem quotientProjection_kernel (L : Subgroup G) (e : ChapterC.BlockModule L ≃* V)
    (v : U L) :
    quotientProjection L e v = 1 ↔ (v : G) ∈ centralizer (L : Set G) := by
  obtain ⟨w, rfl⟩ := (intrinsicModuleEquiv L).surjective v
  rw [quotientProjection_intrinsic, e.map_eq_one_iff,
    ← MonoidHom.mem_ker, QuotientGroup.ker_mk', intrinsicModuleEquiv_mem_centralizer]

/-- The intrinsic model intertwines literal ambient conjugation by internal actors. -/
theorem quotientProjection_conjugate {B : Type*} [Group B] {ρ : B →* MulAut V}
    {R L : Subgroup G} (model : ChapterC.BlockModuleModel L ρ)
    (hn : S R ≤ normalizer (U L : Set G)) (s : S R) (hs : (s : G) ∈ L) (v : U L) :
    quotientProjection L model.moduleIso (moduleConjugate hn s v) =
      ρ (model.quotientIso (QuotientGroup.mk' (pCore 2 L) ⟨s, hs⟩))
        (quotientProjection L model.moduleIso v) := by
  obtain ⟨w, rfl⟩ := (intrinsicModuleEquiv L).surjective v
  have hc : moduleConjugate hn s (intrinsicModuleEquiv L w) =
      intrinsicModuleEquiv L (ChapterC.blockConjugate L ⟨s, hs⟩ w) := by
    apply Subtype.ext
    rfl
  rw [hc, quotientProjection_intrinsic, quotientProjection_intrinsic]
  exact model.intertwining ⟨s, hs⟩ w

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices

end
