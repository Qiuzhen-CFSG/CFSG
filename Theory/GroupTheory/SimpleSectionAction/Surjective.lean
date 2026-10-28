module

public import Theory.GroupTheory.SimpleSectionAction

/-!
# Lifting section actions through surjections

A simple section of a quotient lifts by pulling back its upper subgroup and
kernel. Subnormality pulls back, and surjectivity identifies normalizers of
the pulled-back endpoints. Consequently the source stabilizer maps onto the
quotient stabilizer. Computing on representatives proves equality of the
induced automorphism images on the same simple carrier, hence equality of
the extensions by inner automorphisms.

This supplies the G/Y induction step of Aschbacher--Smith, E.1.11, p.212.
-/

@[expose] public section
open Subgroup
namespace ChiefFactor.SimpleSection
universe u v w
variable {G : Type u} {S : Type v} [Group G] [Group S]
variable {H : Type w} [Group H]

/-- The restriction of a homomorphism to the preimage of the upper endpoint. -/
def preimageMap (s : SimpleSection H S) (f : G →* H) :
    s.subgroup.comap f →* s.subgroup where
  toFun x := ⟨f x, x.property⟩
  map_one' := Subtype.ext f.map_one
  map_mul' x y := Subtype.ext (f.map_mul x y)

theorem preimageMap_surjective (s : SimpleSection H S) (f : G →* H)
    (hf : Function.Surjective f) : Function.Surjective (s.preimageMap f) := by
  intro x
  obtain ⟨y, hy⟩ := hf x
  exact ⟨⟨y, by change f y ∈ s.subgroup; rw [hy]; exact x.property⟩, Subtype.ext hy⟩

/-- A simple section lifts through a surjection to a subnormal simple section. -/
noncomputable def lift (s : SimpleSection H S) (f : G →* H)
    (hf : Function.Surjective f) : SimpleSection G S := by
  letI := s.simple
  exact ChiefFactor.simpleSectionOfSurjective (s.subgroup.comap f) (s.subnormal.comap f)
    (s.projection.comp (s.preimageMap f))
    (s.projection_surjective.comp (s.preimageMap_surjective f hf))

theorem lift_projection (s : SimpleSection H S) (f : G →* H)
    (hf : Function.Surjective f) (x : (s.lift f hf).subgroup) :
    (s.lift f hf).projection x = s.projection (s.preimageMap f x) := rfl

/-- Both endpoints, including the relatively normal kernel, really are pulled back. -/
theorem lift_kernelImage (s : SimpleSection H S) (f : G →* H)
    (hf : Function.Surjective f) : (s.lift f hf).kernelImage = s.kernelImage.comap f := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨s.preimageMap f y, (s.projection_eq_one _).mp hy, rfl⟩
  · rintro ⟨y, hy, he⟩
    have hx : f x ∈ s.subgroup := he ▸ y.property
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    change s.projection (s.preimageMap f ⟨x, hx⟩) = 1
    apply (s.projection_eq_one _).mpr
    have hyx : s.preimageMap f ⟨x, hx⟩ = y := Subtype.ext he.symm
    exact hyx.symm ▸ hy

/-- Stabilizing the lifted endpoints is exactly stabilizing the original endpoints. -/
theorem lift_stabilizer (s : SimpleSection H S) (f : G →* H)
    (hf : Function.Surjective f) (T : Subgroup G) :
    (s.lift f hf).stabilizer T = T ⊓ (s.stabilizer (T.map f)).comap f := by
  rw [stabilizer, lift_kernelImage]
  change T ⊓ (normalizer (s.subgroup.comap f) ⊓ normalizer (s.kernelImage.comap f)) = _
  rw [← comap_normalizer_eq_of_surjective _ hf, ← comap_normalizer_eq_of_surjective _ hf]
  ext x
  change (x ∈ T ∧ (f x ∈ normalizer s.subgroup ∧ f x ∈ normalizer s.kernelImage)) ↔
    (x ∈ T ∧ (f x ∈ T.map f ∧ (f x ∈ normalizer s.subgroup ∧ f x ∈ normalizer s.kernelImage)))
  exact ⟨fun h => ⟨h.1, mem_map_of_mem f h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩

/-- The surjection on literal section stabilizers. -/
def liftStabilizerMap (s : SimpleSection H S) (f : G →* H)
    (hf : Function.Surjective f) (T : Subgroup G) :
    (s.lift f hf).stabilizer T →* s.stabilizer (T.map f) where
  toFun x := ⟨f x, ((s.lift_stabilizer f hf T).le x.property).2⟩
  map_one' := Subtype.ext f.map_one
  map_mul' x y := Subtype.ext (f.map_mul x y)

theorem liftStabilizerMap_surjective (s : SimpleSection H S) (f : G →* H)
    (hf : Function.Surjective f) (T : Subgroup G) :
    Function.Surjective (s.liftStabilizerMap f hf T) := by
  intro x
  obtain ⟨y, hy, he⟩ := x.property.1
  have hmem : y ∈ (s.lift f hf).stabilizer T := by
    rw [s.lift_stabilizer f hf T]
    refine ⟨hy, ?_⟩
    change f y ∈ s.stabilizer (T.map f)
    rw [he]
    exact x.property
  exact ⟨⟨y, hmem⟩, Subtype.ext he⟩

/-- Equivariance on the same simple carrier, with no arbitrary action substituted. -/
theorem lift_action (s : SimpleSection H S) (f : G →* H)
    (hf : Function.Surjective f) (T : Subgroup G)
    (g : (s.lift f hf).stabilizer T) :
    (s.lift f hf).action T g = s.action (T.map f) (s.liftStabilizerMap f hf T g) := by
  ext z
  obtain ⟨x, rfl⟩ := (s.lift f hf).projection_surjective z
  rw [action_projection, lift_projection, lift_projection, action_projection]
  apply congrArg s.projection
  apply Subtype.ext
  change f ((g : G) * x * (g : G)⁻¹) = f g * f x * (f g)⁻¹
  simp only [map_mul, map_inv]

/-- Quotient descent preserves the entire induced automorphism image. -/
theorem lift_action_range (s : SimpleSection H S) (f : G →* H)
    (hf : Function.Surjective f) (T : Subgroup G) :
    ((s.lift f hf).action T).range = (s.action (T.map f)).range := by
  ext a
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨s.liftStabilizerMap f hf T g, (s.lift_action f hf T g).symm⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨h, rfl⟩ := s.liftStabilizerMap_surjective f hf T g
    exact ⟨h, s.lift_action f hf T h⟩

theorem lift_extension (s : SimpleSection H S) (f : G →* H)
    (hf : Function.Surjective f) (T : Subgroup G) :
    (s.lift f hf).extension T = s.extension (T.map f) := by
  simp only [extension, lift_action_range]

end ChiefFactor.SimpleSection
