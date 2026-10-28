module
public import Theory.GroupTheory.SimpleSectionAction.Surjective
public import Theory.GroupTheory.SimpleSectionAction.Embedding
public import Theory.GroupTheory.SolvableResidual

/-!
# Perfect presentations of simple sections and their quotient lifts

A finite nonabelian simple section has a presentation with perfect upper
group: restrict its projection to the terminal derived subgroup. This preserves
the simple carrier, but need not preserve its stabilizer.

For a section whose upper group is already perfect, there is an exact lifting
construction through any surjection. Take the perfect residual of the preimage
upper group and restrict the original projection. Surjectivity on the upper and
lower endpoints proves one stabilizer inclusion; characteristicness of the
residual proves the converse lifting. Computing conjugation on representatives
then identifies the entire induced automorphism extension.

Source: the quotient induction in Aschbacher--Smith, E.1.11, printed p.212.
The perfect-section formulation also avoids stabilizer enlargement in the YT
induction, since perfect subgroups of YT lie in Y.
-/

@[expose] public section
open Subgroup
namespace ChiefFactor.SimpleSection
universe u v w
variable {G : Type u} {H : Type v} {L : Type w}
variable [Group G] [Group H] [Group L]

/-- The perfect residual of the preimage of the upper endpoint. -/
def perfectPreimage (s : SimpleSection H L) (f : G →* H) : Subgroup G :=
  (solvableResidual (s.subgroup.comap f)).map (s.subgroup.comap f).subtype

theorem perfectPreimage_subnormal (s : SimpleSection H L) (f : G →* H) :
    (s.perfectPreimage f).IsSubnormal :=
  (inferInstance : (solvableResidual (s.subgroup.comap f)).Normal).isSubnormal.trans'
    (s.subnormal.comap f)

instance perfectPreimage_perfect [Finite G] (s : SimpleSection H L) (f : G →* H) :
    Group.IsPerfect (s.perfectPreimage f) := Group.IsPerfect.map _

theorem map_perfectPreimage [Finite G] (s : SimpleSection H L)
    [Group.IsPerfect s.subgroup] (f : G →* H) (hf : Function.Surjective f) :
    (s.perfectPreimage f).map f = s.subgroup := by
  rw [perfectPreimage, map_solvableResidual_comap f hf, solvableResidual_eq_top,
    ← MonoidHom.range_eq_map, range_subtype]

/-- The restriction of the original quotient homomorphism, with its actual values. -/
def perfectPreimageMap (s : SimpleSection H L) (f : G →* H) :
    s.perfectPreimage f →* s.subgroup where
  toFun x := ⟨f x, by
    obtain ⟨y, _, he⟩ := x.property
    exact he ▸ y.property⟩
  map_one' := Subtype.ext f.map_one
  map_mul' x y := Subtype.ext (f.map_mul x y)

theorem perfectPreimageMap_surjective [Finite G] (s : SimpleSection H L)
    [Group.IsPerfect s.subgroup] (f : G →* H) (hf : Function.Surjective f) :
    Function.Surjective (s.perfectPreimageMap f) := by
  intro x
  obtain ⟨y, hy, he⟩ := (s.map_perfectPreimage f hf).ge x.property
  exact ⟨⟨y, hy⟩, Subtype.ext he⟩

/-- A perfect section lifts with perfect upper endpoint. -/
noncomputable def perfectLift [Finite G] (s : SimpleSection H L)
    [Group.IsPerfect s.subgroup] (f : G →* H) (hf : Function.Surjective f) :
    SimpleSection G L := by
  let := s.simple
  exact ChiefFactor.simpleSectionOfSurjective (s.perfectPreimage f)
    (s.perfectPreimage_subnormal f) (s.projection.comp (s.perfectPreimageMap f))
    (s.projection_surjective.comp (s.perfectPreimageMap_surjective f hf))

instance perfectLift_perfect [Finite G] (s : SimpleSection H L)
    [Group.IsPerfect s.subgroup] (f : G →* H) (hf : Function.Surjective f) :
    Group.IsPerfect (s.perfectLift f hf).subgroup := by
  change Group.IsPerfect (s.perfectPreimage f)
  infer_instance

theorem perfectLift_projection [Finite G] (s : SimpleSection H L)
    [Group.IsPerfect s.subgroup] (f : G →* H) (hf : Function.Surjective f)
    (x : (s.perfectLift f hf).subgroup) :
    (s.perfectLift f hf).projection x = s.projection (s.perfectPreimageMap f x) := rfl

theorem perfectLift_kernelImage [Finite G] (s : SimpleSection H L)
    [Group.IsPerfect s.subgroup] (f : G →* H) (hf : Function.Surjective f) :
    (s.perfectLift f hf).kernelImage = s.perfectPreimage f ⊓ s.kernelImage.comap f := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, ⟨s.perfectPreimageMap f y, (s.projection_eq_one _).mp hy, rfl⟩⟩
  · rintro ⟨hx, y, hy, he⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    change s.projection (s.perfectPreimageMap f ⟨x, hx⟩) = 1
    apply (s.projection_eq_one _).mpr
    have hyx : s.perfectPreimageMap f ⟨x, hx⟩ = y := Subtype.ext he.symm
    exact hyx.symm ▸ hy

theorem map_perfectLift_kernelImage [Finite G] (s : SimpleSection H L)
    [Group.IsPerfect s.subgroup] (f : G →* H) (hf : Function.Surjective f) :
    (s.perfectLift f hf).kernelImage.map f = s.kernelImage := by
  rw [s.perfectLift_kernelImage]
  ext x
  constructor
  · rintro ⟨y, ⟨_, hy⟩, rfl⟩
    exact hy
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz⟩ := s.perfectPreimageMap_surjective f hf y
    exact ⟨z, ⟨z.property, by
      change f z ∈ s.kernelImage
      rw [show f z = (y : H) from congrArg Subtype.val hz]
      exact ⟨y, hy, rfl⟩⟩, congrArg Subtype.val hz⟩

private theorem normalizer_le_perfectPreimage_normalizer (s : SimpleSection H L)
    (f : G →* H) : normalizer (s.subgroup.comap f) ≤ normalizer (s.perfectPreimage f : Set G) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨y, hy, rfl⟩ := hx
  let a := (s.subgroup.comap f).normalizerMonoidHom ⟨g, hg⟩
  refine ⟨a y, ?_, rfl⟩
  exact map_solvableResidual_le a.toMonoidHom (mem_map_of_mem a.toMonoidHom hy)

/-- Every source stabilizer element maps to an actual target stabilizer element. -/
def perfectLiftStabilizerMap [Finite G] (s : SimpleSection H L)
    [Group.IsPerfect s.subgroup] (f : G →* H) (hf : Function.Surjective f)
    (T : Subgroup G) :
    (s.perfectLift f hf).stabilizer T →* s.stabilizer (T.map f) where
  toFun g := ⟨f g, mem_map_of_mem f g.property.1, by
    have hu := ((s.perfectPreimage f).le_normalizer_map f)
      (mem_map_of_mem f g.property.2.1)
    have hk := ((s.perfectLift f hf).kernelImage.le_normalizer_map f)
      (mem_map_of_mem f g.property.2.2)
    rw [s.map_perfectPreimage f hf] at hu
    rw [s.map_perfectLift_kernelImage f hf] at hk
    exact ⟨hu, hk⟩⟩
  map_one' := Subtype.ext f.map_one
  map_mul' x y := Subtype.ext (f.map_mul x y)

/-- Perfect lifting loses no elements of the target actor. -/
theorem perfectLiftStabilizerMap_surjective [Finite G] (s : SimpleSection H L)
    [Group.IsPerfect s.subgroup] (f : G →* H) (hf : Function.Surjective f)
    (T : Subgroup G) : Function.Surjective (s.perfectLiftStabilizerMap f hf T) := by
  intro x
  obtain ⟨y, hy, he⟩ := x.property.1
  have hU : y ∈ normalizer (s.subgroup.comap f) := by
    rw [← comap_normalizer_eq_of_surjective _ hf]
    change f y ∈ normalizer s.subgroup
    exact he.symm ▸ x.property.2.1
  have hK : y ∈ normalizer (s.kernelImage.comap f) := by
    rw [← comap_normalizer_eq_of_surjective _ hf]
    change f y ∈ normalizer s.kernelImage
    exact he.symm ▸ x.property.2.2
  have hR := s.normalizer_le_perfectPreimage_normalizer f hU
  have hmem : y ∈ (s.perfectLift f hf).stabilizer T := by
    refine ⟨hy, hR, ?_⟩
    rw [s.perfectLift_kernelImage]
    exact inf_normalizer_le_normalizer_inf ⟨hR, hK⟩
  exact ⟨⟨y, hmem⟩, Subtype.ext he⟩

theorem perfectLift_action [Finite G] (s : SimpleSection H L)
    [Group.IsPerfect s.subgroup] (f : G →* H) (hf : Function.Surjective f)
    (T : Subgroup G) (g : (s.perfectLift f hf).stabilizer T) :
    (s.perfectLift f hf).action T g =
      s.action (T.map f) (s.perfectLiftStabilizerMap f hf T g) := by
  ext z
  obtain ⟨x, rfl⟩ := (s.perfectLift f hf).projection_surjective z
  rw [action_projection, perfectLift_projection, perfectLift_projection, action_projection]
  apply congrArg s.projection
  apply Subtype.ext
  change f ((g : G) * x * (g : G)⁻¹) = f g * f x * (f g)⁻¹
  simp only [map_mul, map_inv]

theorem perfectLift_extension [Finite G] (s : SimpleSection H L)
    [Group.IsPerfect s.subgroup] (f : G →* H) (hf : Function.Surjective f)
    (T : Subgroup G) :
    (s.perfectLift f hf).extension T = s.extension (T.map f) := by
  apply congrArg (fun K => MulAut.innerSubgroup L ⊔ K)
  ext a
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨s.perfectLiftStabilizerMap f hf T g, (s.perfectLift_action f hf T g).symm⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨k, rfl⟩ := s.perfectLiftStabilizerMap_surjective f hf T g
    exact ⟨k, s.perfectLift_action f hf T k⟩

/-- Every nonabelian simple composition-factor carrier has a presentation with
perfect upper endpoint. This assertion identifies the carrier, not the actor:
the stabilizer of this presentation can be larger than that of the original. -/
theorem exists_perfect_presentation [Finite G] (s : SimpleSection G L)
    (hn : ¬ IsMulCommutative L) :
    ∃ r : SimpleSection G L, Group.IsPerfect r.subgroup := by
  let := s.simple
  let : Group.IsPerfect L := ⟨by
    rcases (inferInstance : (commutator L).Normal).eq_bot_or_eq_top with hc | hc
    · exact False.elim (hn ((commutator_eq_bot_iff L).mp hc))
    · exact hc⟩
  let f : solvableResidual s.subgroup →* L :=
    s.projection.comp (solvableResidual s.subgroup).subtype
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp, range_subtype,
      map_solvableResidual_eq s.projection s.projection_surjective, solvableResidual_eq_top]
  let r : SimpleSection s.subgroup L := ChiefFactor.simpleSectionOfSurjective
    (solvableResidual s.subgroup) (inferInstance : (solvableResidual s.subgroup).Normal).isSubnormal
    f hf
  let : Group.IsPerfect r.subgroup := inferInstanceAs (Group.IsPerfect (solvableResidual s.subgroup))
  exact ⟨r.embed (r.subnormal.trans' s.subnormal), Group.IsPerfect.map s.subgroup.subtype⟩

end ChiefFactor.SimpleSection
