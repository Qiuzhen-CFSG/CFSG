module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Naturality.Movement.Source.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Geometry.CoreAction

/-!
# Exact subgroup images and full-actor fixed preimages

Taking the actual image in Y/Z_alpha preserves membership in every subgroup
containing Z_alpha. Conjugation sends group commutators to linear action
differences. These identities identify the image of U_delta and the preimage
of the full actor's fixed space with the original subgroup D_delta. The early
geometric core bound supplies the required core displacement containment.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed p.907.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.CoreMovement.Source
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {i : Bool} {d : M}
  {marking : ParabolicMarking source i d}
namespace QuotientModule
variable (b : QuotientModule source i d marking)

/-- The actual image of a subgroup in the quotient coordinates. -/
noncomputable def image (A : Subgroup (FreeAmalgam R)) : Submodule (ZMod 2) b.Space :=
  AddSubgroup.toZModSubmodule 2 ((A.subgroupOf (Y source i d)).map b.coordinates).toAddSubgroup

/-- Membership in an image retains an actual representative in the named subgroup. -/
theorem mem_image (A : Subgroup (FreeAmalgam R)) (v : b.Space) :
    v ∈ b.image A ↔ ∃ x : Y source i d,
      (x : FreeAmalgam R) ∈ A ∧ (b.coordinates x).toAdd = v := by
  change (Multiplicative.ofAdd v) ∈ (A.subgroupOf (Y source i d)).map b.coordinates ↔ _
  constructor
  · rintro ⟨x, hx, he⟩
    exact ⟨x, hx, congrArg Multiplicative.toAdd he⟩
  · rintro ⟨x, hx, he⟩
    exact ⟨x, hx, Multiplicative.toAdd.injective he⟩

/-- For subgroups containing Z_alpha, no information is lost by taking the image. -/
theorem image_preimage (A : Subgroup (FreeAmalgam R)) (hZA : Z R (alpha R) ≤ A)
    (x : Y source i d) :
    (b.coordinates x).toAdd ∈ b.image A ↔ (x : FreeAmalgam R) ∈ A := by
  constructor
  · intro hx
    obtain ⟨y, hy, he⟩ := (b.mem_image A _).mp hx
    have he' : b.coordinates y = b.coordinates x := Multiplicative.toAdd.injective he
    have hk : x * y⁻¹ ∈ b.coordinates.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, he', mul_inv_cancel]
    rw [b.kernel] at hk
    have hh := A.mul_mem (hZA hk) hy
    change (x : FreeAmalgam R) * (y : FreeAmalgam R)⁻¹ * (y : FreeAmalgam R) ∈ A at hh
    simpa only [inv_mul_cancel_right] using hh
  · intro hx
    exact (b.mem_image A _).mpr ⟨x, hx, rfl⟩

/-- Conjugation inside the literal subgroup Y. -/
def conjugate (g : localFlagActor source (!i) d) (x : Y source i d) : Y source i d :=
  ⟨(g : FreeAmalgam R) * (x : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹,
    (mem_normalizer_iff.mp (Y_normalized source i d g.property) x).mp x.property⟩

/-- Group commutators map to linear action differences with their full actor. -/
theorem commutator_coordinates (g : localFlagActor source (!i) d) (x : Y source i d) :
    (b.coordinates (conjugate g x * x⁻¹)).toAdd =
      b.representation (marking.hom g) (b.coordinates x).toAdd - (b.coordinates x).toAdd := by
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv, ← sub_eq_add_neg]
  rw [b.action g x (conjugate g x) rfl]

/-- An exact translation of displacement containment. -/
theorem displacement_mem_image_iff (A : Subgroup (FreeAmalgam R))
    (hZA : Z R (alpha R) ≤ A) (g : localFlagActor source (!i) d) (x : Y source i d) :
    b.representation (marking.hom g) (b.coordinates x).toAdd - (b.coordinates x).toAdd ∈
      b.image A ↔ ⁅(g : FreeAmalgam R), (x : FreeAmalgam R)⁆ ∈ A := by
  rw [← b.commutator_coordinates, b.image_preimage A hZA]
  rfl

/-- Invariance is inherited from the actual ambient normalizer. -/
theorem image_invariant (A : Subgroup (FreeAmalgam R))
    (hA : localFlagActor source (!i) d ≤ normalizer A) (g : Actor) :
    b.image A ≤ (b.image A).comap (b.representation g) := by
  obtain ⟨a, rfl⟩ := marking.onto g
  intro v hv
  obtain ⟨x, hx, rfl⟩ := (b.mem_image A v).mp hv
  change b.representation (marking.hom a) (b.coordinates x).toAdd ∈ b.image A
  rw [← b.action a x (conjugate a x) rfl]
  exact (b.mem_image A _).mpr ⟨conjugate a x,
    (mem_normalizer_iff.mp (hA a.property) x).mp hx, rfl⟩

/-- The displayed layer is literally U_delta/Z_alpha. -/
theorem layer_preimage (x : Y source i d) :
    (b.coordinates x).toAdd ∈ b.image (secondFlagLayer source i d) ↔
      (x : FreeAmalgam R) ∈ secondFlagLayer source i d :=
  b.image_preimage _ (Z_le_secondFlagLayer source i d) x

/-- The full-actor fixed preimage in Y/U is exactly the source subgroup D. -/
theorem fixed_preimage (geometry : Geometry R) (hlarge : 2 < geometry.b R)
    [Finite M] (x : Y source i d) :
    (b.coordinates x).toAdd ∈
        fixedModulo b.representation (b.image (secondFlagLayer source i d)) ↔
      (x : FreeAmalgam R) ∈ D source i d := by
  let F := fixedModulo b.representation (b.image (secondFlagLayer source i d))
  let B := (F.toAddSubgroup.toSubgroup.comap b.coordinates).map (Y source i d).subtype
  have hBD : B ≤ D source i d := by
    apply le_commutatorPreimage
    · rintro y ⟨z, _, rfl⟩
      exact z.property
    · rw [commutator_comm]
      apply commutator_le.mpr
      intro g hg y hy
      obtain ⟨z, hz, rfl⟩ := hy
      let a : localFlagActor source (!i) d := ⟨g, hg⟩
      apply (b.displacement_mem_image_iff _ (Z_le_secondFlagLayer source i d) a z).mp
      exact (mem_fixedModulo _ _ _).mp hz (marking.hom a)
  constructor
  · intro hx
    exact hBD ⟨x, hx, rfl⟩
  · intro hx
    apply (mem_fixedModulo _ _ _).mpr
    intro g
    obtain ⟨a, rfl⟩ := marking.onto g
    apply (b.displacement_mem_image_iff _ (Z_le_secondFlagLayer source i d) a x).mpr
    have hc : ⁅localFlagActor source (!i) d, D source i d⁆ ≤ secondFlagLayer source i d := by
      rw [commutator_comm]
      exact D_commutator_actor source geometry hlarge i d
    exact commutator_le.mp hc a a.property x hx

/-- The source core commutator bound is the pencil's required displacement bound. -/
theorem core_displacement [Finite M] (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (hkernel : flagKernel source i = Q R (beta R)) :
    subspaceCommutator b.representation ⊤ modelCore ≤ b.image (secondFlagLayer source i d) := by
  apply Submodule.span_le.mpr
  rintro v ⟨g, hg, w, _, rfl⟩
  obtain ⟨a, ha, rfl⟩ := (show g ∈
      ((localFlagKernel source (!i) d).subgroupOf (localFlagActor source (!i) d)).map
        marking.hom by rwa [marking.core_image])
  obtain ⟨x, hx⟩ := b.onto (Multiplicative.ofAdd w)
  have he : (b.coordinates x).toAdd = w := congrArg Multiplicative.toAdd hx
  rw [← he]
  apply (b.displacement_mem_image_iff _ (Z_le_secondFlagLayer source i d) a x).mpr
  have hc : ⁅localFlagKernel source (!i) d, Y source i d⁆ ≤ secondFlagLayer source i d := by
    rw [commutator_comm]
    exact Moving.Y_core_le_second source geometry common early i hkernel d
  exact commutator_le.mp hc a ha x x.property


end QuotientModule
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.CoreMovement.Source
