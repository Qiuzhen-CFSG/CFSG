module
public import Theory.SpecificGroups.SymplecticFour.FixedPlaneDisplacement
public import Theory.Representation.QuadraticDuality
public import Mathlib.FieldTheory.Finiteness
/-!
# The plane of a large quadratic symplectic actor

The displacement space is perpendicular to the common fixed space. Each
actor embeds, by its displacement operator, into the linear maps from the
fixed quotient to the displacement space. If that space has dimension d,
this bounds the actor order by q^(d^2). Quadraticity makes the displacement
space isotropic, hence d <= 2; an actor of order greater than q therefore
has a self-orthogonal plane as both displacement space and fixed space.

This is the critical plane calculation in MS93 (3.3), printed p.867. It uses
the actual natural symplectic action and no transvection classification.
-/

public section
noncomputable section
open Representation
namespace Theory.SpecificGroups.SymplecticFour
open TwoLocalCover
variable {F : Type*} [Field F]

/-- The field-linear span of all natural displacements. -/
abbrev displacementSpace (A : Subgroup (Sp F)) : Submodule F (Vector F) :=
  Coinvariants.ker ((symplecticNatural 2).comp A.subtype)

/-- Passing from an actor map to its image preserves the displacement span. -/
theorem displacementSpace_range_eq {G : Type*} [Group G] (α : G →* Sp F) :
    displacementSpace α.range = Coinvariants.ker ((symplecticNatural 2).comp α) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,v⟩,rfl⟩
    obtain ⟨x,hx⟩ := g.property
    change symplecticNatural 2 g.val v-v ∈ _
    rw [←hx]
    exact Coinvariants.sub_mem_ker (ρ := (symplecticNatural 2).comp α) x v
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,v⟩,rfl⟩
    exact Coinvariants.sub_mem_ker
      (ρ := (symplecticNatural 2).comp α.range.subtype) ⟨α g,⟨g,rfl⟩⟩ v

/-- Symplecticity identifies the perpendicular displacement space with the fixed space. -/
theorem orthogonal_displacementSpace (A : Subgroup (Sp F)) :
    (form F).orthogonal (displacementSpace A) = fixedSpace A := by
  ext v
  constructor
  · intro hv g hg
    apply sub_eq_zero.mp
    apply form_nondegenerate.2
    intro w
    rw [map_sub]
    have h := hv _ (Coinvariants.sub_mem_ker
      (ρ := (symplecticNatural 2).comp A.subtype) (⟨g⁻¹,A.inv_mem hg⟩ : A) w)
    change form F (g⁻¹ • w-w) v = 0 at h
    rw [map_sub,LinearMap.sub_apply] at h
    have he := preserves_form g (g⁻¹ • w) v
    rw [smul_inv_smul] at he
    rw [he]
    exact h
  · intro hv
    have hs : displacementSpace A ≤ (form F v).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨g,w⟩,rfl⟩
      change form F v (g.val • w-w) = 0
      rw [map_sub]
      have he := preserves_form g.val v w
      rw [hv g.val g.property] at he
      exact sub_eq_zero.mpr he
    intro w hw
    exact form_alternating.eq_iff.mp (hs hw)

/-- Quadraticity means every displacement is fixed by every actor. -/
theorem displacementSpace_le_fixedSpace_of_quadratic (A : Subgroup (Sp F))
    (hq : ∀ x ∈ A, ∀ y ∈ A, ∀ v : Vector F, x • (y • v-v)=y • v-v) :
    displacementSpace A ≤ fixedSpace A := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g,v⟩,rfl⟩ x hx
  exact hq x hx g.val g.property v

/-- A quadratic symplectic actor has totally isotropic displacement. -/
theorem quadratic_displacement_isotropic (A : Subgroup (Sp F))
    (hq : ∀ x ∈ A, ∀ y ∈ A, ∀ v : Vector F, x • (y • v-v)=y • v-v) :
    ∀ x ∈ displacementSpace A, ∀ y ∈ displacementSpace A, form F x y = 0 := by
  intro x hx y hy
  have hh := displacementSpace_le_fixedSpace_of_quadratic A hq hy
  rw [←orthogonal_displacementSpace] at hh
  exact hh x hx

private def actorDisplacement (A : Subgroup (Sp F)) (g : A) :
    (Vector F ⧸ fixedSpace A) →ₗ[F] displacementSpace A :=
  (fixedSpace A).liftQ
    ((symplecticNatural 2 g.val - LinearMap.id).codRestrict (displacementSpace A)
      (fun v => Coinvariants.sub_mem_ker
        (ρ := (symplecticNatural 2).comp A.subtype) g v))
    (by
      intro v hv
      apply Subtype.ext
      change g.val • v-v=0
      exact sub_eq_zero.mpr (hv g.val g.property))

private theorem actorDisplacement_injective (A : Subgroup (Sp F)) :
    Function.Injective (actorDisplacement A) := by
  intro g h he
  apply Subtype.ext
  apply Subtype.ext
  apply Matrix.ext
  intro i k
  have hh := congrArg (fun f => (f ((fixedSpace A).mkQ (Pi.single k (1:F)))).val) he
  change g.val • (Pi.single k (1:F) : Vector F)-(Pi.single k (1:F) : Vector F) = h.val • (Pi.single k (1:F) : Vector F)-(Pi.single k (1:F) : Vector F) at hh
  have hs := congrFun (sub_left_inj.mp hh) i
  simpa [smul_eq_mulVec,Matrix.mulVec_single] using hs

variable [Finite F]

/-- Displacement operators inject the actor into a linear-map space of dimension d². -/
theorem card_actor_le_displacement_dimension (A : Subgroup (Sp F)) :
    Nat.card A ≤ Nat.card F ^ (Module.finrank F (displacementSpace A))^2 := by
  have hd : Module.finrank F (Vector F ⧸ fixedSpace A) =
      Module.finrank F (displacementSpace A) := by
    have h := (fixedSpace A).finrank_quotient_add_finrank
    have hc : Module.finrank F (fixedSpace A) = Module.finrank F (Vector F)-
        Module.finrank F (displacementSpace A) := by
      rw [←orthogonal_displacementSpace,
        LinearMap.BilinForm.finrank_orthogonal form_nondegenerate]
    rw [hc] at h
    have hle := (displacementSpace A).finrank_le
    omega
  let : Finite ((Vector F ⧸ fixedSpace A) →ₗ[F] displacementSpace A) :=
    Module.finite_of_finite F
  calc
    Nat.card A ≤ Nat.card ((Vector F ⧸ fixedSpace A) →ₗ[F] displacementSpace A) :=
      Nat.card_le_card_of_injective _ (actorDisplacement_injective A)
    _ = _ := by rw [Module.natCard_eq_pow_finrank (K := F),Module.finrank_linearMap (R := F) (S := F),hd,pow_two]

/-- Order greater than the field order forces a self-orthogonal displacement plane. -/
theorem large_quadratic_displacement_self_orthogonal (A : Subgroup (Sp F))
    (hq : ∀ x ∈ A, ∀ y ∈ A, ∀ v : Vector F, x • (y • v-v)=y • v-v)
    (hlarge : Nat.card F < Nat.card A) :
    (form F).orthogonal (displacementSpace A) = displacementSpace A := by
  have hle := finrank_le_two_of_isotropic (displacementSpace A)
    (quadratic_displacement_isotropic A hq)
  have hd : Module.finrank F (displacementSpace A) = 2 := by
    have hc := card_actor_le_displacement_dimension A
    have hp : 0 < Nat.card F := Nat.card_pos
    interval_cases hh : Module.finrank F (displacementSpace A) <;> simp at hc <;> omega
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [orthogonal_displacementSpace]
    exact displacementSpace_le_fixedSpace_of_quadratic A hq
  · rw [LinearMap.BilinForm.finrank_orthogonal form_nondegenerate,hd]
    simp [Vector]
end Theory.SpecificGroups.SymplecticFour
