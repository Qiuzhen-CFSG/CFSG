module
public import Theory.SpecificGroups.SymplecticFour.QuadraticPlane
public import Theory.Representation.SymplecticNaturalNormalizer.QuadraticOuter
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.EmbeddedFixedIndex

/-!
# Quadratic actors in the original symplectic natural module

A quadratic symplectic actor has isotropic displacement, so its natural fixed
quotient has order at most the square of the field order. In a faithful ambient
field-four action, an actor of order greater than two is inner by the quadratic
field-automorphism bound. Its moving index is therefore at most sixteen.
The embedded version retains the whole seed and the literal actor map.

The source application is the unequal-mover selection in MS93 (5.5),
printed pp.915--917, through SourceComparison.OriginalQuadraticActors.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Theory.SpecificGroups.SymplecticFour
variable {F G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [Group G]

omit [CharP F 2] in
/-- Isotropic displacement bounds the fixed quotient of a quadratic natural actor. -/
theorem quadratic_natural_fixed_index_le_square (A : Subgroup (Sp F))
    (hq : ∀ x ∈ A, ∀ y ∈ A, ∀ v : Vector F, x • (y • v-v)=y • v-v) :
    Nat.card (Vector F ⧸ BinaryOffender.fixedSpace
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)) A) ≤ Nat.card F ^ 2 := by
  have hfix : BinaryOffender.fixedSpace
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)) A =
      (TwoLocalCover.fixedSpace A).restrictScalars (ZMod 2) := by
    ext v
    constructor
    · intro h x hx
      exact h ⟨x,hx⟩
    · intro h x
      exact h x.val x.property
  rw [hfix,Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv (ZMod 2) (TwoLocalCover.fixedSpace A)).toEquiv]
  rw [Module.natCard_eq_pow_finrank (K := F)]
  apply Nat.pow_le_pow_right (Nat.card_pos)
  have hdim := TwoLocalCover.finrank_le_two_of_isotropic (displacementSpace A)
    (quadratic_displacement_isotropic A hq)
  have hperp := LinearMap.BilinForm.finrank_orthogonal
    (W := displacementSpace A) TwoLocalCover.form_nondegenerate
  rw [orthogonal_displacementSpace] at hperp
  have hquot := (TwoLocalCover.fixedSpace A).finrank_quotient_add_finrank
  have hle := (displacementSpace A).finrank_le
  omega

/-- A quadratic ambient actor of order greater than two is inner and moves at most sixteen cosets. -/
theorem large_quadratic_ambient_fixed_index_le_sixteen
    (hF : Nat.card F = 4) (B : Subgroup G) [B.Normal]
    (hcent : centralizer (B : Set G) ≤ B)
    (e : B ≃* Sp F) (ρ : Representation (ZMod 2) G (Vector F))
    (hfaith : Function.Injective ρ)
    (hB : ∀ b : B, ∀ w, ρ (b:G) w = symplecticNatural 2 (e b) w)
    (A : Subgroup G) (hq : IsQuadratic ρ A) (hlarge : 2 < Nat.card A) :
    Nat.card (Vector F ⧸ BinaryOffender.fixedSpace ρ A) ≤ 16 := by
  have hAB := SymplecticNaturalNormalizer.le_component_of_quadratic_two_lt_card
    hF B hcent e ρ hfaith hB A hq hlarge
  let E := (A.subgroupOf B).map e.toMonoidHom
  let σ := restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)
  have hqE : ∀ x ∈ E, ∀ y ∈ E, ∀ v : Vector F, x • (y • v-v)=y • v-v := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ v
    have h := hq x.val hx y.val hy v
    simpa only [hB,Representation.symplecticNatural_apply,smul_eq_mulVec,
      MulEquiv.coe_toMonoidHom] using h
  have hi := quadratic_natural_fixed_index_le_square E hqE
  rw [hF] at hi
  have he := fixedCodim_map_equivariant (ρ.comp B.subtype) σ e.toMonoidHom
    (LinearEquiv.refl _ _) (fun b v => hB b v) (A.subgroupOf B)
  have hs := fixedCodim_map_equivariant (ρ.comp B.subtype) ρ B.subtype
    (LinearEquiv.refl _ _) (fun _ _ => rfl) (A.subgroupOf B)
  rw [map_subgroupOf_eq_of_le hAB] at hs
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hi
  change 2 ^ fixedCodim ρ A ≤ 16
  rw [←hs,he]
  exact hi

variable {D : Type*} [Group D]
open scoped commutatorElement in
/-- A quadratic action on the entire embedded natural seed has small moving
index; the original actor kernel is retained. -/
theorem large_quadratic_embedded_fixed_index_le_sixteen
    (hF : Nat.card F = 4) (B : Subgroup G) [B.Normal]
    (hcent : centralizer (B : Set G) ≤ B)
    (e : B ≃* Sp F) (ρ : Representation (ZMod 2) G (Vector F))
    (hfaith : Function.Injective ρ)
    (hB : ∀ b : B, ∀ w, ρ (b:G) w = symplecticNatural 2 (e b) w)
    (V E : Subgroup D) (q : D →* G)
    (j : Multiplicative (Vector F) →* D) (hj : Function.Injective j) (hjr : j.range = V)
    (hact : ∀ a v, j (Multiplicative.ofAdd (ρ (q a) v)) =
      a * j (Multiplicative.ofAdd v) * a⁻¹)
    (hlarge : 2 < Nat.card (E.map q))
    (hquad : ⁅E,V⁆ ≤ centralizer (E : Set D)) :
    (centralizer (E : Set D)).relIndex V ≤ 16 := by
  have hq : IsQuadratic ρ (E.map q) := by
    rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ v
    apply Multiplicative.ofAdd.injective
    apply hj
    have hcomm : j (Multiplicative.ofAdd (ρ (q b) v-v)) =
        ⁅b,j (Multiplicative.ofAdd v)⁆ := by
      rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
      rfl
    have hc := hquad (commutator_mem_commutator hb
      (show j (Multiplicative.ofAdd v) ∈ V from hjr ▸ ⟨_,rfl⟩)) a ha
    rw [hact,hcomm,hc,mul_inv_cancel_right]
  have hi := large_quadratic_ambient_fixed_index_le_sixteen
    hF B hcent e ρ hfaith hB (E.map q) hq hlarge
  have he := embedded_centralizer_index ρ V E j hj hjr (q.comp E.subtype)
    (fun a v => hact a.val v)
  have hr : (q.comp E.subtype).range = E.map q := by
    rw [MonoidHom.range_comp,E.range_subtype]
  rw [hr] at he
  rw [he]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hi
  exact hi
end Theory.SpecificGroups.SymplecticFour
