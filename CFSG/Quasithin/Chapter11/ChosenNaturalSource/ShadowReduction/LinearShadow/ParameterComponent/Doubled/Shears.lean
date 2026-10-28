module

public import Theory.Representation.SL3DoubledNaturalOffenders.Model
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.FinCases

/-!
# Reciprocal shears on two identical natural SL₃ modules

The plane radical acts by the same two shear coefficients on both copies.
Its full commutator is the sum of the two planes. Every nonzero vector on
the first transverse axis has the same nonzero commutator plane. These are
statements about the original ambient subgroup and its conjugation action.

Source: Aschbacher--Smith, 11.3.6, printed pp.772--773.
-/

@[expose] public noncomputable section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
namespace Shears
variable {F : Type*} [Field F]
abbrev Space (F : Type*) := Fin 2 → Fin 3 → F

def shear (a b : F) (v : Space F) : Space F :=
  fun i => ![v i 0 + a * v i 2, v i 1 + b * v i 2, v i 2]

def plane : Submodule F (Space F) where
  carrier := {v | ∀ i, v i 2 = 0}
  zero_mem' := by simp
  add_mem' := by intro v w hv hw i; simp [hv i,hw i]
  smul_mem' := by intro a v hv i; simp [hv i]

def axisPlane : Submodule F (Space F) where
  carrier := {v | v 0 2 = 0 ∧ v 1 = 0}
  zero_mem' := by simp
  add_mem' := by intro v w hv hw; exact ⟨by simp [hv.1,hw.1],by simp [hv.2,hw.2]⟩
  smul_mem' := by intro a v hv; exact ⟨by simp [hv.1],by simp [hv.2]⟩

def axisVector (t : F) : Space F := ![![0,0,t],0]

theorem shear_sub (a b : F) (v : Space F) :
    shear a b v - v = fun i => ![a * v i 2, b * v i 2, 0] := by
  ext i j
  fin_cases j <;> simp [shear]

def planeEquiv : plane (F := F) ≃ₗ[F] (Fin 2 → Fin 2 → F) where
  toFun v i j := v.val i (Fin.castSucc j)
  invFun v := ⟨fun i => ![v i 0,v i 1,0],by intro i; rfl⟩
  left_inv v := by
    apply Subtype.ext
    ext i j
    fin_cases j <;> simp [v.property i]
  right_inv v := by
    change (fun i j : Fin 2 => (![v i 0,v i 1,0] : Fin 3 → F) (Fin.castSucc j)) = v
    ext i j
    fin_cases j <;> rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Shears

variable {G F : Type*} [Group G] [Field F] {A B : Subgroup G}

/-- Coordinates for the actual reciprocal conjugation action. The two
surjectivity clauses specify the full plane radical, with identical action
on the two copies; no commutator or dimension conclusion is included. -/
structure ShearCoordinates (A B : Subgroup G) (F : Type*) [Field F] where
  normalized : A ≤ normalizer (B : Set G)
  coordinates : B ≃* Multiplicative (Shears.Space F)
  shear_action : ∀ a : A, ∃ p q : F, ∀ v : B,
    (coordinates (B.normalizerMonoidHom (inclusion normalized a) v)).toAdd =
      Shears.shear p q (coordinates v).toAdd
  realizes : ∀ p q : F, ∃ a : A, ∀ v : B,
    (coordinates (B.normalizerMonoidHom (inclusion normalized a) v)).toAdd =
      Shears.shear p q (coordinates v).toAdd

namespace ShearCoordinates
variable (d : ShearCoordinates A B F)

def lift (U : Submodule F (Shears.Space F)) : Subgroup G :=
  (U.toAddSubgroup.toSubgroup.comap d.coordinates.toMonoidHom).map B.subtype

theorem mem_lift (U : Submodule F (Shears.Space F)) (v : B) :
    (v : G) ∈ d.lift U ↔ (d.coordinates v).toAdd ∈ U := by
  constructor
  · rintro ⟨w,hw,he⟩
    exact (Subtype.ext he : w = v) ▸ hw
  · intro hv; exact ⟨v,hv,rfl⟩

def displacement (a : A) (v : B) : B :=
  B.normalizerMonoidHom (inclusion d.normalized a) v * v⁻¹

theorem displacement_coe (a : A) (v : B) :
    (d.displacement a v : G) = ⁅(a : G),(v : G)⁆ := rfl

theorem displacement_coordinates (a : A) (p q : F)
    (ha : ∀ v : B,
      (d.coordinates (B.normalizerMonoidHom (inclusion d.normalized a) v)).toAdd =
        Shears.shear p q (d.coordinates v).toAdd) (v : B) :
    (d.coordinates (d.displacement a v)).toAdd =
      fun i => ![p * (d.coordinates v).toAdd i 2,q * (d.coordinates v).toAdd i 2,0] := by
  simp only [displacement,map_mul,map_inv,toAdd_mul,toAdd_inv]
  rw [← sub_eq_add_neg,ha,Shears.shear_sub]

def axisElement (t : F) : B := d.coordinates.symm (Multiplicative.ofAdd (Shears.axisVector t))

@[simp] theorem axisElement_coordinates (t : F) :
    (d.coordinates (d.axisElement t)).toAdd = Shears.axisVector t :=
  congrArg Multiplicative.toAdd (d.coordinates.apply_symm_apply _)

/-- Every plane vector is a product of two actual displacements, one per copy. -/
theorem commutator_eq_plane : ⁅A,B⁆ = d.lift Shears.plane := by
  apply le_antisymm
  · apply commutator_le.mpr
    intro a ha v hv
    let a' : A := ⟨a,ha⟩
    let v' : B := ⟨v,hv⟩
    change (d.displacement a' v' : G) ∈ d.lift Shears.plane
    rw [d.mem_lift]
    obtain ⟨p,q,he⟩ := d.shear_action a'
    rw [d.displacement_coordinates a' p q he]
    intro i
    rfl
  · rintro w ⟨v,hv,rfl⟩
    let u := (d.coordinates v).toAdd
    have hu : ∀ i, u i 2 = 0 := hv
    obtain ⟨a,ha⟩ := d.realizes (u 0 0) (u 0 1)
    obtain ⟨b,hb⟩ := d.realizes (u 1 0) (u 1 1)
    let v₀ := d.axisElement 1
    let v₁ := d.coordinates.symm (Multiplicative.ofAdd ![0,![0,0,1]])
    have he : d.displacement a v₀ * d.displacement b v₁ = v := by
      apply d.coordinates.injective
      apply Multiplicative.toAdd.injective
      rw [map_mul,toAdd_mul,d.displacement_coordinates a _ _ ha,
        d.displacement_coordinates b _ _ hb]
      simp only [v₀,v₁,axisElement_coordinates,MulEquiv.apply_symm_apply]
      change (fun i => ![u 0 0 * Shears.axisVector 1 i 2,
        u 0 1 * Shears.axisVector 1 i 2,0]) +
        (fun i => ![u 1 0 * (![0,![0,0,1]] : Shears.Space F) i 2,
        u 1 1 * (![0,![0,0,1]] : Shears.Space F) i 2,0]) = u
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Shears.axisVector,hu]
    have hc := mul_mem (commutator_mem_commutator a.property v₀.property)
      (commutator_mem_commutator b.property v₁.property)
    change (d.displacement a v₀ * d.displacement b v₁ : B).val ∈ ⁅A,B⁆ at hc
    rwa [he] at hc

variable [CharP F 2]

include d in
/-- Every element of the marked doubled module has square one. -/
theorem element_square (v : B) : (v : G)^2 = 1 := by
  have he : v^2 = 1 := by
    apply d.coordinates.injective
    apply Multiplicative.toAdd.injective
    rw [map_pow,map_one]
    change (2 : ℕ) • (d.coordinates v).toAdd = 0
    rw [two_smul]
    ext i j
    exact CharTwo.add_self_eq_zero _
  exact congrArg Subtype.val he

/-- Every nonzero transverse vector in the first copy has the same full plane
as its commutator with the reciprocal actor. -/
theorem axis_commutator (t : F) (ht : t ≠ 0) :
    ⁅zpowers (d.axisElement t : G),A⁆ = d.lift Shears.axisPlane := by
  rw [commutator_comm]
  apply le_antisymm
  · apply commutator_le.mpr
    intro a ha v hv
    have hv' : v = 1 ∨ v = d.axisElement t := by
      obtain ⟨k,rfl⟩ := mem_zpowers_iff.mp hv
      rw [zpow_eq_zpow_emod' k (d.element_square _)]
      rcases Int.emod_two_eq_zero_or_one k with hk | hk
      · left; simp [hk]
      · right; simp [hk]
    rcases hv' with rfl | rfl
    · simp
    · change (d.displacement ⟨a,ha⟩ (d.axisElement t) : G) ∈ d.lift Shears.axisPlane
      rw [d.mem_lift]
      obtain ⟨p,q,he⟩ := d.shear_action ⟨a,ha⟩
      rw [d.displacement_coordinates _ p q he,d.axisElement_coordinates]
      constructor
      · rfl
      · ext j; fin_cases j <;> simp [Shears.axisVector]
  · rintro w ⟨v,hv,rfl⟩
    let u := (d.coordinates v).toAdd
    have hu : u 0 2 = 0 ∧ u 1 = 0 := hv
    obtain ⟨a,ha⟩ := d.realizes (u 0 0 / t) (u 0 1 / t)
    have he : d.displacement a (d.axisElement t) = v := by
      apply d.coordinates.injective
      apply Multiplicative.toAdd.injective
      rw [d.displacement_coordinates a _ _ ha,d.axisElement_coordinates]
      change (fun i => ![(u 0 0 / t) * Shears.axisVector t i 2,
        (u 0 1 / t) * Shears.axisVector t i 2,0]) = u
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Shears.axisVector,hu.1,hu.2,ht]
    have hc := commutator_mem_commutator a.property
      (mem_zpowers (d.axisElement t : G))
    change (d.displacement a (d.axisElement t) : G) ∈ ⁅A,zpowers (d.axisElement t : G)⁆ at hc
    rwa [he] at hc

omit [CharP F 2] in
/-- The nonzero plane is retained as a literal ambient subgroup. -/
theorem axisPlane_ne_bot : d.lift Shears.axisPlane ≠ ⊥ := by
  let w : B := d.coordinates.symm (Multiplicative.ofAdd ![![1,0,0],0])
  have hw : (w : G) ∈ d.lift Shears.axisPlane := by
    rw [d.mem_lift]
    change (d.coordinates w).toAdd 0 2 = 0 ∧ (d.coordinates w).toAdd 1 = 0
    simp [w]
  intro hz
  have hw1 : w = 1 := Subtype.ext (mem_bot.mp (hz ▸ hw))
  have he := congrArg (fun v : B => (d.coordinates v).toAdd 0 0) hw1
  simp [w] at he

/-- Nonzero transverse vectors really move the reciprocal actor. -/
theorem axis_not_central (t : F) (ht : t ≠ 0) :
    (d.axisElement t : G) ∉ centralizer (A : Set G) := by
  intro hc
  apply d.axisPlane_ne_bot
  rw [← d.axis_commutator t ht]
  exact commutator_eq_bot_iff_le_centralizer.mpr (zpowers_le.mpr hc)

theorem axis_quotient_not_central (t u : F) (htu : t ≠ u) :
    ((d.axisElement t : G) * (d.axisElement u : G)⁻¹) ∉ centralizer (A : Set G) := by
  have he : d.axisElement t * (d.axisElement u)⁻¹ = d.axisElement (t-u) := by
    apply d.coordinates.injective
    apply Multiplicative.toAdd.injective
    rw [map_mul,map_inv,toAdd_mul,toAdd_inv,
      d.axisElement_coordinates,d.axisElement_coordinates,d.axisElement_coordinates]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Shears.axisVector,sub_eq_add_neg]
  change ((d.axisElement t * (d.axisElement u)⁻¹ : B) : G) ∉ _
  rw [he]
  exact d.axis_not_central (t-u) (sub_ne_zero.mpr htu)

omit [CharP F 2] in
/-- The subgroup cut out by vector coordinates has the same cardinality. -/
def liftEquiv (U : Submodule F (Shears.Space F)) : U ≃ d.lift U where
  toFun u := ⟨d.coordinates.symm (Multiplicative.ofAdd u.val),
    (d.mem_lift U _).mpr (by simp [u.property])⟩
  invFun v := ⟨(d.coordinates ⟨v.val,map_subtype_le _ v.property⟩).toAdd,
    (d.mem_lift U _).mp v.property⟩
  left_inv u := by apply Subtype.ext; simp
  right_inv v := by
    apply Subtype.ext
    exact congrArg (fun w : B => (w : G)) (d.coordinates.symm_apply_apply _)

include d in
omit [CharP F 2] in
/-- The reciprocal doubled commutator has rank 4n over the prime field. -/
theorem commutator_card [Finite F] (n : ℕ) (hF : Nat.card F = 2^n) :
    Nat.card (⁅A,B⁆ : Subgroup G) = 2^(4*n) := by
  rw [d.commutator_eq_plane,← Nat.card_congr (d.liftEquiv Shears.plane),
    Nat.card_congr Shears.planeEquiv.toEquiv,Nat.card_fun,Nat.card_fun,
    Nat.card_fin,hF,← pow_mul,← pow_mul]
  congr 1
  omega

end ShearCoordinates
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
