module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.InductionConvention
public import Mathlib.RepresentationTheory.FiniteIndex

/-!
# Coordinates on the literal induction quotient

A finite right transversal gives a linear equivalence from Mathlib's induction
quotient to functions on the transversal. Evaluation of `Rep.indToCoind`
provides the forward map; the inverse is the sum of the specified induction
generators. We prove both inverses directly, so no dimension argument or
abstract choice of basis replaces the original quotient.

The formulas retain Mathlib's convention: a transition `t_i * g = b * t_j`
gives the coefficient `χ(b)⁻¹` for the actor `g⁻¹`. Distinct representatives
become a transversal when their number equals the number of left cosets,
using the explicit right-to-left conversion `Bt ↦ t⁻¹B`.

This supplies the representation-theoretic part of the SU₃(5) cubic comparison
motivated by Guralnick–Malle, Proposition 4.3, p.10. The coinduction map is from
Mathlib's `RepresentationTheory/FiniteIndex`, Copyright (c) 2025 Amelia
Livingston, Apache 2.0; its existing declarations are reused without alteration.
-/

open scoped Classical
open Representation Representation.SU3.FiveSmallModules.Degrees
@[expose] public noncomputable section
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.RightCoordinates
variable {K G : Type*} [Field K] [Group G] (B : Subgroup G) (χ : B →* Kˣ)
variable {ι : Type*} [DecidableEq ι] (t : ι → G)

def coordMap : IndV B.subtype (scalarCharacter χ) →ₗ[K] (ι → K) :=
  (LinearMap.pi fun i => (LinearMap.proj (t i)).comp
    (Submodule.subtype _)).comp (Rep.indToCoind (Rep.of (scalarCharacter χ)))

omit [DecidableEq ι] in
private theorem coordMap_mk_aux (g : G) (a : K) (i : ι) :
    coordMap B χ t (IndV.mk B.subtype (scalarCharacter χ) g a) i =
      Rep.indToCoindAux (Rep.of (scalarCharacter χ)) g a (t i) := by
  simp [coordMap, Rep.indToCoind, IndV.mk]
  rfl

theorem coordMap_mk (hsep : ∀ i j, t i * (t j)⁻¹ ∈ B → i = j) (i : ι) (a : K) :
    coordMap B χ t (IndV.mk B.subtype (scalarCharacter χ) (t i) a) = Pi.single i a := by
  ext j
  rw [coordMap_mk_aux, Pi.single_apply]
  by_cases h : j = i
  · subst j
    rw [if_pos rfl]
    exact Rep.indToCoindAux_self (A := Rep.of (scalarCharacter χ)) (t i) a
  · rw [if_neg h]
    apply Rep.indToCoindAux_of_not_rel
    intro hr
    exact h ((hsep i j (QuotientGroup.rightRel_apply.mp hr)).symm)

variable [Fintype ι]

def fromCoordinates : (ι → K) →ₗ[K] IndV B.subtype (scalarCharacter χ) :=
  ∑ i, (IndV.mk B.subtype (scalarCharacter χ) (t i)).comp (LinearMap.proj i)

omit [DecidableEq ι] in
@[simp] theorem fromCoordinates_apply (v : ι → K) :
    fromCoordinates B χ t v = ∑ i, IndV.mk B.subtype (scalarCharacter χ) (t i) (v i) := by
  simp [fromCoordinates]

@[simp] theorem fromCoordinates_single (i : ι) (a : K) :
    fromCoordinates B χ t (Pi.single i a) = IndV.mk B.subtype (scalarCharacter χ) (t i) a := by
  rw [fromCoordinates_apply, Finset.sum_eq_single i]
  · rw [Pi.single_apply, if_pos rfl]
  · intro j _ hj
    rw [Pi.single_apply, if_neg hj]
    exact map_zero _
  · simp

theorem fromCoordinates_coordMap
    (hsep : ∀ i j, t i * (t j)⁻¹ ∈ B → i = j)
    (hcover : ∀ g : G, ∃ i, ∃ b : B, g = b * t i) :
    (fromCoordinates B χ t).comp (coordMap B χ t) = LinearMap.id := by
  apply IndV.hom_ext
  intro g
  apply LinearMap.ext
  intro a
  obtain ⟨i, b, rfl⟩ := hcover g
  change fromCoordinates B χ t
    (coordMap B χ t (IndV.mk B.subtype (scalarCharacter χ) ((b : G) * t i) a)) = _
  rw [induced_mk_subgroup_mul, coordMap_mk B χ t hsep, fromCoordinates_single]
  exact (induced_mk_subgroup_mul B χ b (t i) a).symm

theorem coordMap_fromCoordinates (hsep : ∀ i j, t i * (t j)⁻¹ ∈ B → i = j) :
    (coordMap B χ t).comp (fromCoordinates B χ t) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  change coordMap B χ t (fromCoordinates B χ t v) = v
  rw [fromCoordinates_apply, map_sum]
  calc
    _ = ∑ i, Pi.single i (v i) := Finset.sum_congr rfl (fun i _ => coordMap_mk B χ t hsep i (v i))
    _ = v := Finset.univ_sum_single v

def equiv (hsep : ∀ i j, t i * (t j)⁻¹ ∈ B → i = j)
    (hcover : ∀ g : G, ∃ i, ∃ b : B, g = b * t i) :
    IndV B.subtype (scalarCharacter χ) ≃ₗ[K] (ι → K) :=
  LinearEquiv.ofLinearMap (coordMap B χ t) (fromCoordinates B χ t)
    (coordMap_fromCoordinates B χ t hsep)
    (fromCoordinates_coordMap B χ t hsep hcover)

@[simp] theorem equiv_symm_apply (hsep : ∀ i j, t i * (t j)⁻¹ ∈ B → i = j)
    (hcover : ∀ g : G, ∃ i, ∃ b : B, g = b * t i) (v : ι → K) :
    (equiv B χ t hsep hcover).symm v =
      ∑ i, IndV.mk B.subtype (scalarCharacter χ) (t i) (v i) :=
  fromCoordinates_apply B χ t v

@[simp] theorem equiv_mk (hsep : ∀ i j, t i * (t j)⁻¹ ∈ B → i = j)
    (hcover : ∀ g : G, ∃ i, ∃ b : B, g = b * t i) (i : ι) (a : K) :
    equiv B χ t hsep hcover (IndV.mk B.subtype (scalarCharacter χ) (t i) a) =
      Pi.single i a := coordMap_mk B χ t hsep i a

@[simp] theorem equiv_mk_subgroup (hsep : ∀ i j, t i * (t j)⁻¹ ∈ B → i = j)
    (hcover : ∀ g : G, ∃ i, ∃ b : B, g = b * t i) (i : ι) (b : B) (a : K) :
    equiv B χ t hsep hcover (IndV.mk B.subtype (scalarCharacter χ) ((b : G) * t i) a) =
      Pi.single i ((χ b : K)⁻¹ * a) := by
  rw [induced_mk_subgroup_mul, equiv_mk]

theorem equiv_action_mk (hsep : ∀ i j, t i * (t j)⁻¹ ∈ B → i = j)
    (hcover : ∀ g : G, ∃ i, ∃ b : B, g = b * t i)
    (g : G) (i j : ι) (b : B) (h : t i * g = b * t j) (a : K) :
    equiv B χ t hsep hcover
        (ind B.subtype (scalarCharacter χ) g⁻¹
          (IndV.mk B.subtype (scalarCharacter χ) (t i) a)) =
      Pi.single j ((χ b : K)⁻¹ * a) := by
  rw [ind_mk, inv_inv, h, equiv_mk_subgroup]

omit [Fintype ι] [DecidableEq ι] in
/-- Maps from the induction quotient are determined on a right transversal. -/
theorem hom_ext {V : Type*} [AddCommGroup V] [Module K V]
    (hcover : ∀ g : G, ∃ i, ∃ b : B, g = b * t i)
    {f g : IndV B.subtype (scalarCharacter χ) →ₗ[K] V}
    (h : ∀ i x, f (IndV.mk B.subtype (scalarCharacter χ) (t i) x) =
      g (IndV.mk B.subtype (scalarCharacter χ) (t i) x)) : f = g := by
  apply IndV.hom_ext
  intro s
  apply LinearMap.ext
  intro x
  obtain ⟨i, b, rfl⟩ := hcover s
  change f (IndV.mk B.subtype (scalarCharacter χ) ((b : G) * t i) x) =
    g (IndV.mk B.subtype (scalarCharacter χ) ((b : G) * t i) x)
  calc
    _ = f (IndV.mk B.subtype (scalarCharacter χ) (t i) ((χ b : K)⁻¹ * x)) :=
      congrArg f (induced_mk_subgroup_mul B χ b (t i) x)
    _ = g (IndV.mk B.subtype (scalarCharacter χ) (t i) ((χ b : K)⁻¹ * x)) := h i _
    _ = _ := (congrArg g (induced_mk_subgroup_mul B χ b (t i) x)).symm

omit [Field K] [Fintype ι] [DecidableEq ι] in
 theorem cover_of_card [Finite (G ⧸ B)] [Finite ι]
    (hsep : ∀ i j, t i * (t j)⁻¹ ∈ B → i = j)
    (hcard : Nat.card (G ⧸ B) = Nat.card ι) :
    ∀ g : G, ∃ i, ∃ b : B, g = b * t i := by
  let f : ι → G ⧸ B := fun i => QuotientGroup.mk ((t i)⁻¹)
  have hf : Function.Injective f := by
    intro i j hij
    apply hsep i j
    have h := QuotientGroup.leftRel_apply.mp (Quotient.exact hij)
    simpa only [inv_inv] using h
  have hs := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf, hcard.symm⟩).2
  intro g
  obtain ⟨i, hi⟩ := hs (QuotientGroup.mk g⁻¹)
  have hm : g * (t i)⁻¹ ∈ B := by
    have h := QuotientGroup.leftRel_apply.mp (Quotient.exact hi.symm)
    simpa only [inv_inv] using h
  exact ⟨i, ⟨g * (t i)⁻¹, hm⟩, by simp⟩

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.RightCoordinates
