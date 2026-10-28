module
public import Theory.Representation.BinaryParabolicExteriorSquare.CubicRestriction
public import Theory.Representation.BinaryConjugationSection.NormalizerAction
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.FinCases

/-!
# Coordinates on the binary plane radical

The upper-right two-by-two block embeds the additive binary four-space in
SL₄(2). Conjugation by the cubic rotating the first natural plane acts on
its two columns by the same binary cubic. Transport through the literal
normalizer gives the full radical representation; the cubic formula follows
from matrix multiplication, without a separate module-action premise.

For an ambient matrix quotient, `exists_section` constructs coordinates on
the original radical preimage. Its kernel is the intersection with the
original quotient kernel, and its action is original ambient conjugation.
The image identification with this model radical remains explicit.

Source application: Aschbacher–Smith, *The Classification of Quasithin
Groups*, 13.8.31(3), printed p.965, the two factors on O₂(L₀*).
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Representation.BinaryParabolicExteriorSquare.PlaneRadical
open PlaneSpan
abbrev Four := Fin 4 → Bit
abbrev SL := SL(4, Bit)

def matrix (v : Four) : Matrix (Fin 4) (Fin 4) Bit :=
  !![1,0,v 0,v 2; 0,1,v 1,v 3; 0,0,1,0; 0,0,0,1]

theorem matrix_det (v : Four) : (matrix v).det = 1 := by
  have ht : (matrix v).IsUpperTriangular := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [matrix]
  rw [Matrix.det_of_isUpperTriangular ht]
  simp [matrix, Fin.prod_univ_succ]

def element (v : Four) : SL := ⟨matrix v, matrix_det v⟩

theorem element_zero : element 0 = 1 := by
  apply Subtype.ext
  change matrix 0 = 1
  decide

theorem element_add (v w : Four) : element (v+w) = element v * element w := by
  apply Subtype.ext
  change matrix (v+w) = matrix v * matrix w
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

def embedding : Multiplicative Four →* SL where
  toFun v := element v.toAdd
  map_one' := element_zero
  map_mul' v w := element_add v.toAdd w.toAdd

theorem embedding_injective : Function.Injective embedding := by
  intro v w he
  have hh := congrArg Subtype.val he
  have h0 := congrArg (fun m => m 0 2) hh
  have h1 := congrArg (fun m => m 1 2) hh
  have h2 := congrArg (fun m => m 0 3) hh
  have h3 := congrArg (fun m => m 1 3) hh
  apply Multiplicative.toAdd.injective
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

def radical : Subgroup SL := embedding.range

def coordinates : radical ≃* Multiplicative Four :=
  (MonoidHom.ofInjective embedding_injective).symm

theorem coordinates_element (v : Four) :
    coordinates ⟨element v,⟨Multiplicative.ofAdd v,rfl⟩⟩ = Multiplicative.ofAdd v :=
  (MonoidHom.ofInjective embedding_injective).symm_apply_apply _

theorem element_coordinates (x : radical) : element (coordinates x).toAdd = x :=
  MonoidHom.apply_ofInjective_symm embedding_injective x

def action : Representation Bit (normalizer (radical : Set SL)) Four where
  toFun g := (BinaryConjugationSection.normalizerAction coordinates.toMonoidHom
    coordinates.bijective g).toLinearMap
  map_one' := by apply LinearMap.ext; intro v; change BinaryConjugationSection.normalizerAction _ _ 1 v = v; rw [map_one]; rfl
  map_mul' g h := by apply LinearMap.ext; intro v; change BinaryConjugationSection.normalizerAction _ _ (g*h) v = _; rw [map_mul]; rfl

theorem action_coordinates (g : normalizer (radical : Set SL)) (x : radical) :
    action g (coordinates x).toAdd =
      (coordinates (radical.normalizerMonoidHom g x)).toAdd :=
  BinaryConjugationSection.normalizerAction_coordinates _ _ g x

theorem cubic_matrix (v : Four) :
    planeCubic * matrix v = matrix (Matrix.mulVec pairedCubic v) * planeCubic := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeCubic, pairedCubic, matrix, Matrix.mul_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]

theorem cubic_conjugation (g : SL) (hg : g.val = planeCubic) (v : Four) :
    g * element v * g⁻¹ = element (Matrix.mulVec pairedCubic v) := by
  have he : g * element v = element (Matrix.mulVec pairedCubic v) * g := by
    apply Subtype.ext
    change g.val * matrix v = matrix (Matrix.mulVec pairedCubic v) * g.val
    rw [hg]
    exact cubic_matrix v
  rw [he,mul_inv_cancel_right]

theorem action_cubic (g : normalizer (radical : Set SL))
    (hg : g.val.val = planeCubic) (v : Four) :
    action g v = Matrix.mulVec pairedCubic v := by
  let x : radical := ⟨element v,⟨Multiplicative.ofAdd v,rfl⟩⟩
  have hx : (coordinates x).toAdd = v := congrArg Multiplicative.toAdd (coordinates_element v)
  rw [←hx,action_coordinates]
  have he : radical.normalizerMonoidHom g x =
      ⟨element (Matrix.mulVec pairedCubic v),⟨Multiplicative.ofAdd _,rfl⟩⟩ :=
    Subtype.ext (cubic_conjugation g.val hg v)
  rw [he,coordinates_element,hx]
  rfl

end Representation.BinaryParabolicExteriorSquare.PlaneRadical

namespace Representation.BinaryParabolicExteriorSquare.PlaneRadical
open PlaneSpan
variable {G : Type*} [Group G]

/-- The action on a literal radical preimage is constructed from its matrix image. -/
theorem exists_section
    (H D R Q : Subgroup G) (hDH : D ≤ H) (hRD : R ≤ D)
    (hDR : D ≤ normalizer (R : Set G)) (hQR : Q ⊓ D ≤ R)
    (π : H →* SL) (hker : π.ker = Q.subgroupOf H)
    (himage : (R.subgroupOf H).map π = radical) :
    ∃ (τ : Representation Bit D Four) (d : BinaryConjugationSection D R (Q ⊓ D) τ),
      (∀ r : R, element (d.coordinates r).toAdd = π (inclusion (hRD.trans hDH) r)) ∧
      (∀ a : D, (π (inclusion hDH a)).val = planeCubic →
        ∀ v, τ a v = Matrix.mulVec pairedCubic v) := by
  let πD := π.comp (inclusion hDH)
  have hn (a : D) : πD a ∈ normalizer (radical : Set SL) := by
    rw [←himage]
    apply le_normalizer_map π
    refine mem_map_of_mem π ?_
    exact (mem_normalizer_iff.mpr (fun x =>
      mem_normalizer_iff.mp (hDR a.property) (x : G)))
  let α : D →* normalizer (radical : Set SL) := πD.codRestrict _ hn
  let f : R →* radical := (π.comp (inclusion (hRD.trans hDH))).codRestrict _
    (fun r => by
      rw [←himage]
      exact mem_map_of_mem π (show inclusion (hRD.trans hDH) r ∈ R.subgroupOf H from r.property))
  have hf : Function.Surjective f := by
    intro x
    have hx : x.val ∈ (R.subgroupOf H).map π := by rw [himage]; exact x.property
    obtain ⟨r,hr,he⟩ := hx
    exact ⟨⟨r,hr⟩,Subtype.ext he⟩
  let c : R →* Multiplicative Four := coordinates.toMonoidHom.comp f
  let τ := action.comp α
  let d : BinaryConjugationSection D R (Q ⊓ D) τ := {
    section_le := hRD
    kernel_le := hQR
    normalized := hDR
    coordinates := c
    onto := coordinates.surjective.comp hf
    kernel_eq := by
      ext r
      change coordinates (f r) = 1 ↔ (r : G) ∈ Q ⊓ D
      rw [coordinates.map_eq_one_iff]
      have hh : f r = 1 ↔ inclusion (hRD.trans hDH) r ∈ π.ker :=
        Subtype.ext_iff
      rw [hh,hker]
      exact ⟨fun h => ⟨h,hRD r.property⟩,fun h => h.1⟩
    equivariant := by
      intro a r
      change (coordinates (f _)).toAdd = action (α a) (coordinates (f r)).toAdd
      rw [action_coordinates]
      apply congrArg (fun x => (coordinates x).toAdd)
      apply Subtype.ext
      change π (inclusion hDH a * inclusion (hRD.trans hDH) r * (inclusion hDH a)⁻¹) =
        π (inclusion hDH a) * π (inclusion (hRD.trans hDH) r) * (π (inclusion hDH a))⁻¹
      rw [map_mul,map_mul,map_inv] }
  refine ⟨τ,d,?_,?_⟩
  · intro r
    exact element_coordinates (f r)
  · intro a ha v
    exact action_cubic (α a) ha v

end Representation.BinaryParabolicExteriorSquare.PlaneRadical
