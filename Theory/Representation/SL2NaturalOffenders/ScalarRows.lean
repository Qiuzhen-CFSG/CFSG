module
public import Theory.Representation.SL2NaturalOffenders.Semilinear
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Algebra.Group.Hom.Instances

/-!
# Scalar parameters for equivariant rows

A multiplicative family of additive endomorphisms of the natural SL₂ module
has an additive scalar parameter if each row commutes with SL₂. The parameter
is obtained by evaluating the first basis vector and taking its first
coordinate. The indexing group need not be commutative.

This applies to the descended commutator rows of the original marked pair
in the point-parabolic argument of Meierfrankenfeld--Stellmacher (1993), (3.7).
-/

public section
namespace Representation.SL2NaturalOffenders
variable {F C : Type*} [Field F] [Group C]

/-- Equivariant rows of an arbitrary group-indexed multiplicative family are
scalars, and their scalar parameters form a homomorphism to the additive field. -/
theorem exists_scalar_rows
    (d : C →* (Multiplicative (Fin 2 → F) →* Multiplicative (Fin 2 → F)))
    (hd : ∀ x (L : Matrix.SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F),
      (d x (Multiplicative.ofAdd (L.val.mulVec v))).toAdd =
        L.val.mulVec ((d x (Multiplicative.ofAdd v)).toAdd)) :
    ∃ φ : C →* Multiplicative F, ∀ x (v : Fin 2 → F),
      d x (Multiplicative.ofAdd v) = Multiplicative.ofAdd ((φ x).toAdd • v) := by
  let φ : C →* Multiplicative F := {
    toFun x := Multiplicative.ofAdd ((d x (Multiplicative.ofAdd ![1,0])).toAdd 0)
    map_one' := by simp
    map_mul' x y := by
      rw [map_mul]
      rfl }
  refine ⟨φ,?_⟩
  intro x v
  let row : (Fin 2 → F) →+ (Fin 2 → F) := AddMonoidHom.toMultiplicative.symm (d x)
  obtain ⟨a,ha⟩ := centralizer_scalar row (hd x)
  have hφ : (φ x).toAdd = a := by
    have h := congrFun (ha ![1,0]) 0
    change (d x (Multiplicative.ofAdd ![1,0])).toAdd 0 = a
    change (d x (Multiplicative.ofAdd ![1,0])).toAdd 0 = (a • ![1,0]) 0 at h
    simpa only [Pi.smul_apply,smul_eq_mul,Matrix.cons_val_zero,mul_one] using h
  apply Multiplicative.toAdd.injective
  change row v = (φ x).toAdd • v
  rw [hφ,ha]

end Representation.SL2NaturalOffenders
