module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.SymplecticFour.ExtendedCartan
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.SymplecticFour.Geometry

/-!
# Localizing the marked symplectic Weyl relation

The literal point and plane reflections in a genuine extension transport
through the completion maps. Their product acts on the full Cartan by a
quarter-turn, and its square inverts the Cartan. Its fourth power therefore
centralizes the Cartan. If that power belongs to the marked middle subgroup,
the extended-Borel centralizer theorem puts it in the torus, where the
half-turn identity kills it in characteristic two.

Thus closing the original marked edge is exactly the remaining Weyl relation.
This algebraic statement retains every field-automorphism factor and works
at q = 4. It does not assume or prove apartment closure or identification.
Source: Aschbacher–Smith F.4.10, F.4.16, printed pp.279,282 of
`refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.SourceCompletion.SymplecticFour
variable {F : Type*} [Field F] [CharP F 2]
namespace SourceExtension
variable (E : SourceExtension F)

def pointWeyl : E.left := ⟨MulAut.conj WeylFrame.pointReflection,
  (E.left_inner.ge ⟨_,WeylFrame.pointReflection_mem,rfl⟩).1⟩

def planeWeyl : E.right := ⟨MulAut.conj WeylFrame.planeReflection,
  (E.right_inner.ge ⟨_,WeylFrame.planeReflection_mem,rfl⟩).1⟩

theorem pointWeyl_sq : E.pointWeyl^2=1 := by
  apply Subtype.ext
  change (MulAut.conj (WeylFrame.pointReflection (F := F)))^2=1
  rw [←map_pow,WeylFrame.pointReflection_sq,map_one]

theorem planeWeyl_sq : E.planeWeyl^2=1 := by
  apply Subtype.ext
  change (MulAut.conj (WeylFrame.planeReflection (F := F)))^2=1
  rw [←map_pow,WeylFrame.planeReflection_sq,map_one]
end SourceExtension

namespace Completion
variable {E : SourceExtension F} {M : Type*} [Group M] (c : Completion E M)

def weylProduct : M := c.left E.pointWeyl * c.right E.planeWeyl

private theorem torusMap_left (p : Fˣ × Fˣ) : c.torusMap p =
    c.left ⟨MulAut.conj (diagonalTorus p.1 p.2),
      (E.left_inner.ge ⟨_,(diagonalTorus_mem_borel p.1 p.2).1,rfl⟩).1⟩ := rfl

private theorem torusMap_right (p : Fˣ × Fˣ) : c.torusMap p =
    c.right ⟨MulAut.conj (diagonalTorus p.1 p.2),
      (E.right_inner.ge ⟨_,(diagonalTorus_mem_borel p.1 p.2).2,rfl⟩).1⟩ :=
  DFunLike.congr_fun c.compatible (E.borelToMiddle (torusToBorel p))

theorem pointWeyl_torus (a b : Fˣ) :
    c.left E.pointWeyl * c.torusMap (a,b) * c.left E.pointWeyl = c.torusMap (a,b⁻¹) := by
  rw [c.torusMap_left,c.torusMap_left,←map_mul,←map_mul]
  apply congrArg c.left
  apply Subtype.ext
  change MulAut.conj WeylFrame.pointReflection * MulAut.conj (diagonalTorus a b) *
    MulAut.conj WeylFrame.pointReflection = MulAut.conj (diagonalTorus a b⁻¹)
  rw [←map_mul,←map_mul,WeylFrame.pointReflection_torus]

theorem planeWeyl_torus (a b : Fˣ) :
    c.right E.planeWeyl * c.torusMap (a,b) * c.right E.planeWeyl = c.torusMap (b,a) := by
  rw [c.torusMap_right,c.torusMap_right,←map_mul,←map_mul]
  apply congrArg c.right
  apply Subtype.ext
  change MulAut.conj WeylFrame.planeReflection * MulAut.conj (diagonalTorus a b) *
    MulAut.conj WeylFrame.planeReflection = MulAut.conj (diagonalTorus b a)
  rw [←map_mul,←map_mul,WeylFrame.planeReflection_torus]

private theorem pointWeyl_inv : (c.left E.pointWeyl)⁻¹=c.left E.pointWeyl := by
  apply inv_eq_of_mul_eq_one_left
  rw [←pow_two,←map_pow,E.pointWeyl_sq,map_one]

private theorem planeWeyl_inv : (c.right E.planeWeyl)⁻¹=c.right E.planeWeyl := by
  apply inv_eq_of_mul_eq_one_left
  rw [←pow_two,←map_pow,E.planeWeyl_sq,map_one]

private theorem rotation_torus (a b : Fˣ) :
    c.weylProduct*c.torusMap (a,b)*c.weylProduct⁻¹=c.torusMap (b,a⁻¹) := by
  calc
    _ = c.left E.pointWeyl *
        (c.right E.planeWeyl*c.torusMap (a,b)*c.right E.planeWeyl) * c.left E.pointWeyl := by
      simp only [weylProduct,mul_inv_rev,c.pointWeyl_inv,c.planeWeyl_inv,mul_assoc]
    _ = _ := by rw [c.planeWeyl_torus,c.pointWeyl_torus]

/-- The half-turn inverts both independent diagonal parameters. -/
theorem weylProduct_sq_inverts (p : Fˣ × Fˣ) :
    c.weylProduct^2*c.torusMap p*(c.weylProduct^2)⁻¹=(c.torusMap p)⁻¹ := by
  rcases p with ⟨a,b⟩
  calc
    _ = c.weylProduct*(c.weylProduct*c.torusMap (a,b)*c.weylProduct⁻¹)*c.weylProduct⁻¹ := by simp only [pow_two,mul_inv_rev,mul_assoc]
    _ = c.torusMap (a⁻¹,b⁻¹) := by rw [c.rotation_torus,c.rotation_torus]
    _ = _ := (map_inv c.torusMap (a,b))

/-- The possible fourth-power obstruction centralizes the whole marked Cartan. -/
theorem weylProduct_four_centralizes :
    c.weylProduct^4 ∈ centralizer (c.torusMap.range : Set M) := by
  rintro t ⟨p,rfl⟩
  apply Eq.symm
  apply mul_inv_eq_iff_eq_mul.mp
  calc
    _ = c.weylProduct^2*(c.weylProduct^2*c.torusMap p*(c.weylProduct^2)⁻¹)*(c.weylProduct^2)⁻¹ := by group
    _ = c.weylProduct^2*c.torusMap p⁻¹*(c.weylProduct^2)⁻¹ := by rw [c.weylProduct_sq_inverts,←map_inv]
    _ = _ := by rw [c.weylProduct_sq_inverts,map_inv,inv_inv]

/-- A fourth-power obstruction lying in the torus is trivial, also over F₄. -/
theorem weylProduct_four_eq_one_of_torus
    (hm : c.weylProduct^4 ∈ c.torusMap.range) : c.weylProduct^4=1 := by
  obtain ⟨p,hp⟩ := hm
  have hi := c.weylProduct_sq_inverts p
  rw [hp] at hi
  have he : c.weylProduct^4=(c.weylProduct^4)⁻¹ := by
    calc
      _ = c.weylProduct^2*c.weylProduct^4*(c.weylProduct^2)⁻¹ := by group
      _ = _ := hi
  have hs : (c.torusMap p)^2=1 := by
    rw [hp,pow_two]
    nth_rw 1 [he]
    exact inv_mul_cancel _
  have hp2 : p^2=1 := c.torusMap_injective (by rw [map_pow,hs,map_one])
  have hp1 : p=1 := by
    apply Prod.ext <;> apply Units.ext <;> apply CharTwo.sq_injective
    · simpa using congrArg (fun x : Fˣ × Fˣ => (x.1 : F)) hp2
    · simpa using congrArg (fun x : Fˣ × Fˣ => (x.2 : F)) hp2
  rw [←hp,hp1,map_one]

variable [Finite F]
/-- The exact algebraic localization needed by the apartment argument.
The extended Borel is allowed to contain field automorphisms of even order. -/
theorem weylProduct_four_eq_one_iff_middle {n : ℕ}
    (hF : Nat.card F=2^n) (hn : 1<n) :
    c.weylProduct^4=1 ↔ c.weylProduct^4 ∈ c.middle.range := by
  constructor
  · intro h
    rw [h]
    exact one_mem _
  · intro h
    apply c.weylProduct_four_eq_one_of_torus
    exact (c.middle_inf_centralizer_torus hF hn).le ⟨h,c.weylProduct_four_centralizes⟩

/-- Closing the literal marked edge is sufficient for the canonical Weyl relation. -/
theorem weylProduct_four_eq_one_iff_fixes_edge {n : ℕ}
    (hF : Nat.card F=2^n) (hn : 1<n)
    (ho : c.left.range ⊓ c.right.range=c.middle.range) :
    c.weylProduct^4=1 ↔
      (c.weylProduct^4 • base c.cosetFamily false=base c.cosetFamily false ∧
       c.weylProduct^4 • base c.cosetFamily true=base c.cosetFamily true) := by
  rw [c.weylProduct_four_eq_one_iff_middle hF hn,←ho]
  change (_∈c.left.range ∧ _∈c.right.range) ↔ _
  have hf (i : Bool) : c.weylProduct^4 • base c.cosetFamily i=base c.cosetFamily i ↔
      c.weylProduct^4 ∈ c.cosetFamily i := by
    change c.weylProduct^4 ∈ MulAction.stabilizer M (base c.cosetFamily i) ↔ _
    rw [base,Subgroup.CosetGeometry.stabilizer_base]
  rw [hf false,hf true]
  rfl
end Completion
end CFSG.Quasithin.ChapterF.SourceCompletion.SymplecticFour
