module
public import Theory.Representation.NormalElementaryQuotient
/-!
# A seed centralizer controls fixed-space enlargement

For the actual conjugation representation of a centralizer quotient, every
vector in a seed centralized by P is P-fixed. Therefore an element fixing
the entire P-fixed space must lift to the seed centralizer P. This retains
an arbitrary surjective quotient map and its literal conjugation action.
Source application: Aschbacher–Smith C.2.7 and 15.4.20.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.NormalElementaryQuotient
variable {G Q : Type*} [Group G] [Group Q]
    (V Z : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* Q) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (V : Set G))

theorem no_fixedSpace_enlargement_of_seed
    (hZV : Z ≤ V) (P : Subgroup G) (hCZ : centralizer (Z : Set G) = P)
    (g : Q) (hg : g ∉ P.map q)
    (hfix : ∀ v ∈ fixedSpace (representation V q hq hk) (P.map q),
      representation V q hq hk g v = v) : False := by
  obtain ⟨x,rfl⟩ := hq g
  apply hg
  apply mem_map_of_mem
  rw [← hCZ]
  intro z hz
  let v : Additive V := Additive.ofMul ⟨z,hZV hz⟩
  have hv : v ∈ fixedSpace (representation V q hq hk) (P.map q) := by
    intro a
    obtain ⟨y,hy,hay⟩ := a.property
    change representation V q hq hk (a : Q) v = v
    rw [←hay]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [representation_apply]
    change y*z*y⁻¹ = z
    have hh := mem_centralizer_iff.mp (hCZ.symm ▸ hy) z hz
    rw [←hh,mul_inv_cancel_right]
  have hh := congrArg (fun w : Additive V => (w.toMul : G)) (hfix v hv)
  rw [representation_apply] at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm
end Representation.NormalElementaryQuotient
