module
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.SectionLinear

/-!
# Cubic movement above a fixed quotient

For a binary representation, an element of order dividing three admits the
averaging projection v ↦ v + av + a²v. If it fixes the quotient by W, this
projection gives V = W + C_V(a), so all its movement is already visible on W.
The statement concerns the literal quotient action, with no splitting assumed.

Source application: Aschbacher–Smith 14.6.24(2), printed p.1041; the paired
A₆ covers have different cubic movement and therefore yield two nontrivial
sections even when their central kernels intersect.
-/

public section
open Representation Representation.BinaryOffender Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Averaging over an element of order dividing three removes a trivial
quotient from its displacement calculation. -/
theorem fixedCodim_cubic_eq_subrepresentation
    (ρ : Representation (ZMod 2) G V) (W : Subrepresentation ρ)
    (a : G) (ha : a ^ 3 = 1) (hq : W.quotientRepresentation a = 1) :
    fixedCodim ρ (zpowers a) = fixedCodim W.toRepresentation (zpowers a) := by
  symm
  apply (fixedCodim_subrepresentation_eq_iff ρ W (zpowers a)).mpr
  apply top_unique
  intro v _
  have h3 : ρ a (ρ a (ρ a v)) = v := by
    have hh := LinearMap.congr_fun (congrArg ρ ha) v
    simpa only [map_pow, pow_succ, pow_zero, mul_one, one_mul, map_mul, Module.End.mul_apply,
      map_one, Module.End.one_apply] using hh
  have hd : ρ a (ρ a v) - ρ a v ∈ W := by
    have hh := LinearMap.congr_fun hq (W.toSubmodule.mkQ (ρ a v))
    exact (Submodule.Quotient.eq W.toSubmodule).mp hh
  have hchar (x : V) : x + x = 0 := by
    have hh := two_smul (ZMod 2) x
    have hz : (2 : ZMod 2) = 0 := by decide
    rw [hz,zero_smul] at hh
    exact hh.symm
  refine Submodule.mem_sup.mpr ⟨ρ a (ρ a v) - ρ a v,hd,
    v - (ρ a (ρ a v) - ρ a v),?_,by abel⟩
  apply (mem_fixedSpace_zpowers_iff ρ a _).mpr
  rw [map_sub,map_sub,h3]
  have hn (x : V) : -x = x := neg_eq_of_add_eq_zero_left (hchar x)
  simp only [sub_eq_add_neg, hn]
  abel

end Representation.BinaryOffender
