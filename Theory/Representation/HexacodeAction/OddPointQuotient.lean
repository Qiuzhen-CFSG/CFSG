module

public import Theory.Representation.HexacodeAction.ThompsonOffenders
public import Theory.Representation.BinaryOffender.CommutatorRank
import Theory.Representation.BinaryOffender.ComponentPermutationObstruction

/-!
# The quotient above an odd involution's scalar point

An odd involution has a three-dimensional displacement space. That space
is fixed pointwise, so it cannot contain the scalar point of a nonzero
fixed vector. Any subspace containing both therefore has dimension at
least four, and its quotient in the original hexacode has dimension at
most two.

Source: Aschbacher--Smith12.7.17, printed p.845.
-/

public noncomputable section
open Atlas.Codes Subgroup Representation.BinaryOffender
namespace Representation.Hexacode

/-- The original scalar point and all displacements of an odd involution
leave at most two binary dimensions in the quotient. -/
theorem odd_involution_point_quotient_finrank_le_two
    (g : HexAutomorphisms) (hg : hexSign g = -1) (h2 : g ^ 2 = 1)
    (v : hexacode) (hv : v ≠ 0) (hgv : action g v = v)
    (E : Submodule Bit hexacode)
    (hpoint : (Submodule.span F {v}).restrictScalars Bit ≤ E)
    (hmove : ∀ w : hexacode, action g w - w ∈ E) :
    Module.finrank Bit (hexacode ⧸ E) ≤ 2 := by
  let D := LinearMap.range (action g - LinearMap.id)
  have hd : Module.finrank Bit D = 3 :=
    (fixedCodim_zpowers_eq_displacement_rank action g).symm.trans
      (ThompsonOffenders.odd_involution_fixedCodim g hg h2)
  have hDE : D ≤ E := by
    rintro _ ⟨w, rfl⟩
    exact hmove w
  have hfix (w : hexacode) (hw : w ∈ D) : action g w = w := by
    obtain ⟨x, rfl⟩ := hw
    exact involution_fixes_displacement action (by simpa only [pow_two] using h2) x
  have hω : omega • v ∈ E :=
    hpoint ((Submodule.span F {v}).smul_mem omega (Submodule.mem_span_singleton_self v))
  have hlarge : 4 ≤ Module.finrank Bit E := by
    by_contra hn
    have he : D = E := Submodule.eq_of_le_of_finrank_eq hDE (by
      have hh := Submodule.finrank_mono hDE
      change Module.finrank Bit D ≤ Module.finrank Bit E at hh
      change Module.finrank Bit D = Module.finrank Bit E
      omega)
    exact hv (ThompsonOffenders.eq_zero_of_odd_fixes_scalar g hg v hgv
      (hfix _ (he.symm ▸ hω)))
  have hh := E.finrank_quotient_add_finrank
  rw [hexacode_finrank] at hh
  omega

end Representation.Hexacode
