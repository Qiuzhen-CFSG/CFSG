module
public import Theory.Representation.CubicClifford.IndexTwoRestriction
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Imprimitive.Split

/-!
# Displacement on exchanged Clifford constituents

When a normal index-two restriction splits into two conjugate constituents,
an actor commuting with the chosen outer conjugator has equal displacement
on both constituents. The actual product equivalence makes their dimensions
add. In particular, rank two on the original module gives rank one on each
constituent. No action recognition or new constituent is assumed.

Source: Clifford theory, Isaacs, Theorem 6.5; the displacement step in
Aschbacher–Smith 15.2.27(2), printed p.1119.
-/

public section
open Subgroup Representation
namespace Representation.CubicClifford.Inertia
variable {F H V : Type*} [Field F] [Group H]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem constituent_displacement_double (ρ : Representation F H V)
    (K : Subgroup H) [K.Normal]
    (C : Subrepresentation (ρ.comp K.subtype)) (g : H) (a : K)
    (hc : Commute g (a : H))
    (e : Representation.Equiv (ρ.comp K.subtype)
      (C.toRepresentation.prod (conjugateRep C.toRepresentation g))) :
    Module.finrank F (LinearMap.range (ρ (a : H) - 1)) =
      2 * Module.finrank F (LinearMap.range (C.toRepresentation a - 1)) := by
  have he : Module.finrank F (LinearMap.range (ρ (a : H) - 1)) =
      Module.finrank F (LinearMap.range
        ((C.toRepresentation.prod (conjugateRep C.toRepresentation g)) a - 1)) :=
    RankTwo.finrank_movedSpace_transport (ρ.comp K.subtype)
      (C.toRepresentation.prod (conjugateRep C.toRepresentation g))
      (MulEquiv.refl K) e.toLinearEquiv
      (fun k v => LinearMap.congr_fun (e.isIntertwining' k) v) a
  rw [he]
  have ha : (conjugateRep C.toRepresentation g) a = C.toRepresentation a := by
    rw [conjugateRep_apply]
    congr 1
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr hc.eq
  exact (RankTwo.Imprimitive.finrank_block
    (C.toRepresentation a) ((conjugateRep C.toRepresentation g) a)).trans
    (by rw [ha, two_mul])

theorem constituent_rank_one_of_rank_two (ρ : Representation F H V)
    (K : Subgroup H) [K.Normal]
    (C : Subrepresentation (ρ.comp K.subtype)) (g : H) (a : K)
    (hc : Commute g (a : H))
    (e : Representation.Equiv (ρ.comp K.subtype)
      (C.toRepresentation.prod (conjugateRep C.toRepresentation g)))
    (hr : Module.finrank F (LinearMap.range (ρ (a : H) - 1)) = 2) :
    Module.finrank F (LinearMap.range (C.toRepresentation a - 1)) = 1 := by
  have hh := constituent_displacement_double ρ K C g a hc e
  omega
end Representation.CubicClifford.Inertia
