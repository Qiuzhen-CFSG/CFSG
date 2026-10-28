module
public import Theory.GroupTheory.CentralPGroupHomRigidity
public import Theory.SpecificGroups.SL2.NoIndexTwo
public import GorensteinWalter.SL2ProjectiveCover

/-!
# Projective determination of odd-field SL2 actions

Two endomorphisms of SL2 over a finite odd field agree if their composites
with the actual central projection to PSL2 agree. Their pointwise discrepancy
lies in the central kernel of order two. SL2 has no normal subgroup of index
two, so the central p-group discrepancy theorem forces that discrepancy to
be trivial.

This supplies the action comparison in Alperin--Brauer--Gorenstein, Chapter
II, Section 3, Proposition 3 (article page 26). It applies uniformly to the
field of order three, where a perfectness argument would not apply, and
retains the field of order nine. Identifying the surrounding group extension
and its matrix model remains a separate step.
-/

namespace Matrix.SpecialLinearGroup

public theorem hom_eq_of_projective_comp_eq
    (F : Type*) [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (f g : Matrix.SpecialLinearGroup (Fin 2) F →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hfg : (GorensteinWalter.sl2ProjectiveProjection F).comp f =
      (GorensteinWalter.sl2ProjectiveProjection F).comp g) : f = g := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q := GorensteinWalter.sl2ProjectiveProjection F
  have hno : ∀ N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F),
      N.Normal → N.index ≠ 2 := by
    intro N _
    exact index_ne_two (GorensteinWalter.two_ne_zero_of_odd_card F hodd) N
  apply MonoidHom.eq_of_central_pgroup_discrepancy hno q.ker
    (GorensteinWalter.sl2ProjectiveProjection_ker F).le
    (GorensteinWalter.sl2ProjectiveProjection_ker_isPGroup F hodd) f g
  intro x
  rw [MonoidHom.mem_ker, map_mul, map_inv]
  have h : q (f x) = q (g x) := DFunLike.congr_fun hfg x
  rw [h, mul_inv_cancel]

end Matrix.SpecialLinearGroup
