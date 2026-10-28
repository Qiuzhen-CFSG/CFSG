module

public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.Solvable
public import Theory.GroupTheory.ChiefFactorDirectPower.Solvable
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Generation for cyclic composition-factor extensions

A genuine simple section of a solvable group is cyclic of prime order,
and its full automorphism group is cyclic. For any actual subgroup D of
that automorphism group, its natural semidirect extension has a solvable
kernel and quotient. The proved solvable generation theorem supplies a
rank-one witness for that extension.

This verifies the cyclic-factor calculation in Aschbacher--Smith,
*The Classification of Quasithin Groups*, E.1.13, printed p.214. It does
not invoke the still-unfinished nonabelian reduction E.1.11.
-/

public section
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE
variable {G S : Type*} [Group G] [Group S] [Finite S] [Group.IsSolvable G]

local instance (D : Subgroup (MulAut S)) : Finite (S ⋊[D.subtype] D) :=
  Finite.of_equiv (S × D) SemidirectProduct.equivProd.symm

/-- The cyclic-factor extension with its actual automorphism subgroup has a
rank-one generation witness. -/
theorem simpleSection_cyclic_extension_isEGenerated_one
    (s : ChiefFactor.SimpleSection G S) (D : Subgroup (MulAut S)) :
    IsEGenerated 1 (S ⋊[D.subtype] D) := by
  let _ := s.isSolvable
  let _ := s.automorphism_isCyclic
  let _ : Group.IsSolvable (S ⋊[D.subtype] D) :=
    Group.isSolvable_of_ker_le_range SemidirectProduct.inl SemidirectProduct.rightHom
      SemidirectProduct.range_inl_eq_ker_rightHom.symm.le
  exact isEGenerated_one_of_solvable
end CFSG.Quasithin.ChapterE
