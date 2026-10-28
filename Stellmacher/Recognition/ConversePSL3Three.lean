module

public import Theory.SpecificGroups.PSL3Three.Simplicity
public import Theory.SpecificGroups.PSL3Three.ProperSubgroups
public import Stellmacher.Recognition.PSL3ThreeModel

/-!
# Minimal simplicity of PSL₃(3)

The concrete projective special linear group over `ZMod 3` is minimal simple.
Elementary matrices and the projective Iwasawa criterion give simplicity and
nonsolvability. The checked maximal-subgroup classification places each proper
subgroup inside a conjugate of a line stabilizer, plane stabilizer, monomial
subgroup, or Singer normalizer; each of these is solvable. The result also
transports to the actual group models recognized by `ABG.IsPSL3 G 3`.

Source: Thompson's minimal-simple catalogue, GLS I §28; the maximal-subgroup
ingredient is the PSL₃(3) specialization of GLS III, Theorem 6.5.3, with the
concrete completeness certificate in `Theory.SpecificGroups.PSL3Three.ProperCover`.
-/

namespace Stellmacher.Recognition

/-- The concrete group PSL₃(3) is minimal simple. -/
public theorem isMinimalSimple_psl3_three :
    IsMinimalSimple (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3)) :=
  ⟨isSimpleGroup_psl3_three, not_isSolvable_psl3_three,
    Matrix.PSL3Three.isSolvable_of_lt⟩

/-- Every actual PSL₃(3) model in the ABG recognition interface is minimal simple. -/
public theorem isMinimalSimple_of_isPSL3_three
    {G : Type*} [Group G] [Finite G] (hG : ABG.IsPSL3 G 3) :
    IsMinimalSimple G :=
  (isMinimalSimple_iff_of_isPSL3_three hG).mpr isMinimalSimple_psl3_three

end Stellmacher.Recognition
