module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.OutsideFusion
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.MarkedKernel

/-!
# Fusion of the actual returning actor in a reflected cubic marking

The original involution-fusion theorem supplies the missing fusion of the
second dihedral actor. This is the literal source input to the U-line
normalizer argument; the cubic subgroup and both actors remain unchanged.
Source: Aschbacher, *Sporadic Groups*,45.5(4) and45.7, printed pp.244–245.
-/

public section
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.ReflectedMarking
variable {G : Type*} [Group G] [Finite G] {z : G} {X : Subgroup G}

theorem s_fused (m : CubicNormalizer.ReflectedMarking z X) (h : IsType z) :
    IsConj z m.s := h.involution_fused m.s m.s_order

end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.ReflectedMarking
