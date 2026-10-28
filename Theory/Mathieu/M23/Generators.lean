module

public import Theory.Mathieu.M24.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Perm.List
public import Mathlib.Data.Fin.Basic
public import Mathlib.Algebra.Group.Subgroup.Actions

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

namespace Sporadic.Mathieu

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


@[expose] public noncomputable def m24GeneratorAInM24 : M24 :=
  ⟨m24GeneratorA, m24GeneratorA_mem⟩

@[expose] public noncomputable def m24GeneratorBInM24 : M24 :=
  ⟨m24GeneratorB, m24GeneratorB_mem⟩

/-- The short M24 word moving the Atlas maximal-subgroup fixed point 11 to 24. -/
@[expose] public noncomputable def m23AtlasConjugator : M24 :=
  m24GeneratorBInM24 * m24GeneratorAInM24 *
    m24GeneratorBInM24 * m24GeneratorAInM24

/-- The first M23 standard generator before moving its fixed point to 24. -/
@[expose] public noncomputable def m23AtlasRawA : M24 :=
  m24GeneratorBInM24 * m24GeneratorAInM24 *
    (m24GeneratorBInM24 *
      (m24GeneratorAInM24 * m24GeneratorBInM24) ^ 4) ^ 4 *
    m24GeneratorAInM24⁻¹ * m24GeneratorBInM24⁻¹

/-- The second M23 standard generator before moving its fixed point to 24. -/
@[expose] public noncomputable def m23AtlasRawB : M24 :=
  let bab :=
    m24GeneratorBInM24 * m24GeneratorAInM24 * m24GeneratorBInM24
  m24GeneratorBInM24 * bab ^ 2 *
    (m24GeneratorBInM24 * m24GeneratorAInM24 * bab ^ 2 *
      m24GeneratorAInM24) ^ 2 *
    m24GeneratorBInM24⁻¹ *
    (m24GeneratorAInM24⁻¹ * m24GeneratorBInM24⁻¹ ^ 2) ^ 2

/-- First standard M23 generator as an element of the M24 point-24 stabilizer. -/
@[expose] public noncomputable def m23M24GeneratorA : M24 :=
  m23AtlasConjugator * m23AtlasRawA * m23AtlasConjugator⁻¹

/-- Second standard M23 generator as an element of the M24 point-24 stabilizer. -/
@[expose] public noncomputable def m23M24GeneratorB : M24 :=
  m23AtlasConjugator * m23AtlasRawB * m23AtlasConjugator⁻¹

public theorem m23M24GeneratorA_fix24 :
    ((m23M24GeneratorA : M24) : Equiv.Perm (Fin 24)) 24 = 24 := by
  rfl

public theorem m23M24GeneratorB_fix24 :
    ((m23M24GeneratorB : M24) : Equiv.Perm (Fin 24)) 24 = 24 := by
  rfl

@[expose] public noncomputable def m23M24StabilizerGeneratorA :
    MulAction.stabilizer M24 (24 : Fin 24) :=
  ⟨m23M24GeneratorA, m23M24GeneratorA_fix24⟩

@[expose] public noncomputable def m23M24StabilizerGeneratorB :
    MulAction.stabilizer M24 (24 : Fin 24) :=
  ⟨m23M24GeneratorB, m23M24GeneratorB_fix24⟩

end Sporadic.Mathieu
