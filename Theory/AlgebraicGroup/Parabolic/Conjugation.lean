module

public import Theory.AlgebraicGroup.Borel.Conjugation
public import Theory.AlgebraicGroup.Parabolic.Defs

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- Inner conjugation preserves parabolic subgroups. -/
public lemma IsParabolicSubgroup.conjugate
    {G : Variety k} [AlgebraicGroup G]
    {P : ClosedSubgroup G} (hP : IsParabolicSubgroup P)
    (g : Variety.Point G) :
    IsParabolicSubgroup (P.conjugate g) := by
  obtain ⟨B, hB, hBP⟩ := hP
  refine ⟨B.conjugate g, hB.conjugate g, ?_⟩
  intro x hx
  apply (P.mem_conjugate_iff g x).mpr
  apply hBP
  exact (B.mem_conjugate_iff g x).mp hx

end Theory.AlgebraicGroup
