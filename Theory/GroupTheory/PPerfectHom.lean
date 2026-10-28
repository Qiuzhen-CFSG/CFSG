module

public import Theory.GroupTheory.PResidual.Defs

/-!
# Homomorphisms from p-perfect groups

A p-perfect group has no nontrivial homomorphic image which is a p-group.  The
form below is convenient when a fixed-point argument produces a homomorphism
into an elementary abelian p-group.
-/

@[expose] public section

/-- A homomorphism from a p-perfect group to a p-group is trivial. -/
public theorem IsPPerfect.hom_eq_one_of_isPGroup
    {p : ℕ} {G P : Type*} [Fact p.Prime] [Group G] [Group P]
    (hG : IsPPerfect p G) (hP : IsPGroup p P) (f : G →* P) : f = 1 := by
  have hrange : IsPGroup p f.range := hP.to_subgroup f.range
  have hquot : IsPGroup p (G ⧸ f.ker) := by
    exact hrange.of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  have hker : f.ker = ⊤ := hG f.ker inferInstance hquot
  ext g
  have hg : g ∈ f.ker := by rw [hker]; trivial
  exact MonoidHom.mem_ker.mp hg
