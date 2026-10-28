module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.LocalFusion.SourceCompletion
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal

/-!
# Aschbacher's Lemma 3.4 from exact Theorem ZD

Strong induction on the order of the finite ambient group supplies the
subgroup and quotient induction hypotheses used by local fusion. The proved
local-fusion theorem gives global set strong closure and unique conjugate
membership, including products of factor involutions. The terminal theorem
constructs the product-disconnected involution set and applies exact ZD.

The resulting statement retains the actual intersection-generated subgroup,
both relative-normalizer closure hypotheses, strong embedding in the normal
closure of the first factor, and the full dihedral/semidihedral exception.
Only the universal Theorem ZD remains an explicit independent input; no
fusion or recognition reduction is assumed. Chapter 2 uses this theorem for
the disjoint Sylow factors in source 2.5.21.

Source: M. Aschbacher, *On finite groups of component type*, Illinois J. Math.
19 (1975), Lemma 3.4, printed pp.94--96, DOI 10.1215/ijm/1256050927.
-/

public section

namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

universe u

/-- Full source Lemma 3.4, with both its fusion and terminal reductions
discharged. Exact Theorem ZD is the independent finite-group input. -/
theorem lemma_3_4 (zd : TheoremZD.{u})
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (A₁ A₂ : Subgroup G) (h : Hypotheses S A₁ A₂) :
    Conclusion A₁ A₂ :=
  conclusion_of_terminal zd terminal_conclusion_of_theoremZD S A₁ A₂ h

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

end
