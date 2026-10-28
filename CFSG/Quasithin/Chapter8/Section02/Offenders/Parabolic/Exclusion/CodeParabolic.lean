module

public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion.CodeParabolic.Source

/-!
# The exceptional Aut(M22) code branch of Proposition 8.2.2(1)

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, printed pp.714–715 (PDF pp.731–732).

The current exports prove the six-three-cycle assertion on 22 points and
cubic displacement six on both native ten-dimensional modules, including
the outer action. The actual Aut(M22) comparison supplies the equivariant
marking required by `Exclusion.Actors`. The source application uses the
literal conjugation image and its relative-centralizer kernel, and retains
M_V rather than replacing it with M.

Final source assembly remains open. It must verify 3.1.5(II) and 3.1.9(a–d)
with M₀ = LT, count three noncentral cubic chief factors, establish the local
residual L_z and the {2,3}' centralization hypothesis, and reconstruct the
parabolic from the chief-action quotients of 3.1.9(6). That lemma identifies
H/C_H(U_i); it does not directly identify H/O₂(H). The final outputs must
include actual XiMember, its prime-three quotient, and the literal dihedral
H/O₂,₃(H), retaining H ≤ C_G(Z). None is claimed by these partial results.
-/
