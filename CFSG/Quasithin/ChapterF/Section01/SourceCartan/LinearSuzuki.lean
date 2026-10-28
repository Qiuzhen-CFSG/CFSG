module

public import CFSG.Quasithin.ChapterF.Section01.SourceCartan.LinearSuzuki.Linear
public import CFSG.Quasithin.ChapterF.Section01.SourceCartan.LinearSuzuki.Suzuki

/-!
# The linear and Suzuki Cartan rigidity branches of F.1.3(5)

Both concrete families satisfy the exact `CartanQuadraticRigidity` contract.
The proofs use the actual Borel quotient, semilinear automorphism coverage
and rigidity of a quadratic field action on all units. They retain the
specified automorphism and arbitrary complement, and include PSL₂(2) and
Sz(2). The source's quotient lifting and compatible-Cartan assembly remain
in `SourceCartan.Transport` and the parent `SourceCartan` module.

Source: Aschbacher–Smith, F.1.3(5), printed p.260, final paragraph.
-/
