module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.Natural.StandardActions

/-!
# The concrete 24-dimensional natural Parker modules

The labels `Omega × ParkerBit` identify distinct actual coordinate halfspaces
on each Parker axis. Signed functions on these labels give real modules with
`L^(ε+1)(x) = -L^ε(x)` and orthonormal basis `L^1(x)`.

The imported development constructs actions from permutations of the genuine
halfspace families, proves their exact linear kernel criterion, and computes
all the loop and standard-automorphism actions of Aschbacher's Lemma 27.4(1)–(3).
In particular it includes both directions of the odd `psiAut2` transport
between the first and third modules. On the first natural module, `z1` acts
trivially and `psi2(sπ)` acts as minus identity.

Source: Aschbacher, *Sporadic Groups*, printed pp. 146–147 (PDF page 79).
The unconditional `N1` action and identification of its kernel subgroup are
separate obligations of the triality parent; no such conclusions are assumed
in this construction.
-/
