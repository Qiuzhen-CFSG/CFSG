module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Markings
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Subgroups
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Terminal
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Escaping
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.SourceReduction.Selection
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Escaping.Source.Assembly
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Escaping.Source.Residual
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Escaping.Source.Completion
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.SourceReduction.PointIncidence
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.SourceReduction.Completion

/-!
# Source development of the natural-module reduction 12.5.1

The original natural action supplies the full AmbientNaturalMarking used
in Section 12.9. Every ten-dimensional irreducible action supplies genuine
exterior coordinates, including the dual case by inverse transpose. The
standard ambient subgroups and the final commutator contradiction are
provided here. The nonsingular point can now be chosen with its T-centralizer
of index four and Sylow in its M-centralizer, using the earlier structural
theorem of Section 12.2.

The seven-case selection now leaves the full natural marking or an actual
exterior marking aligned with T. The original local-component, fusion and
weak-closure arguments construct PointControl from the same-G,T earlier
structural input. From point escape, the terminal source chain selects H
inside the literal quotient-centralizer supplement, identifies its A₅
residual, constructs an escaping conjugate, and proves its corank and full
action-kernel bounds. This directly constructs TerminalConfiguration and
gives the final contradiction.

The original H-star selection and its actual A₅ residual now give weak
closure inside O₂(H). The F.7 geometry constructs a noncommuting conjugate;
the six-space argument and unique point incidence prove the opposite
point-centralizer escape. This excludes the exterior branch and constructs
the full original natural marking. Completion exports NaturalModule at
the same G,T and NaturalReduction from genuine universal earlier inputs.
Only the earlier structural/module theorems remain explicit; their final
discharge belongs to qt-d-1332-source.

Source: Aschbacher--Smith, 12.5.1--12, printed pp.816--822.
-/
