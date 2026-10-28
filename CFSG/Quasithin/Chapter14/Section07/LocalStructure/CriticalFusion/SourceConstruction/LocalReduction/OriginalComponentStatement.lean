module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.ComponentStatement
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideComponentBorel
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideComponentCentralResidual
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideLinearTwoActions
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideLinearTwoNormality
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideLinearThree

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideUnitaryThree
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.RankTwoContainment

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedLinearTwo
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedRows
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedLinearThree
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedUnitaryThree
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ModelRows
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.SymplecticFourExclusion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.GTwoExclusion

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ProjectiveExceptions

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.CenterCubic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.BorelGraph
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.NaturalDual
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.SpecialLinearExclusion

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.SpecialUnitaryExclusion

/-!
# Original-source inputs toward the component theorem 14.7.47

The outside-component branch now constructs the original Sylow normalizer,
its intrinsic two-core quotient preimage and its containment in N_G(L),
without an assumed Borel marking. The original inverter now proves B_C = B,
so B fixes the seed and L/O₂(L), and both L₁ and that inverter fix B/O₂(B).
For the binary L₂ row, both L₁ and the same inverter now induce inner
automorphisms of the literal C/O₂(C). Correcting the inverter within T∩C now
proves that L₁ centralizes C/O₂(C), that C normalizes L₁, and that L₁ is
normal in the reduced local C L₁ T. These supply the Borel and binary L₂
action steps of 14.7.40–42. For PSL₃(2ⁿ), n ≥ 4, the original inverter
now also acts inner, yielding the same centralization and normalization
when L₁ is outside the component. The original three-rank bound and an
explicit projective elementary nine force L₁ into the component when n
is even. For binary PSU₃(2ⁿ), n ≥ 2, the full Borel-fixation argument now
makes the original inverter inner, gives an original-Sylow centralizing
inverter, proves point normality in C L₁ T and forces three-rank one in
the outside-component case. The G₂(q) and Sp₄(q) rows, for even q > 2,
now force the original L₁ into each actual component: the literal quotient
action has three-rank at most two, the fixed-field cubic calculation makes
all cubic actors inner, and full-rank absorption gives containment.
The two nonbinary rank-two quotient rows are now excluded: the original
inverter and source fixed supplement bound the actual Borel torus
displacement by three, contradicting the G₂ and Sp₄ automorphism
calculations after transporting through the original Sylow and two-core.
For a binary L₂ component containing the original L₁, the actual Borel
unit action and original inverter now force field order four. The contained
PSL₃ row now has the same field-four restriction, using the actual torus
modulo its cubic scalars. Combined with even-degree containment, this also
forces field four for every original even-degree PSL₃ component.
For a contained PSU₃(2ⁿ) component, the original Borel quotient and inverter
now force n = 3. The projective three-rank bound also gives containment
for every odd-degree unitary component, so each such component has field
order eight without a containment premise.
The actual reduced-local quadratic actor now excludes PSL₃(4) and
PSU₃(8). Thus every contained nonbinary projective degree-three component
is excluded, as are all even-degree projective linear-three and odd-degree
projective unitary-three components. For every component with nontrivial quotient center, the same-G,T guarded
source now identifies that center with the original point cubic and lifts
point containment and normality. In every even-degree special-linear-three
row, the original T∩L inverter inverts the scalar center and acts outer on
the actual quotient. The actual Borel supplement now forces field four
and gives a linear-times-inverse-transpose factorization for this same
inverter, after an explicit inner change of the given marking. The original
full point-normalizer application retains the literal quotient action.
Native module recognition now constructs the full natural-plus-dual action
on the literal reduced-local U_I/V₁. The original selected critical denominator
and its single commutator line contradict the actual root-plane actor
configurations. Thus SL₃(4), and all even-degree nonbinary SL₃ component
quotients, are excluded with their scalar centers retained. A nontrivial
central cover of PSU₃(2ⁿ), n ≥ 2, is now also excluded: the actual Borel
supplement forces the original inverter to act inner on the projective
quotient, hence on its perfect cover, contradicting center inversion. With
the source congruence, both signed special-three catalogue rows are eliminated.
The triple-A₆ central-cover exclusion remains.
The remaining outer-action rows, larger-field and
central-cover exclusions and the
L₃(2) containment case are still needed for `WholeResidualAssembly.Earlier14747`.

Source: Aschbacher–Smith 14.7.40–47, printed pp.1061–1064,
refs/quasithin.pdf.
-/
