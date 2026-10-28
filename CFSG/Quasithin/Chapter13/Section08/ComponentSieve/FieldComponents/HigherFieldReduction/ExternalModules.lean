module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Alternatives
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.SeedAction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.NaturalLayers
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.NaturalBranches
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Borel
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Natural
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Assembly
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.SupplementGeneration
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.SourceCalculation

/-!
# External-X module deductions for the higher-field reduction

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.8.20, printed pp.954–955 (PDF pp.971–972).

The natural branches below use the literal action on U_H/V₁ and the actual
lift of the marked Borel inside K. Residual transport, odd-degree torus orders,
and the local centralizing-residual identities derive seed centralization.
The index-three route also derives normalization from the local action on L.
One or two genuine natural tensor sections, including independently chosen
natural/dual orientations for L₃, then contradict the source action kernel.

`Assembly.external_moved_reduction` connects the seven-entry component sieve,
the constructed cubic action and FF alternatives to these natural endpoints.
It leaves only the exceptional moved tensor module and proves absence of
transvections on the original U_H/V₁. `external_impossible_of_critical_inputs`
connects that result to the existing moved tensor contradiction.

`SourceCalculation` supplies a separate family under minimal earlier local
data, without the obsolete covered centralizer formula or local index.
Actual Borel centralization feeds both natural branches; the genuine critical
selection and parabolic calculation discharge rank, conjugation, quadraticity
and component placement for the exceptional branch. The coordinates remain on
W = [U,K*]. The source supplement theorem also discharges generation in the
covered case using its elementary-nine quotient and the SQTK three-rank bound.
`SourceCalculation.external_impossible` completes this external family. The
field assembly supplies actual Borel centralization as an intermediate result
and the genuine earlier geometric/classification inputs. The old conditional
family remains unchanged.
-/
