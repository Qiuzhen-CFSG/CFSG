module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Normalizers
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.Basic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Setup
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.LocalCore
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.SectionCentralizer

/-!
# Fixed-element centralizers in the source 14.7.68 argument

The checked reductions construct the actual local Sylow and normal component
from a characteristic-subgroup witness, verify Hypothesis C.2.3 on the actual
two-core, and prove the order-three section-centralizer obstruction using the
marked S₅ quotient. All normality is relative to the specified local group.

The ambient bound C_G(u) ≤ H is not yet proved. Final assembly must construct
the characteristic witness from dual chief factors and C.1.26, exclude the odd
SL₂(5) involvement using the actual critical subgroup, and finish the
quasisimple Ru-cover and remaining C.2.7 alternatives. The direct assumptions
N_G(K)=H and maximal two-locality belong to the separate 14.7.67(4) owner.
No component-exclusion certificate or legacy CriticalFusion input is used.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
14.7.68(2), printed pp.1071–1072 (PDF pp.1088–1089).
-/
