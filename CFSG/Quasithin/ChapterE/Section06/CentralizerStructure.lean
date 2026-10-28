module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Sylow
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Local
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Maximal

/-!
# Escaping centralizers in Section E.6

The checked foundation consists of E.6.5 (with its normality clause from
`Basic`), E.6.6, E.6.9(1), E.6.10(1), and the maximality and automizer
deductions used in E.6.11. The characteristic-two assertions take the
explicit earlier Chapter 1 results `EarlierLocalFacts`.

The block, component and odd-core hyperplane arguments remain separate
proof obligations. In particular this module does not yet assert E.6.11
or supply the structural premise of `hyperplane_escape_of_maximal_action`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.5–11,
printed pp.245–250 (PDF pp.256–261).
-/
