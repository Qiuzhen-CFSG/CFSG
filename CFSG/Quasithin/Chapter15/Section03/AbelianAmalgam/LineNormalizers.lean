module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Selection
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Basic
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Control
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Definitions
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Orthogonal
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Descent

/-!
# Singular-line normalizers in the abelian branch of Section 15.3

The line choice now includes the conjugacy adjustment inside `M`: the
prescribed subgroup `T_E=N_T(E)` is the ambient image of an actual Sylow
subgroup of `M_E=N_M(E)`. The elementary residual arguments prove the
relative normality of `X_E`, the normalization needed for the product
`Y_E T_E`, and the product and abelian-span consequences of the full
action on `E`.

Normalizer control promotes this local Sylow subgroup to the original
`G_E`. An abelian `V_E` is elementary abelian and lies in `Q_E`. The
definitions of `I=J(C_G(E))` and `I₀=N_I(C_T(V_E/E))` use the elementary
Thompson subgroup and the actual quotient centralizer; `I` is proved
normal in the original `G_E`.

The orthogonal calculation proves all seven clauses of 15.3.66. The local
structure constructs the Thompson controls and marked paired module; the
offender calculation identifies the original I₀, and descent removes the
temporary normalizer assumption and proves the terminal products and quotients.

`LineNormalizers.SourceAssembly` combines these results for the full
KnownSimple class and constructs the selected line from explicit `r(G,V)=2`.
It proves every clause of 15.3.66–67 conditional only on the genuine earlier
local inputs and adequate B.5 classification. Its action comparison requires
the higher OriginalSource boundary, so Section03 reexports that assembly.
The parent retains the earlier-source, rank-two and classifier discharge.

All constructions use the original `lineNormalizer E`. The separate
`temporaryLineNormalizer T V E` is reserved for the intermediate argument
on printed pp.1153–1154.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
printed pp.1152–1154, PDF pp.1169–1171.
-/
