module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Selection
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Residual
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Exchange
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Extraspecial

/-!
# Selection from the original marked action

The component construction uses only the earlier marked subgroup, Sylow
centralizer, prime residual and central seed. It retains the marker and
prime, without requiring that the decomposable prime five or extraspecial
row has already been excluded. For prime three, the faithful quotient
identifies the cubic moved subgroup; the actual exchanged-plane geometry
then supplies the common source interface with planes of order four or
sixteen.

`ExchangedSelection.Nine` checks the entire construction on the original
Nine action. `ExchangedSelection.Decomposable` constructs the two literal
sixteen-element supports, their odd kernels, and their Sylow exchange from
the eight-dimensional large action. It also constructs the two actual
Thompson four-subgroups, their splitting and exchange, retaining the same
prime. Its marked centralizer inside the original factor-product preimage
now has the opposite odd kernel as faithful quotient residual. The full
marked centralizer has the required Sylow intersection and central-seed
bound; its faithful residual order is divisible by the same original prime.
Its fixed and moved subgroups are exactly the original sixteen-element
supports, with their original exchange and marked containment. For the same
prime-three marking, the actual Sylow marked centralizer is now normal of
index two, its action on the fixed support has kernel of index two, and every
exchanged-plane clause is proved. The actual eight-dimensional consumer
retains the same prime-five alternative; it does not assume its exclusion.
For prime three, the full marked-centralizer residual now equals the original
opposite cubic kernel, with exact order three in C_M(Z₁)/C_M(V). The actual
consumer retains this equality and the geometry for the same marking.
Generation by the marked centralizer and T now completes that prime-three
marker. The actual eight-dimensional consumer selects the component and
carries its same pre-exclusion witness through `exchangedSource`, retaining
the prime-five alternative. A further actual-action consumer now proves the
full marked-centralizer residual cyclic; its order is the original prime,
or fifteen in the quintic branch, with both sixteen-element supports
retained. The canonical O^{5′}(C_M(Z₁)) now has the original order-five image
through the literal module-centralizer quotient, and is irreducible on the
same moving support. The actual eight-dimensional consumer retains its
C_T(Z₁)-normalization and containment in the original two-residual.
The original prime-five pre-exclusion witness now excludes ordinary
components through the complete ordinary catalogue, and excludes the natural
binary SL3 block and the constrained rank-one alternative. The actual
eight-dimensional consumer keeps the same marking and its faithful
sixteen-element moving support. Its literal prime-to-three residual now
centralizes V, excluding the constrained cubic-centralizer rows. The A₇
partition residual has a full-cover automorphism fixer of order at most four,
contradicting that faithful support of order sixteen. The same-component
consumer reduces the constrained catalogue at prime five to its actual
SL₄(2) and SL₅(2) quotient rows. The selected parabolic now has equal
two-residual and prime-to-three residual through its original two-core
quotient. At prime five that residual centralizes V, placing the parabolic
in Mc and contradicting its generation with M_L. Thus the same-component
consumer excludes every constrained alternative as well as ordinary
components, while retaining both sixteen-element supports. The extra cubic factor still needs an
ambient exclusion, and the prime-five marker still needs construction.
The extraspecial central lift is now constructed in the exact source
O²(⟨R^{X₀}⟩), conditional on the intersection core moving the original
extraspecial center. The prepared module supplies the kernel commutator
bound, and the lift moves the same marked four-group. The combined
component consumer retains that cubic, the same selected component and
its pre-exclusion witness. The original extraspecial action now constructs
the image marking, including its Thompson-compatible cubic, without a
selection premise. The exact central-preimage residual is now proved
trivial under earlier 15.1.14, so its conditional lift cannot be made into
an independent construction before row exclusion. The separate O^{3′}(X₀) now supplies a moving residual on the marked
four-group. Applied to the same selected component, it excludes the ordinary
quotient list, including HS, Ru and triality, and all constrained alternatives
except the natural L₃(2) block. A separate comparison of its automorphisms
with the two original cubic images now excludes that block as well. The
proved ordinary catalogue also discharges ordinary exhaustiveness for this
row, including its Rudvalis remainder. The actual source consumer therefore
retains the same component and excludes ordinary components and all
constrained alternatives. Constrained catalogue exhaustion remains required
for the full extraspecial exclusion.
The prime-five and extraspecial constructions,
the preceding component catalogue,
and the exclusions in 15.1.23--24 are still needed for the full large-action
selection. In particular this module does not assert that those exclusions
follow from the already-surviving `ExchangedSource` interface.

Source: Aschbacher--Smith 15.1.16--25, printed pp.1092--1102.
-/
