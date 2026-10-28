module

public import Theory.Character.ModularBlock.CyclicThirteenOrdinaryData
public import Theory.Character.ModularBlock.CyclicThirteenOrdinaryConstruction

/-!
# Ordinary character rows for a cyclic Sylow thirteen-subgroup

This is the public entry point for
`ModularBlock.CyclicThirteen.nonempty_ordinaryRows`. For a self-centralizing
Sylow subgroup of order thirteen whose normalizer has centralizer index three,
the theorem constructs `OrdinaryRows` in any supplied complete ordinary
character family `PrimeCongruenceBlockData 13 G`. In particular it applies to
finite simple groups; simplicity is not needed for the ordinary construction.

The proof constructs four cubic normalizer characters and applies the integral
special-support isometry to their differences. Fourier restriction embeds the
resulting ambient exceptional characters in the supplied family and determines
their values up to a common integer shift. Ordinary column orthogonality removes
that shift and selects exactly three further constant sign rows, with the
principal row first. All other characters vanish on the punctured Sylow subgroup.
The exceptional rows have a common natural degree and signed triple-period
values at a nonidentity generator.

The construction and this entry point are independent of congruence-block
identification. The separate `CyclicThirteenRows` module supplies that bridge.

Source: the ordinary exceptional-character argument underlying Brauer's
cyclic-block theorem, as used in Alperin--Brauer--Gorenstein, III.8,
printed pp.116–117.
-/
