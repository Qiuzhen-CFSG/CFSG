module

public import CFSG.Quasithin.Chapter16.Section04To05.NonRankTwo.Binary.Setup
public import CFSG.Quasithin.Chapter16.Section04To05.NonRankTwo.Binary.Centralizer
public import CFSG.Quasithin.Chapter16.Section04To05.NonRankTwo.Binary.Products
public import CFSG.Quasithin.Chapter16.Section04To05.NonRankTwo.Binary.Action

/-!
# Binary component elimination: configuration and orbit interfaces

The target is exclusion of the actual full components PSL₄(2) and PSL₅(2)
in the genuine Δ₀ setup, the binary part of Aschbacher–Smith, combined
manuscript of 1 March 2004, Lemma 16.5.12, printed pp.1200–1201.

The checked deductions here give the cyclic commuting-Sylow centralizer
consequence, the mixed-product fusion contradiction, and the faithful
seven-point contradiction after excluding thirteen using the actual
automorphism group of an elementary group of order 32. The normalizer
actor is the genuine conjugation image, with its kernel and ambient orbits.

The binary configuration construction and both final orbit branches are
still required. `ElementaryConfiguration` is their intermediate output
contract, not a hypothesis acceptable in the final binary exclusion.
No numbered source theorem or unconditional exclusion is asserted here.
The contained-A branch must use the established j₂ class in the orbit
paragraph: its printed j₁ label conflicts with the immediately preceding
exclusion of that class. The other branch uses O²(I), not O₂(I) or O^{2′}(I).
-/
