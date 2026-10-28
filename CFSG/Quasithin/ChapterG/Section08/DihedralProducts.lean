module

public import CFSG.Quasithin.ChapterG.Section08.DihedralProducts.PrescribedPrime
public import CFSG.Quasithin.ChapterG.Section08.G09Extraction

/-!
# Dihedral products in G.8

The Thompson induction constructs injective homomorphisms from concrete
products of odd-prime dihedral groups. It proves G.8.6, the relative splitting
of G.8.7, and the prescribed first prime of G.8.8, conditional only on the
explicit universal G.8.2 input `FaithfulComplementTheorem`. The Section 08
assembly must supply that proved input.

The existing Section 09 interface transport is re-exported for compatibility.
`DihedralProducts.G09Extraction` separately proves all four extraction clauses,
including the residual-to-prime deductions. The product constructions themselves
can be imported through `DihedralProducts.PrescribedPrime` without importing G.9.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
G.8.6–8, printed p.350 (combined manuscript of 1 March 2004).
-/
