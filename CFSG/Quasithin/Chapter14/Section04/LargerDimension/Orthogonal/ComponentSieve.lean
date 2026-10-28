module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve.Quotients
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve.Module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve.Source
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve.Assembly

/-!
# Component and module interfaces for Lemma 14.4.9

The literal quotient and normality checks expose a necessary source repair.
The smaller local subgroup cannot simply be the diagonal K₀: its nontrivial
action on UD/D contradicts the commutator property of a local C-component,
since K₀ ∩ UD ≤ D. The corrected subgroup is the solvable residual of
K₀UD; `source_residual_mem_localFamily` constructs its genuine local-family
placement from the selected configuration and the proved lift. The quotient actor is K₀UD/UD, whereas the printed K₀D/UD lacks
its required denominator containment. No theorem here equates those groups.

The normalizer section UD/D is identified through its literal quotient map.
Core image functoriality supplies the core and actor comparisons, and 1.2.4
places any correctly constructed local member in a containing component.
A core escaping O₂(N_G(D)) proves strict inclusion even after quotienting.
The binary five-point module is distinguished from the natural SL₂(4)
module by the fixed points of an element of order three.

The terminal A.3.14 sieve remains to be assembled. The source on pp.49–50
has fourteen numbered alternatives, not thirteen:

* (1) The maximal parabolic residuals in (S)L₃(4), Sp₄(4), G₂(4), ³D₄(4).
* (2), (3), (8) The A₅ subgroups in A₇ or its triple cover, L₂(25) or the
  specified prime-field L₂(p), and J₁, with their marked embeddings.
* (4) The SL₂(5) centralizer residual in (S)L₃^ε(5).
* (5) The E₂₅ extension by SL₂(5), a maximal-parabolic residual in L₃(5).
* (6), (7) The natural L₂(4) blocks with E₁₆ kernel in M₂₂ or its triple
  cover, and M₂₃. The module comparison exported here addresses these.
* (9) The extraspecial order-32 extension in J₂, at a 2-central involution.
* (10) The J₄ case, with B/O₂(B) ≃ A₅ and F*(B) = O₂(B). The printed
  statement supplies no kernel size or action that excludes E₁₆ directly.
* (11) The cyclic-four central product with the extraspecial order-32
  kernel in HS, as a 2-central involution-centralizer residual.
* (12) The order-2048 kernel in Ru, again a centralizer residual.
* (13), (14) Both odd-core alternatives with B/O(B) ≃ SL₂(5), retaining
  their distinct containing groups and prime congruences.

The residual construction and local placement are now proved. The exact
image core and binary action still need to be identified, and the complete
embedding sieve must use the proved Lie-parabolic and J₄ obstructions.
These obligations must not be replaced by a shorter assumed classification list. The
universal A.3.12–14 producer is `qt-a03-embeddings`; final source assembly
must discharge that theorem input as well as the selection and lift inputs.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, A.3.14,
pp.49–50, Definition 1.2.3 and Lemma 1.2.4, p.505, and 14.4.9, p.1010.
-/
