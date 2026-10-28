module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.Conclusion

/-!
# Fitting centralization in Lemma 13.5.20

For the actual star quotient H/O₂(H), V* centralizes F(H*). A noncentral
prime core would have prime three; the normalizer and Thompson A×B
arguments force the two-core of Y* to act nontrivially on a supercritical
subgroup. The cyclic and extraspecial cases are excluded by two-perfectness
and the cubic rank argument. The remaining normal E₉ forces at least four
moved binary dimensions, contradicting the rank-two action on U_H/V₁.

`centralizes_fitting_of_counterexample` obtains the required normalizer
facts from 13.5.19 for Y=L₀ or Y=L₁. `exists_component_of_counterexample`
then supplies the component used after 13.5.20, with its actual star image
and two-core quotient equivalence. The old normal-nine reduction is
re-exported unchanged from Reduction.

Earlier local geometry, the universal 13.5.16–17 recognitions, and the
universal F.9.5 implications remain explicit source inputs, discharged by
the Section05 assembly owner. The full SQTK input is retained.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
13.5.20 and the following paragraph, printed p.923 (PDF p.940).
-/
