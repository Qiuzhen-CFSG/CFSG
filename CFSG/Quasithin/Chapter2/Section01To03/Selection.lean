module

public import CFSG.Quasithin.Chapter2.Section01To03.Selection.Delta
public import CFSG.Quasithin.Chapter2.Section01To03.Selection.Maximal
public import CFSG.Quasithin.Chapter2.Section01To03.Selection.Persistence

/-!
# Local-pair existence and Γ selection in the unique maximal two-local case

This is the structural selection part of Aschbacher–Smith, *The Classification
of Quasithin Groups*, combined manuscript of 1 March 2004, §2.3, printed
pp.521–524. It proves 2.3.2(3), both parts of 2.3.3, the nonemptiness
assertions after 2.3.4–5, all of 2.3.7, and precisely 2.3.8(1–3).

The construction starts with an actual maximal D in δ and produces a
Sylow subgroup S of N_M(D) giving the local pair (S,N_G(D)). Both starred
families retain their separate maximality conditions. The extra largest-base
witness in 2.3.7(3) is explicit, and both star-preservation implications of
2.3.7(4) occur in the conclusions of parts (2) and (3).

The source statements use Chapter 1's actual characteristic-two collection
`He`. They reuse the checked 1.1.3–4 extensions and require no 1.1.5 component
classification. Cores remain intrinsic cores mapped to G, relative normalizers
remain intersections with ambient normalizers, and every asserted Sylow
transport constructs a Sylow subgroup whose ambient image is the chosen one.
The chapter classification theorem and 2.3.8(4–6) are separate results.
-/
