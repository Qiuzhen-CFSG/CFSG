module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.QuotientGeometry.Assembly

/-!
# Paired offender geometry in the degree-eight dihedral quotient

The two-block permutation stabilizer and its Klein-four product are explicit,
and `parabolic_pCoreIn` identifies that product with the intrinsic two-core
embedded in S8. The quotient of the canonical Sylow by this core is proved
isomorphic to D8. Every subgroup realizing one of the four source cases has
the stated position (I)–(IV) relative to its center and even four-group; none
lies in the core. These results hold for every relevant subgroup.

`SylowCoordinates` transports the calculations through a commuting diagram
of actual action and quotient maps. With the actual action-kernel identities,
`ranks_of_realizes` gives quotient ranks (1,1,2,1) and kernel-intersection ranks
(2,0,2,2). `paired_rank_bound_of_realizes` bounds the second kernel image by
inclusion. The strict bounds in `Consequences` feed the parent's rank inequality,
and `disjoint_paired_rank_bound` supplies the replacement bound of six.
The actual even preimage is T-normalized when the quotient images of S and T
are equal, by `normalizes_even_preimage_of_equal_quotient_images`.

`Conjugation` proves that the genuine SD16 extension interchanges the two
elementary four-groups. Compatible local action diagrams then force precisely
regular/transposition, transposition/regular, or even/even. The GL2(3) comparison
uses an actual Sylow equivalence and derives the semidihedral parameter four.
When the images of T and S agree, the marked four-group is fixed and the cases
agree.

`Assembly` connects these local diagrams with the numerical API and transports
the core identity through actual parabolic equivalences. Its strict bounds and
`disjoint_replacement_bound` use the actual natural fixed codimensions. The
actions need only be defined on S. Genuine compatible identifications and
action-kernel identities remain explicit inputs under this module's contract;
the parent owns their instantiation, the rank-inequality eliminations,
replacement and terminal assembly of 15.3.25.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.25, printed pp.1133–1134 (PDF pp.1150–1151).
-/
