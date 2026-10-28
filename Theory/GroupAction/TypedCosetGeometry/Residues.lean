module

public import Theory.GroupAction.TypedCosetGeometry.Residues.Flags
public import Theory.GroupAction.TypedCosetGeometry.Residues.Connectivity
public import Theory.GroupAction.TypedCosetGeometry.Residues.Local
public import Theory.GroupAction.TypedCosetGeometry.Residues.Quotient
public import Theory.GroupAction.TypedCosetGeometry.Residues.Transport

/-!
# Rank-three coset geometry

The middle subgroup product condition supplies common representatives of flags,
flag transitivity and the complete bipartite incidence of line residues, including
the point–plane containments along a line. Global and local generation give
connectivity of the incidence graph and every vertex residue.

Each standard residue is equivariantly identified with the intrinsic rank-two
coset geometry in its vertex group. Its action kernel is the normal core of the
chamber subgroup there, and its typed cardinalities are the parabolic indices;
index three at both line endpoints gives the three-by-three line residue.
Surjections with kernel in both parabolics transport this identification and
its action kernel to local quotients. None of these results requires ambient
finiteness.

The component files separate the common-representative argument (`Flags`),
generation and paths (`Connectivity`), intrinsic cosets (`Local`), subgroup
correspondence (`Quotient`), and their residue-level composition (`Transport`).

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.5.3–6,
printed pp. 419–420, and Aschbacher, *Sporadic Groups*, §4.
-/
