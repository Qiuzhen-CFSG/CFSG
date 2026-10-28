module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.MarkedPlane.Transport
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.MarkedPlane.Scalar
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.MarkedPlane.FullWeight
public import Theory.Representation.HexacodeAction.Field

/-!
# Recognition of the actual source definite planes

The shared configuration retains the source `Y_E`, `Y_F`, the conjugate
singular planes, the local groups and cores, and their compatible orthogonal
marking. Transport identifies the literal ambient subgroup in the hexacode,
preserves its dimension, and carries normalizers and centralizers to the
correct stabilizers and fixed spaces.

The external `Y_E` action commutes with the even hexacode group and hence is
cubic scalar. Its nontrivial action on `V` makes each definite summand
scalar-stable. The residual product makes weight constant on the three
nonzero orthogonal support patterns, of sizes three, three and nine. The
Sylow-stable scalar four-space has weight total 72; since nonzero codewords
have weight four or six, both definite summands have full weight.

The assembly below discharges both scalar premises of the weight argument.
`localPlane_isFullWeightScalarPlane` applies it to the literal subgroup of
`G₀` and the supplied coordinate map. The construction of those coordinates
and of `SourceConfiguration` remains with the parent recognition theorem.

The earlier clauses used are the compatible orthogonal action and residual
image of 15.3.2 and 15.3.7 (pp.1121–1122), the definition of the two-residual
`Y_E` and `V = [V,Y_E]` in 15.3.66(5) (p.1152), and `M = YT`,
`R = C_G(V)` and `|Y_E/O₂(Y_E)| = 3` in 15.3.67(1),(3). We use the
conjugate construction of `Y_F`, the product `Y = Y_E Y_F O₂(Y)`, and the
definitions of `G₁,G₂,G₀` preceding 15.3.68 (p.1154); normalization of
`Y_E`, containment of `V`, and the Sylow conclusion of 15.3.68(1)–(3);
and the bound on `O₂(Y_F)` in the final proof (p.1155). The bound on
`O₂(Y)` comes from 15.3.7. All the other marked source relations remain
in the shared configuration; no further source premise is added here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, printed
pp.1121–1122 and 1152–1155, with the field convention of K.1.3 on p.453.
-/

public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.MarkedPlane

variable {G : Type*} [Group G] [Finite G] {G₀ M V : Subgroup G}
  {d : NaturalOrthogonalAction M V}
  [IsElementaryAbelian 2 (moduleClosure (V.subgroupOf G₀))]
  {hC : IsPGroup 2 (centralizer (V.subgroupOf G₀ : Set G₀))}
  {hcore : pCore 2 G₀ ≤ centralizer (V.subgroupOf G₀ : Set G₀)}
  (c : HexacodeCoordinates (V.subgroupOf G₀) hC hcore)
  (cfg : SourceConfiguration G₀ M V d)

include cfg

/-- Both actual definite summands have binary dimension two, are stable under
the cubic scalar, and have weight six at every nonzero vector. -/
theorem vectorImage_plane_isFullWeightScalarPlane (i : OrthogonalPlaneIndex) :
    Representation.Hexacode.IsFullWeightScalarPlane (vectorImage c (d.plane i)) :=
  ⟨vectorImage_plane_finrank c cfg i, plane_scalar_stable c cfg i,
    vectorImage_plane_full_weight c cfg (first_residual_scalarAction c cfg)
      (plane_scalar_stable c cfg) i⟩

/-- Recognition for the literal source plane inside `G₀`, using the given
coordinates on its normal-closure module. No scalar or weight premise remains. -/
theorem localPlane_isFullWeightScalarPlane (i : OrthogonalPlaneIndex) :
    Representation.Hexacode.IsFullWeightScalarPlane
      ((planeSubspace (V.subgroupOf G₀) (localPlane G₀ M V d i)).map
        c.vectors.toLinearMap) := by
  rw [← vectorImage_plane c i]
  exact vectorImage_plane_isFullWeightScalarPlane c cfg i

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.MarkedPlane
