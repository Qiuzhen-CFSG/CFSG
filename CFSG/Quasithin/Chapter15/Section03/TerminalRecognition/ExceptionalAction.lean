module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition
public import Theory.Representation.BinaryOffender.EquivariantStabilizer
public import Theory.Representation.HexacodeAction
public import Theory.Representation.HexacodeAction.Cover

/-!
# Coordinates for the exceptional terminal action

The even hexacode group is a concrete quasisimple triple cover of `A₆`.
The full hexacode group acts faithfully in binary dimension six. We
transfer stabilizers from that action to the actual centralizer quotient
acting on `V₀ = ⟨Vᴳ⁰⟩`, retaining both the image of `X` and the specified
plane subgroup. The subgroup equivalence below can be composed with a
model stabilizer quotient and the lifting theorem in `TerminalRecognition`.

The descendant `ExceptionalAction.Source` assembles the constructed actor
and vector equivalences, the Thompson-image equality, recognition of the
specified source planes and their actual `A₅` quotients from earlier local
geometry and classification witnesses. This base module supplies the
equivariant transport used by that recognition chain; keeping the source
consumer above it preserves the module dependency direction.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, final
proof of 15.3.1, printed p.1155 (PDF p.1172); covering convention A.3.5,
printed p.43, and the four-element field action K.1.3, printed p.453.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction

open Subgroup Atlas.Codes Representation.BinaryOffender
open scoped IsMulCommutative

variable {H : Type*} [Group H]
  (V : Subgroup H) [IsElementaryAbelian 2 (moduleClosure V)]
  (hC : IsPGroup 2 (centralizer (V : Set H)))
  (hcore : pCore 2 H ≤ centralizer (V : Set H))

/-- Genuine linear coordinates on the hexacode determine the dimension of `V₀`. -/
theorem moduleClosure_finrank_of_hexacode_equiv
    (e : Additive (moduleClosure V) ≃ₗ[ZMod 2] hexacode) :
    Module.finrank (ZMod 2) (Additive (moduleClosure V)) = 6 :=
  e.finrank_eq.trans hexacode_finrank

/-- Equivariant coordinates identify the actual plane stabilizer in the image
of `X` with the even hexacode stabilizer of the image of that same plane. -/
noncomputable def planeStabilizerEquiv_hexacode (X P : Subgroup H)
    (f : coreQuotient H ≃* HexAutomorphisms)
    (e : Additive (moduleClosure V) ≃ₗ[ZMod 2] hexacode)
    (he : ∀ g v, e (quotientAction V hC hcore g v) =
      Representation.Hexacode.action (f g) (e v))
    (hX : (X.map coreProjection).map f.toMonoidHom = hexSign.ker) :
    (X.map coreProjection ⊓
      subspaceStabilizer (quotientAction V hC hcore) (planeSubspace V P) :
        Subgroup (coreQuotient H)) ≃*
    (hexSign.ker ⊓ subspaceStabilizer Representation.Hexacode.action
      ((planeSubspace V P).map e.toLinearMap) : Subgroup HexAutomorphisms) :=
  (equivariantStabilizerEquiv (quotientAction V hC hcore)
    Representation.Hexacode.action f e he (X.map coreProjection) (planeSubspace V P)).trans
      (MulEquiv.subgroupCongr (by rw [hX]))

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction
