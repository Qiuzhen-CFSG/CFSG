module

public import CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage.LocalActions.Inputs
public import Theory.SpecificGroups.PSL3Two.SplitBlockActions.QuaternionResidual.Geometry
public import Theory.GroupTheory.PResidual.Defs
public import Theory.PGroupCore

/-!
# The common Sylow image and residual cubic

The quaternion geometry gives the common image of U and T_L, of order four,
and its normalization by the actual N_K(A). Two remaining local calculations
are kept separate: the outer relative-normalizer index is three, and its
two-core part induces exactly four automorphisms. Cauchy's theorem then
constructs a nonidentity cubic in the literal N_G(A)/C_G(A) and proves the
required generation equality.

The exports are conditional assembly lemmas, not the completed source
calculation: the two indices and centralizer containment still require the
earlier H/O₂(H) action and control of the extra two-core. In particular no
equality U = O₂(H), A₄ identification, or coordinate image is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
14.4.4, printed p.1007. The split-block branch supplies the marked swapping
involution, A = ⟨a,[U,a]⟩ = J(T_L), and T_L = U⟨a⟩. Its construction remains
with that branch's assembly owner.
-/

open Subgroup
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage

variable {G : Type*} [Group G] [Finite G]

/-- The actual residual image in the ambient group. -/
@[expose] public def quaternionResidual (H : Subgroup G) : Subgroup G :=
  (pResidual 2 H).map H.subtype

/-- The actual two-core image; it is not identified with U. -/
@[expose] public def quaternionTwoCore (H : Subgroup G) : Subgroup G :=
  (pCore 2 H).map H.subtype

/-- Extract the desired generator after the residual image order is known.
The common four-group and its normalization are proved from the embedded
quaternion geometry, rather than assumed as action-image data. -/
public theorem quaternionGenerators_of_image_order
    (H U A TL : Subgroup G) (d : QuaternionCentralProductData U)
    (a : G) (ha : a ^ 2 = 1) (hout : a ∉ U)
    (hswap : (d.left.map U.subtype).map (MulAut.conj a).toMonoidHom =
      d.right.map U.subtype)
    (hA : A = zpowers a ⊔ ⁅U, zpowers a⁆)
    (hTL : TL = U ⊔ zpowers a) (hTLN : TL ≤ normalizer (A : Set G))
    (hUK : U ≤ quaternionResidual H) (hHU : H ≤ normalizer (U : Set G))
    (horder : Nat.card (quotientImage A
      (quaternionResidual H ⊓ normalizer (A : Set G))) = 12) :
    Nonempty (QuaternionGenerators A (quaternionResidual H) TL) := by
  have hKU : quaternionResidual H ≤ normalizer (U : Set G) := by
    rintro _ ⟨k, _, rfl⟩
    exact hHU k.property
  obtain ⟨_, hfour, hle, hn⟩ := QuaternionResidual.common_image_of_swap U A TL
    (quaternionResidual H) d a ha hout hswap hA hTL hTLN hUK hKU
  obtain ⟨c, hc, hne, hnorm, hgen⟩ := QuaternionResidual.exists_cubic_supplement
    (quotientImage A TL)
    (quotientImage A (quaternionResidual H ⊓ normalizer (A : Set G)))
    hle hn hfour horder
  exact ⟨⟨c, hc, hne, hnorm, hgen⟩⟩

/-- Assemble the cubic on the literal quotient from independent outer and
two-core index calculations. Their source proofs are still obligations of
this module's final assembly, not conclusions of this conditional theorem. -/
public theorem quaternionGenerators_of_residual_indices
    (H U A TL : Subgroup G) (d : QuaternionCentralProductData U)
    (a : G) (ha : a ^ 2 = 1) (hout : a ∉ U)
    (hswap : (d.left.map U.subtype).map (MulAut.conj a).toMonoidHom =
      d.right.map U.subtype)
    (hA : A = zpowers a ⊔ ⁅U, zpowers a⁆)
    (hTL : TL = U ⊔ zpowers a) (hTLN : TL ≤ normalizer (A : Set G))
    (hUK : U ≤ quaternionResidual H) (hHU : H ≤ normalizer (U : Set G))
    (hcentral : (quaternionResidual H ⊓ normalizer (A : Set G)) ⊓
      centralizer (A : Set G) ≤ quaternionTwoCore H)
    (hfour : (centralizer (A : Set G)).relIndex
      ((quaternionResidual H ⊓ normalizer (A : Set G)) ⊓ quaternionTwoCore H) = 4)
    (hthree : (quaternionTwoCore H).relIndex
      (quaternionResidual H ⊓ normalizer (A : Set G)) = 3) :
    Nonempty (QuaternionGenerators A (quaternionResidual H) TL) := by
  apply quaternionGenerators_of_image_order H U A TL d a ha hout hswap hA hTL hTLN hUK hHU
  exact QuaternionResidual.card_image_of_two_indices A
    (quaternionResidual H ⊓ normalizer (A : Set G)) (quaternionTwoCore H)
    inf_le_right hcentral hfour hthree

end CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage
