module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceTwenty.Reduction
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.SymmetricCentralizer
public import Theory.Representation.BinaryOffender.InvolutionHomology
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.Representation.SymmetricEightConstituents

/-!
# The marked layers needed for the symmetric outer HS calculation

The proposed identification concerns the literal image of t-1 and the
literal quotient C_V(t)/[V,t], acted on by C_G(t) intersected with F*(G).
Its group marking is compared, through conjugation on the specified HS
quotient, with the already constructed S8 embedding. In particular this
is a relative HS centralizer, not the full centralizer 2 x S8.

These are explicit, still unconstructed representation data for the
6,8,6 filtration in Guralnick--Malle, Classification of 2F-modules I,
Proposition 5.1, HS paragraph, preprint pp.16--17. The theorems below
transport them faithfully to elementary actors and preserve both costs
across the possibly nonsplit extensions. They do not assert recognition
of an arbitrary source module.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open Chapter16.OtherPreliminaries.JankoTwoHigmanSims

namespace Twenty.Symmetric
namespace Models
abbrev S8 := Representation.SymmetricEightConstituents.S8
abbrev Six := Representation.SymmetricEightConstituents.Six
abbrev Eight := Representation.SymmetricEightConstituents.Eight
abbrev deleted := Representation.SymmetricEightConstituents.deleted
noncomputable abbrev induced := Representation.SymmetricEightConstituents.symmetricRepresentation
end Models

/-- The remaining local calculation on the concrete induced model. This
includes regular rank-three subgroups with all nonidentity elements of
permutation type 2^4; a non-2^4 element cannot be selected by rank alone. -/
def InducedRankThreeBound : Prop :=
  ∀ B : Subgroup Models.S8, IsElementaryTwo B → 3 ≤ rank B →
    4 ≤ fixedCodim Models.induced B

universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- The centralizer inside the actual covering component. -/
noncomputable def innerCentralizer (t : G) : Subgroup G :=
  centralizer {t} ⊓ generalizedFitting G

noncomputable abbrev moved (ρ : Representation (ZMod 2) G V) (t : G) :=
  InvolutionHomology.moved ρ t (innerCentralizer t) inf_le_left

noncomputable abbrev homology (ρ : Representation (ZMod 2) G V) (t : G) :=
  InvolutionHomology.homology ρ t (innerCentralizer t) inf_le_left

/-- Actual intertwining identifications, with the original group marking.
This is a construction target, not an assumption of the source theorem. -/
structure Factors (ρ : Representation (ZMod 2) G V)
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* HS) (t : G) where
  conjugator : MulAut HS
  outer_action : quotientAction e t = conjugator *
    (show MulAut HS from _root_.Sporadic.LeechRelated.HS.generated.normalizerMonoidHom
      HSOuter.symmetricNormalizer) * conjugator⁻¹
  marking : innerCentralizer t →* Models.S8
  marking_action : ∀ c : innerCentralizer t,
    quotientAction e (c : G) = MulAut.conj
      (conjugator (show HS from (HSOuter.SymmetricCentralizer.embedding (marking c)).val))
  six : (moved ρ t).toSubmodule ≃ₗ[ZMod 2] Models.Six
  six_equivariant : ∀ c v,
    six ((moved ρ t).toRepresentation c v) = Models.deleted (marking c) (six v)
  eight : ((InvolutionHomology.fixed ρ t (innerCentralizer t) inf_le_left).toSubmodule ⧸
    (sectionLower (ρ.comp (innerCentralizer t).subtype) (moved ρ t)
      (InvolutionHomology.fixed ρ t (innerCentralizer t) inf_le_left)).toSubmodule)
    ≃ₗ[ZMod 2] Models.Eight
  eight_equivariant : ∀ c v,
    eight (homology ρ t c v) = Models.induced (marking c) (eight v)

variable {e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* HS}
  {t : G} (F : Factors ρ e t)

/-- The marking loses no elementary actor; this uses faithfulness on the
original HS quotient, not faithfulness of a chosen matrix representation. -/
theorem Factors.marking_injective_on_elementary (h : SourceHypotheses ρ)
    (B : Subgroup (innerCentralizer t)) [IsElementaryAbelian 2 B] :
    Function.Injective (F.marking.comp B.subtype) := by
  let K := innerCentralizer t
  let D := B.map K.subtype
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.map K.subtype
  have hi := quotientAction_injective_on_elementary h e D
  intro x y hxy
  have hx : (x.val : G) ∈ D := mem_map_of_mem K.subtype x.property
  have hy : (y.val : G) ∈ D := mem_map_of_mem K.subtype y.property
  have he : quotientAction e (x.val : G) = quotientAction e (y.val : G) := by
    change F.marking x.val = F.marking y.val at hxy
    rw [F.marking_action x.val, F.marking_action y.val, hxy]
  have hh : (⟨x.val, hx⟩ : D) = ⟨y.val, hy⟩ := hi he
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : D => (z : G)) hh

/-- Rank is retained on the actual marked subgroup of S8. -/
theorem Factors.rank_map_marking (h : SourceHypotheses ρ)
    (B : Subgroup (innerCentralizer t)) [IsElementaryAbelian 2 B] :
    rank (B.map F.marking) = rank B := by
  let f := F.marking.comp B.subtype
  have hi : Function.Injective f := F.marking_injective_on_elementary h B
  have he := Nat.card_congr (MonoidHom.ofInjective hi).toEquiv
  have hr : f.range = B.map F.marking := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  change Nat.card B = Nat.card f.range at he
  rw [hr] at he
  exact congrArg (Nat.log 2) he.symm

variable [FiniteDimensional (ZMod 2) V]

include F in
/-- Recognition of the image as the deleted six-space determines the
displacement exactly, without any splitting of V. -/
theorem Factors.displacement : fixedCodim ρ (zpowers t) = 6 := by
  have hd := F.six.finrank_eq
  rw [Representation.SymmetricEightConstituents.six_finrank] at hd
  exact (InvolutionHomology.moved_finrank ρ t (innerCentralizer t) inf_le_left).symm.trans hd

/-- Both constituent costs add to the involution's six-dimensional cost,
for the literal actor and its marked inner subgroup. -/
theorem Factors.codim_bound (ht : t ^ 2 = 1) (A : Subgroup G) (htA : t ∈ A)
    (B : Subgroup (innerCentralizer t))
    (hBA : B.map (innerCentralizer t).subtype ≤ A) :
    6 + fixedCodim Models.induced (B.map F.marking) +
      fixedCodim Models.deleted (B.map F.marking) ≤ fixedCodim ρ A := by
  have hbound := InvolutionHomology.codim_bound ρ t (innerCentralizer t) inf_le_left
    ht A htA B hBA
  rw [F.displacement,
    fixedCodim_map_equivariant (homology ρ t) Models.induced F.marking F.eight
      F.eight_equivariant B,
    fixedCodim_map_equivariant (moved ρ t).toRepresentation Models.deleted F.marking F.six
      F.six_equivariant B] at hbound
  exact hbound

end Twenty.Symmetric
end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims
