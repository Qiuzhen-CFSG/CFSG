module

public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.FermatMersenne
public import Theory.AtlasPort.LinearGroups.G2.Basic
public import Theory.SpecificGroups.Triality.StandardModel
public import Theory.SpecificGroups.Tits.Presentation
public import BenderSuzuki.MatrixGroups.Suzuki
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Theory.Mathieu.M11.Basic
public import Theory.Mathieu.M12.Basic
public import Theory.Mathieu.M22.Basic
public import Theory.Mathieu.M23.Basic
public import Theory.Mathieu.M24.Basic
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS
public import Theory.SpecificGroups.Janko3.Model.Basic
public import Theory.SpecificGroups.Janko4.Model
public import Theory.SpecificGroups.Held.Model.Basic
public import Theory.SpecificGroups.Rudvalis.Model.Basic
public import Theory.SpecificGroups.Janko1.Model.Basic

/-!
# Concrete families for the quasithin output lists

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Theorem 0.1.2 (printed p.4), the repeated Main Theorem
on p.482, and Remark A.2.4 (p.33). Rank means relative Lie rank: U₃ has rank
one, and U₄ and U₅ have rank two. In unitary predicates q is the fixed-field
order; in particular U₅(4) uses matrices over a field of order 16.

The Bender and eleven-sporadic lists below are complete. The partial rank-two
list omits the general Ree family ²F₄(2^(2m+1)), m ≥ 1; the complete extension
is defined in `ClassificationModels.RankTwo`.
Its simple small endpoints use the actual commutator carriers Sp₄(2)′ and
G₂(2)′, and Parrott's presentation of ²F₄(2)′. Thus no exceptional isomorphism
is silently used to replace a derived group by another construction.

The sporadic carriers are the same sourced constructions used by
`KnownSimple.ConstructedSporadicCarriers` and `KnownSimple.LeechCarrierContribution`;
only the needed construction modules are imported here. J₂ and HS use the ATLAS
permutation carriers, without asserting comparison with the lattice ports.
Triality uses the genuine pinned D₄ graph-field construction. Membership and
transport always use actual multiplicative equivalences. No order, simplicity
or classification theorem is part of these definitions.
-/

@[expose] public section

universe u v

namespace CFSG.Quasithin.ClassificationModels

/-- The split-octonion automorphism construction at a specified field order. -/
def IsG2At (G : Type u) [Group G] (q : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
    Nonempty (G ≃* Atlas.G2.Model F)

/-- The rank-one groups in Remark A.2.4, in their nonabelian simple ranges. -/
inductive IsBenderModel (G : Type u) [Group G] : Prop
  | linear (f : ℕ) (hf : 2 ≤ f) (iso : ClassicalGroup.IsPSL G 2 (2 ^ f))
  | unitary (f : ℕ) (hf : 2 ≤ f) (iso : ClassicalGroup.IsPSU G 3 (2 ^ f))
  | suzuki (m : ℕ) (hm : 1 ≤ m)
      (iso : Nonempty (G ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))

/-- Available rank-two groups over the field of order `2^f`, with U₅ only
at q = 4. This list omits the general Ree family, and is deliberately partial. -/
inductive IsRankTwoModelWithoutReeF4 (G : Type u) [Group G] (f : ℕ) : Prop
  | linear (hf : 1 ≤ f) (iso : ClassicalGroup.IsPSL G 3 (2 ^ f))
  | unitary_four (hf : 1 ≤ f) (iso : ClassicalGroup.IsPSU G 4 (2 ^ f))
  | unitary_five (hf : f = 2) (iso : ClassicalGroup.IsPSU G 5 (2 ^ f))
  | symplectic (hf : 2 ≤ f) (iso : ClassicalGroup.IsPSp G 2 (2 ^ f))
  | g2 (hf : 2 ≤ f) (iso : IsG2At G (2 ^ f))
  | triality (hf : 1 ≤ f) (iso : Triality.Standard.IsTrialityGroupAt (2 ^ f) G)
  | symplectic_derived (hf : f = 1)
      (iso : Nonempty (G ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))))
  | g2_derived (hf : f = 1)
      (iso : Nonempty (G ≃* commutator (Atlas.G2.Model (ZMod 2))))
  | tits (hf : f = 1) (iso : Nonempty (G ≃* Tits.ParrottGroup))

/-- Exactly the eleven sporadic names in the Main Theorem. -/
inductive SporadicName
  | m11 | m12 | m22 | m23 | m24 | j2 | j3 | j4 | hs | he | ru

/-- The sourced, fixed carrier for each sporadic output name. -/
def SporadicName.Carrier : SporadicName → Type
  | .m11 => Sporadic.Mathieu.M11
  | .m12 => Sporadic.Mathieu.M12
  | .m22 => Sporadic.Mathieu.M22
  | .m23 => Sporadic.Mathieu.M23
  | .m24 => Sporadic.Mathieu.M24
  | .j2 => Sporadic.LeechRelated.J2.Carrier
  | .j3 => Sporadic.Janko3.Model
  | .j4 => Janko4.Model
  | .hs => Sporadic.LeechRelated.HS.Carrier
  | .he => Held.He
  | .ru => Rudvalis.Model

noncomputable instance SporadicName.carrierGroup (name : SporadicName) :
    Group name.Carrier := by
  cases name <;> unfold SporadicName.Carrier <;> infer_instance

/-- An actual isomorphism to one of the eleven sporadic constructions. -/
def IsSporadicModel (G : Type u) [Group G] : Prop :=
  ∃ name : SporadicName, Nonempty (G ≃* name.Carrier)

/-- The additional output of the Even Type Theorem (p.483), separate from QTKE. -/
def IsEvenTypeAdditionalModel (G : Type u) [Group G] : Prop :=
  Nonempty (G ≃* Janko1.Model)

variable {G : Type u} {H : Type v} [Group G] [Group H]

theorem IsG2At.of_mulEquiv {q : ℕ} (h : IsG2At G q) (e : H ≃* G) :
    IsG2At H q := by
  obtain ⟨F, hF, hfin, hq, ⟨a⟩⟩ := h
  exact ⟨F, hF, hfin, hq, ⟨e.trans a⟩⟩

theorem IsBenderModel.of_mulEquiv (h : IsBenderModel G) (e : H ≃* G) :
    IsBenderModel H := by
  cases h with
  | linear f hf iso => exact .linear f hf (iso.of_mulEquiv e)
  | unitary f hf iso => exact .unitary f hf (iso.of_mulEquiv e)
  | suzuki m hm iso => exact .suzuki m hm (iso.map fun a => e.trans a)

theorem IsRankTwoModelWithoutReeF4.of_mulEquiv {f : ℕ}
    (h : IsRankTwoModelWithoutReeF4 G f) (e : H ≃* G) :
    IsRankTwoModelWithoutReeF4 H f := by
  cases h with
  | linear hf iso => exact .linear hf (iso.of_mulEquiv e)
  | unitary_four hf iso => exact .unitary_four hf (iso.of_mulEquiv e)
  | unitary_five hf iso => exact .unitary_five hf (iso.of_mulEquiv e)
  | symplectic hf iso => exact .symplectic hf (iso.of_mulEquiv e)
  | g2 hf iso => exact .g2 hf (iso.of_mulEquiv e)
  | triality hf iso => exact .triality hf (iso.of_mulEquiv e)
  | symplectic_derived hf iso => exact .symplectic_derived hf (iso.map fun a => e.trans a)
  | g2_derived hf iso => exact .g2_derived hf (iso.map fun a => e.trans a)
  | tits hf iso => exact .tits hf (iso.map fun a => e.trans a)

theorem IsSporadicModel.of_mulEquiv (h : IsSporadicModel G) (e : H ≃* G) :
    IsSporadicModel H := by
  obtain ⟨name, ⟨a⟩⟩ := h
  exact ⟨name, ⟨e.trans a⟩⟩

theorem IsEvenTypeAdditionalModel.of_mulEquiv
    (h : IsEvenTypeAdditionalModel G) (e : H ≃* G) : IsEvenTypeAdditionalModel H :=
  h.map fun a => e.trans a

theorem isG2At_mulEquiv_iff {q : ℕ} (e : G ≃* H) : IsG2At G q ↔ IsG2At H q :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

theorem isBenderModel_mulEquiv_iff (e : G ≃* H) : IsBenderModel G ↔ IsBenderModel H :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

theorem isRankTwoModelWithoutReeF4_mulEquiv_iff {f : ℕ} (e : G ≃* H) :
    IsRankTwoModelWithoutReeF4 G f ↔ IsRankTwoModelWithoutReeF4 H f :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

theorem isSporadicModel_mulEquiv_iff (e : G ≃* H) : IsSporadicModel G ↔ IsSporadicModel H :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

theorem isEvenTypeAdditionalModel_mulEquiv_iff (e : G ≃* H) :
    IsEvenTypeAdditionalModel G ↔ IsEvenTypeAdditionalModel H :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

end CFSG.Quasithin.ClassificationModels
