module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.Preparation
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.CubicDegree
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.MinimalDegree
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Unitary.Model
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.Models

/-!
# The full unitary natural-module recognition in K.3.3

The cubic actor bounds the degree of the actual central-cover pullback by
`6*s`. The binary minimal-degree classifier constructs natural coordinates,
which force the covering kernel to be trivial. Descending those coordinates
identifies the original layer with the full SU₃ group and intertwines its
original binary action with matrix multiplication on columns. The coefficient
field has order `(2^s)^2`, the fixed field has order `2^s`, and the center has
order three for odd `s` and order one for even `s`.

Only the earlier group-only central cover remains an input. The adapter uses
the existing `IsCentralQuotient` contract and produces the literal
`UnitaryModel` consumed by the independent ratio calculation. Neither natural
coordinates, a degree bound, nor injectivity of the covering map is assumed.
The earlier covering producer and final rank-one assembly are recorded in
`UnitaryRecognition/Source.md`.

Source: Aschbacher--Smith K.3.3, printed p.456; Guralnick--Malle,
*Classification of 2F-modules, II*, Theorem 4.10, Proposition 4.11 and Table 7.
-/

public section
namespace CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition
open BenderSuzuki.MatrixGroups Subgroup
open ChapterB.ComponentRecognition.KnownFFTypes.Classical

variable {G V F : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [Field F] [Finite F] [Algebra (ZMod 2) F]
  (J : HermitianForm 3 F) {s : ℕ} (hs : 2 ≤ s)
  (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
  (h : SourceHypotheses ρ L)

include hs hcard hconj h

/-- K.3.3 recognition from the permitted group-only central cover. The cubic
degree bound is discharged, and the resulting intertwiner proves the cover
injective, including when the full special group has center of order three. -/
theorem source_naturalModel (π : J.specialSubgroup →* L)
    (hπ : Function.Surjective π) (hker : π.ker ≤ center J.specialSubgroup) :
    Nonempty (NaturalModel ρ L J) ∧ Function.Injective π :=
  MinimalDegree.source_naturalModel_of_finrank_le J h π hπ hs hcard hconj
    (CubicDegree.source_degree_le J hs hcard hconj h π hπ hker)

/-- The possible projective covering kernel is proved trivial, rather than
excluded as an assumption of recognition. -/
theorem source_cover_ker_eq_bot (π : J.specialSubgroup →* L)
    (hπ : Function.Surjective π) (hker : π.ker ≤ center J.specialSubgroup) :
    π.ker = ⊥ :=
  π.ker_eq_bot_iff.mpr (source_naturalModel J hs hcard hconj h π hπ hker).2

/-- The explicit group equivalence and binary linear intertwiner for the
original source action, together with the source degree, fixed-field order,
and full center order. The matrix convention is multiplication on columns. -/
theorem source_recognition (π : J.specialSubgroup →* L)
    (hπ : Function.Surjective π) (hker : π.ker ≤ center J.specialSubgroup) :
    ∃ (e : L ≃* J.specialSubgroup) (E : V ≃ₗ[ZMod 2] (Fin 3 → F)),
      (∀ (g : L) (v : V), E (ρ (g : G) v) = Matrix.mulVec (e g).val.val (E v)) ∧
      Module.finrank (ZMod 2) V = 6 * s ∧
      Nat.card {x : F // J.conj x = x} = 2 ^ s ∧
      Nat.card (center L) = Nat.gcd 3 (2 ^ s + 1) := by
  obtain ⟨⟨M⟩, _⟩ := source_naturalModel J hs hcard hconj h π hπ hker
  refine ⟨M.groupEquiv, M.coordinates, M.intertwines, M.finrank_eq hcard,
    fixedField_card J (by omega) hcard hconj, ?_⟩
  rw [Nat.card_congr (centerCongr M.groupEquiv).toEquiv]
  exact special_center_card J (by omega) hcard hconj

/-- Odd exponents retain the order-three center on the original layer. -/
theorem source_center_card_of_odd (π : J.specialSubgroup →* L)
    (hπ : Function.Surjective π) (hker : π.ker ≤ center J.specialSubgroup)
    (hodd : Odd s) : Nat.card (center L) = 3 := by
  obtain ⟨⟨M⟩, _⟩ := source_naturalModel J hs hcard hconj h π hπ hker
  exact M.center_card_of_odd hodd hcard hconj

/-- Even exponents have trivial center on the original layer. -/
theorem source_center_card_of_even (π : J.specialSubgroup →* L)
    (hπ : Function.Surjective π) (hker : π.ker ≤ center J.specialSubgroup)
    (heven : Even s) : Nat.card (center L) = 1 := by
  obtain ⟨⟨M⟩, _⟩ := source_naturalModel J hs hcard hconj h π hπ hker
  exact M.center_card_of_even (by omega) heven hcard hconj

/-- Apply recognition to the exact group-only output of the earlier classical
covering argument. The quotient's normal subgroup and its literal quotient
instance are retained when constructing the surjective central covering map. -/
theorem source_naturalModel_of_centralQuotient
    (hc : IsCentralQuotient L J.specialSubgroup) : Nonempty (NaturalModel ρ L J) := by
  obtain ⟨N, hN, hcentral, ⟨e⟩⟩ := hc
  let π : J.specialSubgroup →* L := e.symm.toMonoidHom.comp (QuotientGroup.mk' N)
  have hπ : Function.Surjective π :=
    e.symm.surjective.comp (QuotientGroup.mk'_surjective N)
  have hker : π.ker ≤ center J.specialSubgroup := by
    dsimp only [π]
    rw [MonoidHom.ker_comp_of_injective _ _ e.symm.injective, QuotientGroup.ker_mk']
    exact hcentral
  exact (source_naturalModel J hs hcard hconj h π hπ hker).1

omit hs hcard hconj h in
/-- Pass the recognized coordinates unchanged to the independent ratio
calculation's model: the group, binary coordinates, and column action agree. -/
@[expose] def NaturalModel.toUnitaryModel {J : HermitianForm 3 F}
    (M : NaturalModel ρ L J) : UnitaryModel J ρ L :=
  ⟨M.groupEquiv, M.coordinates, M.intertwines⟩

/-- Discharge the natural-module premise of `SourceHypotheses.unitary_case`
using the earlier classical central-quotient contract. No representation
recognition or numerical premise remains for that consumer. -/
theorem source_unitaryModel_of_centralQuotient
    (hc : IsCentralQuotient L J.specialSubgroup) : Nonempty (UnitaryModel J ρ L) := by
  obtain ⟨M⟩ := source_naturalModel_of_centralQuotient J hs hcard hconj h hc
  exact ⟨M.toUnitaryModel⟩

end CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition
