module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.Setup
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.Transport
public import Theory.Representation.SU3.BinaryDegree
public import Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel
public import Theory.SpecificGroups.SU3.EvenProjectiveComparison

/-!
# Preparation and faithful-cover assembly for unitary recognition

The source action pulled back along an actual SU₃ cover is irreducible and
nontrivial, and has the same action image as the original layer. In particular
the ambient cubic actor survives in its full linear normalizer, without
assuming that normalizer is SQTK. The proved SU₃ degree minimum applies even
when this pulled-back action has a central kernel.

Once a natural intertwiner is constructed, equality of column actions forces
the covering kernel to be trivial. The resulting equivalence identifies the
original layer and its original binary action, and gives degree `6*s` and
center order three for odd `s` (order one for even `s`).

The missing cubic upper bound and minimal-degree recognition are independent
proof obligations. This module does not assert K.3.3 before those obligations
are discharged. Source: Aschbacher--Smith K.3.3, printed p.456;
Guralnick--Malle, *Classification of 2F-modules, II*, Theorem 4.10,
Proposition 4.11 and Table 7.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition
open BenderSuzuki.MatrixGroups Representation Representation.BinaryOffender
open Subgroup

universe u v w
variable {G : Type u} {V : Type v} {F : Type w}
  [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [Field F]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
  (J : HermitianForm 3 F)

section Coordinates
variable [Algebra (ZMod 2) F]

/-- The natural column action is faithful, so any action genuinely
quasiequivalent to it is faithful as an action of the full SU group. -/
theorem IsNatural.injective {σ : Representation (ZMod 2) J.specialSubgroup V}
    (h : IsNatural J σ) : Function.Injective σ := by
  obtain ⟨a, E, hE⟩ := h
  intro g k he
  apply a.injective
  apply Subtype.ext
  apply Units.ext
  apply Matrix.mulVec_injective
  funext v
  obtain ⟨v, rfl⟩ := E.surjective v
  rw [← hE, ← hE, he]

/-- A natural pullback cannot factor through a proper central quotient.
No injectivity of the covering map is an assumption. -/
theorem cover_injective_of_natural (π : J.specialSubgroup →* L)
    (hnat : IsNatural J ((ρ.comp L.subtype).comp π)) : Function.Injective π := by
  intro g k h
  apply hnat.injective J
  change ρ (π g : G) = ρ (π k : G)
  rw [h]

/-- Descend the actual coordinates to the original layer, preserving the
matrix convention. This is the assembly step after representation recognition. -/
theorem naturalModel_of_pullback (π : J.specialSubgroup →* L)
    (hπ : Function.Surjective π)
    (hnat : IsNatural J ((ρ.comp L.subtype).comp π)) :
    Nonempty (NaturalModel ρ L J) := by
  have hinj := cover_injective_of_natural J π hnat
  obtain ⟨a, E, hE⟩ := hnat
  let e : J.specialSubgroup ≃* L := MulEquiv.ofBijective π ⟨hinj, hπ⟩
  refine ⟨⟨e.symm.trans a, E, ?_⟩⟩
  intro g v
  have ht := hE (e.symm g) v
  change E (ρ (e (e.symm g) : G) v) = _ at ht
  simpa only [e.apply_symm_apply, MulEquiv.trans_apply] using ht

end Coordinates

/-- The image, and hence its full linear normalizer, is unchanged by the
surjective pullback. This retains the literal outer actors. -/
theorem pullback_actionImage (π : J.specialSubgroup →* L) (hπ : Function.Surjective π) :
    actionImage ((ρ.comp L.subtype).comp π) = actionImage (ρ.comp L.subtype) := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨π g, Units.ext rfl⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨k, rfl⟩ := hπ g
    exact ⟨k, Units.ext rfl⟩

section Source
variable [Finite G] [FiniteDimensional (ZMod 2) V]
  (h : SourceHypotheses ρ L) (π : J.specialSubgroup →* L)
  (hπ : Function.Surjective π)

include h hπ

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- Inflation preserves irreducibility even when the cover has a kernel. -/
theorem pullback_irreducible :
    IsIrreducible ((ρ.comp L.subtype).comp π) :=
  (irreducible_comp_surjective_iff π hπ (ρ.comp L.subtype)).mpr h.irreducible

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- The source action pulled back to SU is nontrivial; faithfulness of the
pullback is not used. -/
theorem pullback_nontrivial :
    ∃ g, ((ρ.comp L.subtype).comp π) g ≠ 1 := by
  let : IsSimpleGroup (L ⧸ center L) := h.quasisimple.simple
  let : Nontrivial L := Function.Surjective.nontrivial
    (QuotientGroup.mk'_surjective (center L))
  obtain ⟨l, hl⟩ := exists_ne (1 : L)
  obtain ⟨g, rfl⟩ := hπ l
  refine ⟨g, fun hg => hl ?_⟩
  apply Subtype.ext
  apply h.faithful
  change ρ (π g : G) = 1 at hg
  change ρ (π g : G) = ρ 1
  simpa only [map_one] using hg

/-- The source cubic bound holds on the same module for the full normalizer
of the possibly nonfaithful SU action. No SQTK assertion about that
normalizer is needed. -/
theorem pullback_normalizer_cubic_le_two :
    cubicRatio (normalizerRepresentation ((ρ.comp L.subtype).comp π)) ≤ 2 := by
  let : L.Normal := h.layer_normal
  have hc := Exceptional.cubicRatio_normalizer_le_two ρ L h.faithful h.smallCubic
  unfold normalizerRepresentation linearNormalizer at hc ⊢
  rwa [pullback_actionImage J π hπ]

variable [Finite F]

omit [Finite G] in
/-- The source lower degree bound retains the possible projective kernel. -/
theorem source_degree_lower {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ s)) :
    6 * s ≤ Module.finrank (ZMod 2) V :=
  Representation.SU3.BinaryDegree.finrank_ge J hs hcard hconj
    ((ρ.comp L.subtype).comp π) (pullback_nontrivial J h π hπ)

end Source

variable [Finite F]

/-- The fixed field has the source's order `2^s`, as distinguished from
the coefficient-field order `(2^s)^2`. -/
theorem fixedField_card {s : ℕ} (hs : 0 < s)
    (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ s)) :
    Nat.card {x : F // J.conj x = x} = 2 ^ s :=
  FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 s hs hcard hconj

/-- The center of the full special group, including the odd-exponent case. -/
theorem special_center_card {s : ℕ} (hs : 0 < s)
    (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ s)) :
    Nat.card (center J.specialSubgroup) = Nat.gcd 3 (2 ^ s + 1) := by
  rw [← J.specialToProjective_ker_eq_center
    (HermitianForm.EvenProjectiveComparison.center_eq_bot J hs hcard hconj)]
  have he : J.specialToProjective =
      Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel.project J := by
    apply MonoidHom.ext
    intro g
    apply Subtype.ext
    exact J.specialToProjective_apply_val g
  rw [he]
  exact Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel.card_project_kernel
    J hconj hcard

/-- The order-three center is present for every odd exponent. -/
theorem special_center_card_of_odd {s : ℕ} (hs : Odd s)
    (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ s)) :
    Nat.card (center J.specialSubgroup) = 3 := by
  rw [special_center_card J hs.pos hcard hconj]
  apply Nat.gcd_eq_left
  have hm := Nat.BinaryTorusParity.two_pow_mod_three s
  have ho := Nat.odd_iff.mp hs
  apply Nat.dvd_of_mod_eq_zero
  simp only [ho, show ¬ (1 : ℕ) = 0 by decide, if_false] at hm
  omega

/-- Even exponents have trivial center. -/
theorem special_center_card_of_even {s : ℕ} (hs : 0 < s) (he : Even s)
    (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ s)) :
    Nat.card (center J.specialSubgroup) = 1 := by
  rw [special_center_card J hs hcard hconj]
  have hm := Nat.BinaryTorusParity.two_pow_mod_three s
  rw [if_pos (Nat.even_iff.mp he)] at hm
  rw [Nat.gcd_rec]
  have hadd : (2 ^ s + 1) % 3 = 2 := by omega
  rw [hadd]
  decide

namespace NaturalModel
variable [Algebra (ZMod 2) F] {J} (M : NaturalModel ρ L J)
include M

/-- Natural coordinates have precisely the binary dimension asserted in K.3.3. -/
theorem finrank_eq {s : ℕ} (hcard : Nat.card F = (2 ^ s) ^ 2) :
    Module.finrank (ZMod 2) V = 6 * s := by
  have hd : Module.finrank (ZMod 2) F = 2 * s := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
    rw [hcard, Nat.card_eq_fintype_card, ZMod.card, ← pow_mul] at hc
    have he := (Nat.pow_right_injective (by decide : 1 < (2 : ℕ))) hc.symm
    omega
  rw [M.coordinates.finrank_eq, Module.finrank_pi_fintype]
  simp only [hd, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

/-- The center calculation transfers along the actual group identification. -/
theorem center_card_of_odd {s : ℕ} (hs : Odd s)
    (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ s)) : Nat.card (center L) = 3 := by
  rw [Nat.card_congr (centerCongr M.groupEquiv).toEquiv]
  exact special_center_card_of_odd J hs hcard hconj

/-- The original layer also has trivial center in even exponent. -/
theorem center_card_of_even {s : ℕ} (hs : 0 < s) (he : Even s)
    (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ s)) : Nat.card (center L) = 1 := by
  rw [Nat.card_congr (centerCongr M.groupEquiv).toEquiv]
  exact special_center_card_of_even J hs he hcard hconj

end NaturalModel
end CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition
