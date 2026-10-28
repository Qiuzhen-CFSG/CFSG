module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Covers
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.PSL2Recognition.Preparation
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.PSL2Recognition.Models
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.PSL2Recognition.DegreeSelection
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.PSL2Recognition.TripleExclusion
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.RankOneRecognition
public import Theory.Representation.SL2.BinarySmallInvolution.Triple
public import Theory.Representation.SL2.BinarySmallInvolution.Hermitian
public import Theory.Representation.OrthogonalFourMinusHermitianEquiv
public import Theory.Representation.Quotient

/-!
# Recognition of the binary PSL₂ rank-one modules

The actual even central quotient identifies the layer with SL₂ over its binary
field. The source actor has two-rank at most the field degree, and at odd
degree its two-subgroups lie in the layer. These deductions are re-exported
from `Preparation`.

The existing highest-weight classifier gives the natural, Hermitian, and
SL₂(8) triple alternatives once the small-degree bound has been proved.
The assembly converts the first two to the actual marked models used in K.3,
retaining their distinct Schur fields. `DegreeSelection` derives the degree
bound from the original ambient cubic actor, and `TripleExclusion` eliminates
the third alternative using its fixed spaces. Thus `psl2_module_recognition`
proves the unconditional K.3.1 dichotomy from the actual central quotient.
The earlier conditional interface is preserved.

The Hermitian field identification and intertwiner are retained in
`BinarySmall.IsHermitian`. The re-exported `hermitianScalarExtensionEquiv`
identifies its fixed-field model over the quadratic field with N tensor N^σ;
`OrthogonalModel.minus_intertwines` gives the actual minus-orthogonal action.
Both comparisons include s=1. The specialization `binary_recognition_four`
distinguishes the two four-dimensional A₅ modules by Schur degrees two and one.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), K.3.1,
printed pp.453--454; Guralnick--Malle [GM04], Proposition 4.1 and Table 7.
-/

@[expose] public section

open scoped MatrixGroups
open Representation Representation.SL2
namespace CFSG.Quasithin.ChapterK.RankOne

universe u v

variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}


namespace SourceHypotheses

omit [Finite G] in
/-- The exhaustive small-degree alternatives after transport from the actual
layer `L` to the literal matrix group `SL₂(K)`. -/
theorem binary_module_alternatives
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (hh : SourceHypotheses ρ L) (e : L ≃* SL(2,K)) (r : ℕ) (hr : 2 ≤ r)
    (hcard : Nat.card K = 2 ^ r)
    (hdegree : Module.finrank (ZMod 2) V ≤ 2 * (r + 1)) :
    let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
    (Module.finrank (ZMod 2) V = 2 * r ∧
        Representation.SL2.BinarySmall.IsNatural σ) ∨
    (∃ s : ℕ, 0 < s ∧ r = 2 * s ∧
      Module.finrank (ZMod 2) V = 2 * r ∧
      ∃ hs : 0 < s, letI : NeZero s := ⟨hs.ne'⟩
        Representation.SL2.BinarySmall.IsHermitian σ s) ∨
    (r = 3 ∧ Module.finrank (ZMod 2) V = 8 ∧
      Representation.SL2.BinarySmall.IsTriple σ ∧
      Nonempty (K ≃+* GaloisField 2 3) ∧
      ∀ τ : K ≃+* K, ∃ j : ℕ, j < 3 ∧
        (iterateFrobeniusEquiv K 2 1) ^ j = τ) := by
  let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : Representation.IsIrreducible σ :=
    (Representation.irreducible_comp_surjective_iff e.symm.toMonoidHom
      e.symm.surjective (ρ.comp L.subtype)).mpr hh.irreducible
  have hf : Function.Injective σ :=
    hh.faithful.comp (L.subtype_injective.comp e.symm.injective)
  let : Theory.GroupTheory.IsQuasisimple L := hh.quasisimple
  let : IsSimpleGroup (L ⧸ Subgroup.center L) := hh.quasisimple.simple
  rcases CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.binary_small_faithful_classification σ
      hf r hr hcard hdegree with hnat | hherm | htriple
  · exact Or.inl ⟨hnat.2.1, hnat.2.2⟩
  · obtain ⟨hrs, hv, ⟨hs, hhm⟩⟩ := hherm
    exact Or.inr (Or.inl ⟨_, hs, by omega, hv, ⟨hs, hhm⟩⟩)
  · obtain ⟨hs, hr3, hv, ht, hfield, hfrob⟩ := htriple
    exact Or.inr (Or.inr ⟨hr3, hv, ht, hfield, hfrob⟩)

end SourceHypotheses

end CFSG.Quasithin.ChapterK.RankOne

open scoped MatrixGroups MonoidAlgebra
open Representation Representation.SL2 Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterK.RankOne.SourceHypotheses
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
  {K : Type*} [Field K] [Finite K] [CharP K 2]
local instance : Algebra (ZMod 2) K := ZMod.algebra K 2

/-- Conditional K.3.1 assembly. The two extra inputs are the degree selection
and the intrinsic triple-module exclusion. The latter is applied after proving
that the original cubic actor restricts to the layer, since its exponent is odd.
The Schur degrees distinguish the two four-dimensional modules when r=2. -/
theorem binary_recognition_of_degree_and_triple_exclusion
    (h : SourceHypotheses ρ L) (e : L ≃* SL(2,K))
    (r : ℕ) (hr : 2 ≤ r) (hc : Nat.card K = 2 ^ r)
    (hd : Module.finrank (ZMod 2) V ≤ 2 * (r + 1))
    (ht : r = 3 →
      BinarySmall.IsTriple ((ρ.comp L.subtype).comp e.symm.toMonoidHom) →
      ¬ cubicRatio ((ρ.comp L.subtype).comp e.symm.toMonoidHom) ≤ 2) :
    let σ : Representation (ZMod 2) SL(2,K) V := (ρ.comp L.subtype).comp e.symm.toMonoidHom
    let d := Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] σ.asModule)
    Module.finrank (ZMod 2) V = 2 * r ∧
      ((d = r ∧ Nonempty (NaturalModel (F := K) ρ L)) ∨
      ∃ s : ℕ, r = 2 * s ∧ d = s ∧
        ∃ hs : 0 < s, letI : NeZero s := ⟨hs.ne'⟩
          BinarySmall.IsHermitian σ s ∧ Nonempty (OrthogonalModel s ρ L)) := by
  let σ : Representation (ZMod 2) SL(2,K) V := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : Representation.IsIrreducible σ :=
    (Representation.irreducible_comp_surjective_iff e.symm.toMonoidHom
      e.symm.surjective (ρ.comp L.subtype)).mpr h.irreducible
  have hf : Function.Injective σ :=
    h.faithful.comp (L.subtype_injective.comp e.symm.injective)
  rcases CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.binary_small_faithful_classification
      σ hf r hr hc hd with hn | hh | hx
  · exact ⟨hn.2.1, Or.inl ⟨hn.1, ⟨naturalModelOfIsNatural e hn.2.2⟩⟩⟩
  · obtain ⟨hrs, hv, hs, hherm⟩ := hh
    let : NeZero (Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] σ.asModule)) := ⟨hs.ne'⟩
    exact ⟨hv, Or.inr ⟨_, hrs.symm, rfl, hs, hherm,
      ⟨orthogonalModelOfIsHermitian e hherm⟩⟩⟩
  · exact False.elim (ht hx.2.1 hx.2.2.2.1
      (h.psl2_matrix_cubicRatio_le_two_of_odd e hc (by rw [hx.2.1]; decide)))

/-- K.3.1 recognition on the actual matrix layer, with both formerly explicit
premises discharged. The dimension and the marked models follow from the
ambient cubic ratio; neither a degree bound nor recognition is assumed. -/
theorem binary_recognition
    (h : SourceHypotheses ρ L) (e : L ≃* SL(2,K))
    (r : ℕ) (hr : 2 ≤ r) (hc : Nat.card K = 2 ^ r) :
    let σ : Representation (ZMod 2) SL(2,K) V := (ρ.comp L.subtype).comp e.symm.toMonoidHom
    let d := Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] σ.asModule)
    Module.finrank (ZMod 2) V = 2 * r ∧
      ((d = r ∧ Nonempty (NaturalModel (F := K) ρ L)) ∨
      ∃ s : ℕ, r = 2 * s ∧ d = s ∧
        ∃ hs : 0 < s, letI : NeZero s := ⟨hs.ne'⟩
          BinarySmall.IsHermitian σ s ∧ Nonempty (OrthogonalModel s ρ L)) := by
  apply h.binary_recognition_of_degree_and_triple_exclusion e r hr hc
    (h.psl2_degree_window e hr hc)
  intro hr3 ht
  exact False.elim (h.psl2_not_isTriple_of_card_eight e (by simpa [hr3] using hc) ht)

/-- The same recognition retaining identifications of the actual Schur field.
In the natural branch it is the defining field; in the Hermitian branch it is
the Frobenius fixed half-field, whose extension has degree two. -/
theorem binary_recognition_with_fields
    (h : SourceHypotheses ρ L) (e : L ≃* SL(2,K))
    (r : ℕ) (hr : 2 ≤ r) (hc : Nat.card K = 2 ^ r) :
    let σ : Representation (ZMod 2) SL(2,K) V := (ρ.comp L.subtype).comp e.symm.toMonoidHom
    let E := Module.End (ZMod 2)[SL(2,K)] σ.asModule
    let d := Module.finrank (ZMod 2) E
    Module.finrank (ZMod 2) V = 2 * r ∧
      ((d = r ∧ Nonempty (E ≃+* K) ∧ Nonempty (NaturalModel (F := K) ρ L)) ∨
      ∃ s : ℕ, r = 2 * s ∧ d = s ∧
        ∃ hs : 0 < s, letI : NeZero s := ⟨hs.ne'⟩
          Nonempty (E ≃+* OrthogonalFourMinus.FiniteModel.fixedField s) ∧
          BinarySmall.IsHermitian σ s ∧ Nonempty (OrthogonalModel s ρ L)) := by
  let σ : Representation (ZMod 2) SL(2,K) V := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : Representation.IsIrreducible σ :=
    (Representation.irreducible_comp_surjective_iff e.symm.toMonoidHom
      e.symm.surjective (ρ.comp L.subtype)).mpr h.irreducible
  let E := Module.End (ZMod 2)[SL(2,K)] σ.asModule
  let : Fintype E := Fintype.ofFinite E
  obtain ⟨hd, hn | ⟨s, hrs, hds, hs, hh, hm⟩⟩ := h.binary_recognition e r hr hc
  · let : Fintype K := Fintype.ofFinite K
    have hcard : Nat.card E = Nat.card K := by
      rw [← FiniteField.pow_finrank_eq_natCard 2 E, hn.1, hc]
    exact ⟨hd, Or.inl ⟨hn.1, ⟨FiniteField.ringEquivOfCardEq
      (by simpa only [Fintype.card_eq_nat_card] using hcard)⟩, hn.2⟩⟩
  · let : NeZero s := ⟨hs.ne'⟩
    let : Fintype (OrthogonalFourMinus.FiniteModel.fixedField s) := Fintype.ofFinite _
    have hcard : Nat.card E = Nat.card (OrthogonalFourMinus.FiniteModel.fixedField s) := by
      rw [← FiniteField.pow_finrank_eq_natCard 2 E, hds,
        OrthogonalFourMinus.FiniteModel.card_fixedField]
    exact ⟨hd, Or.inr ⟨s, hrs, hds, hs, ⟨FiniteField.ringEquivOfCardEq
      (by simpa only [Fintype.card_eq_nat_card] using hcard)⟩, hh, hm⟩⟩

/-- K.3.1 from the source central quotient. The covering theorem first
identifies the actual layer, including the exceptional parameter four; the
ambient cubic actor then selects exactly the natural or Hermitian model.
The Schur-field identifications, defining field and Hermitian intertwiner
are part of the conclusion. -/
theorem psl2_module_recognition
    (h : SourceHypotheses ρ L) {r : ℕ} (hr : 2 ≤ r)
    (hq : ClassicalGroup.IsPSL (L ⧸ Subgroup.center L) 2 (2 ^ r)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = 2 ^ r ∧ ∃ e : L ≃* SL(2,K),
      let σ : Representation (ZMod 2) SL(2,K) V := (ρ.comp L.subtype).comp e.symm.toMonoidHom
      let E := Module.End (ZMod 2)[SL(2,K)] σ.asModule
      let d := Module.finrank (ZMod 2) E
      letI : Algebra (ZMod 2) K := ZMod.algebra K 2
      Module.finrank (ZMod 2) V = 2 * r ∧
        ((d = r ∧ Nonempty (E ≃+* K) ∧ Nonempty (NaturalModel (F := K) ρ L)) ∨
        ∃ s : ℕ, r = 2 * s ∧ d = s ∧
          ∃ hs : 0 < s, letI : NeZero s := ⟨hs.ne'⟩
            Nonempty (E ≃+* OrthogonalFourMinus.FiniteModel.fixedField s) ∧
            BinarySmall.IsHermitian σ s ∧ Nonempty (OrthogonalModel s ρ L)) := by
  obtain ⟨K, hK, hfin, hchar, hc, ⟨e⟩⟩ := h.exists_binary_sl2_equiv hr hq
  exact ⟨K, hK, hfin, hchar, hc, e, h.binary_recognition_with_fields e r hr hc⟩

/-- At field order four, both modules have binary dimension four, but the
natural module has Schur degree two and the Hermitian module has Schur degree
one. In particular the half-degree-one orthogonal model is retained. -/
theorem binary_recognition_four
    (h : SourceHypotheses ρ L) (e : L ≃* SL(2,K)) (hc : Nat.card K = 4) :
    let σ : Representation (ZMod 2) SL(2,K) V := (ρ.comp L.subtype).comp e.symm.toMonoidHom
    let d := Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] σ.asModule)
    Module.finrank (ZMod 2) V = 4 ∧
      ((d = 2 ∧ Nonempty (NaturalModel (F := K) ρ L)) ∨
        (d = 1 ∧ BinarySmall.IsHermitian σ 1 ∧ Nonempty (OrthogonalModel 1 ρ L))) := by
  obtain ⟨hd, hn | ⟨s, hrs, hds, hs, hh, hm⟩⟩ :=
    h.binary_recognition e 2 (by decide) (by simpa using hc)
  · exact ⟨hd, Or.inl hn⟩
  · have hs1 : s = 1 := by omega
    exact ⟨hd, Or.inr ⟨hds.trans hs1,
      by simpa only [hs1] using hh, by simpa only [hs1] using hm⟩⟩

end CFSG.Quasithin.ChapterK.RankOne.SourceHypotheses
