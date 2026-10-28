module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Models
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Cover
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank
public import Theory.Representation.Quotient

/-!
# The full tensor catalogue on the original K.3.4 component

The central-cover isomorphism and the derived-to-full matrix inclusion put the
component in the domain of the proved absolute symplectic catalogue. We extend
the original component action over its own Schur field, so that no change of
acting group changes the endomorphism field. Character periodicity gives the
Schur degree, repeated support and the exact binary dimension.

This is the catalogue reduction in K.3.4, not the GM04 selection of its two
permitted supports. Source: Aschbacher--Smith, printed pp.451,456--457, and
GLS3, 2.8.6(a), 2.8.8 and Examples 2.8.10(d).
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.Symplectic.Recognition
open Representation Representation.FrobeniusTensor
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary

noncomputable section

variable {F D V : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
  [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) [ρ.IsIrreducible]

/-- The complete periodic tensor data, over the original action's Schur field.
No restriction to the two K.3.4 alternatives is part of this record. -/
structure TensorParameters (d : D ≃* Derived F) (r : ℕ) where
  embedding : F →+* Closure ρ
  support : Finset (Fin (2*r))
  blocks : ℕ
  factors : ℕ
  blocks_pos : 0 < blocks
  factors_pos : 0 < factors
  field_degree : r = Module.finrank (ZMod 2) (Symplectic.SchurField ρ) * blocks
  support_card : support.card = factors * blocks
  periodic : ∀ [NeZero (2*r)], rotateSupport (Module.finrank (ZMod 2) (Symplectic.SchurField ρ)) support = support
  binary_degree : Module.finrank (ZMod 2) V =
    Module.finrank (ZMod 2) (Symplectic.SchurField ρ) * (4^factors)^blocks
  equivalence : Nonempty (Representation.Equiv ((absoluteRep ρ).comp d.symm.toMonoidHom)
    (tensorModel embedding support))

/-- Exhaust the original action by the checked catalogue and derive its exact
Schur period. No ambient degree bound or representation-selection premise is used. -/
theorem exists_tensorParameters (d : D ≃* Derived F) {r : ℕ}
    (hr : 1 < r) (hF : Nat.card F = 2^r) (hρ : Function.Injective ρ) :
    Nonempty (TensorParameters ρ d r) := by
  classical
  let : NeZero (2*r) := ⟨by omega⟩
  let : Algebra (ZMod 2) (Closure ρ) := ZMod.algebra _ _
  let : Module.Finite (ZMod 2) F := Module.Finite.of_finite
  let e : F →+* Closure ρ :=
    (IsAlgClosed.lift (R := ZMod 2) (S := F) (M := Closure ρ)).toRingHom
  let τ := (absoluteRep ρ).comp d.symm.toMonoidHom
  have hτ : IsIrreducible τ :=
    (irreducible_comp_surjective_iff d.symm.toMonoidHom d.symm.surjective _).mpr inferInstance
  let cat := absoluteTensorCatalogue e hF (by omega)
  obtain ⟨S, ⟨φ⟩⟩ := cat.exhaustive (AbsoluteSpace ρ) τ hτ
  let s := Module.finrank (ZMod 2) (Symplectic.SchurField ρ)
  have hχ (g : Derived F) : (absoluteRep ρ).character (d.symm g) =
      (tensorModel e S).character g := congrFun (char_iso φ) g
  have hsr : s ∣ r := (character_pow_iff ρ r).mp (by
    intro g
    have hx := tensorModel_character_field_fixed hF e S (d g)
    rw [← hχ, d.symm_apply_apply] at hx
    exact hx)
  have hperiod : rotateSupport s S = S :=
    rotateSupport_eq_of_character_fixed hF e cat s S (by
      intro g
      rw [← hχ]
      exact (character_pow_iff ρ s).mpr (dvd_refl s) (d.symm g))
  obtain ⟨t, hrt⟩ := hsr
  have ht : 0 < t := by
    by_contra! hz
    have hz' : t = 0 := Nat.eq_zero_of_le_zero hz
    simp only [hz', mul_zero] at hrt
    omega
  obtain ⟨a, ha⟩ := rotateSupport_card_multiple hrt S hperiod
  have hapos : 0 < a := by
    have hpos := Finset.card_pos.mpr (tensorSupport_nonempty τ
      ((absoluteRep_injective ρ hρ).comp d.symm.injective) e S φ)
    rw [ha] at hpos
    exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at hpos)
  refine ⟨⟨e, S, t, a, ht, hapos, hrt, ha, hperiod, ?_, ⟨φ⟩⟩⟩
  rw [binary_finrank_eq ρ, φ.toLinearEquiv.finrank_eq, tensorModel_finrank, ha, pow_mul]

variable {G : Type*} [Group G] [Finite G]
  {ρG : Representation (ZMod 2) G V} {L : Subgroup G}

/-- The marked source component isomorphism, retaining the actual central quotient. -/
def sourceDerivedEquiv {K : GroupClass} (h : SourceHypothesis K ρG L)
    {r : ℕ} (hr : 1 < r) (hF : Nat.card F = 2^r)
    (e : L ⧸ Subgroup.center L ≃* Sp F) : L ≃* Derived F := by
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  let : Theory.GroupTheory.IsQuasisimple L := h.quasisimple
  let : IsIrreducible (ρG.comp L.subtype) := h.irreducible
  exact (coverEquiv (ρG.comp L.subtype)
    (h.faithful.comp Subtype.val_injective) e).trans
      (EvenTwoRank.derivedEquiv hF (by omega)).symm

/-- Application of the full catalogue to the literal K.3.4 component action.
The final selection must use the source's ambient cubic offender separately. -/
theorem source_tensorParameters {K : GroupClass} (h : SourceHypothesis K ρG L)
    {r : ℕ} (hr : 1 < r) (hF : Nat.card F = 2^r)
    (e : L ⧸ Subgroup.center L ≃* Sp F) :
    letI := h.irreducible
    Nonempty (TensorParameters (ρG.comp L.subtype) (sourceDerivedEquiv h hr hF e) r) := by
  let := h.irreducible
  exact exists_tensorParameters (ρG.comp L.subtype) (sourceDerivedEquiv h hr hF e)
    hr hF (h.faithful.comp Subtype.val_injective)

end
end CFSG.Quasithin.ChapterK.Symplectic.Recognition
