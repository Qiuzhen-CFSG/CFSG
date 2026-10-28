module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.EvenCoverLifting.Descent
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.SpecificGroups.Symplectic.FieldTransport
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Higher symplectic covers: reduction to two-primary kernels

The source requires an isomorphism of the whole component with the literal
central quotient of `Matrix.symplecticGroup (Fin r) F`. A two-group kernel
of the constructed universal projection suffices: universal covering descent
kills its image in the component's trivial two-core. Quasisimplicity of the
projective carrier is inherited from the given simple quotient, so no separate
simplicity or perfectness calculation for the matrix family is needed here.

Entrywise field transport reduces cardinality two to `ZMod 2` and returns the
result to the original field. For rank at least three, excluding `(3,2)` leaves
two independent kernel calculations: nonbinary even fields, and binary rank at
least four. The last three theorems are conditional assembly, with both bounds
explicit. They do not assert that either multiplier calculation is proved.

Source: Aschbacher–Smith, B.1.13, printed pp.73–74; GLS3 §6.1,
Theorem 6.1.4 and Tables 6.1.2–6.1.3 (`refs/KGroup/GLS3/chapter6.tex`).
The canonical symplectic part is trivial for even q. The binary rank-three
exception has a two-primary exceptional part, but is owned separately.
-/

public section

open Subgroup Theory.GroupTheory PerfectCentralCovering

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical

universe u v
variable {L : Type u} [Group L] [Finite L] [IsQuasisimple L]

omit [Finite L] in
private theorem symplectic_quasisimple_of_quotient
    {F : Type v} [Field F] [Finite F] {r : ℕ}
    (e : L ⧸ center L ≃* ClassicalGroup.PSp r F) :
    IsQuasisimple (ClassicalGroup.PSp r F) := by
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup (ClassicalGroup.PSp r F) := e.symm.isSimpleGroup
  exact IsQuasisimple.of_surjective
    (e.toMonoidHom.comp (QuotientGroup.mk' (center L)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _))

/-- Apply the two-primary bound to the constructed universal cover of the
actual projective symplectic model. All model instances come from `e`. -/
theorem nonempty_mulEquiv_of_symplectic_universal_two_kernel
    (hcore : pCore 2 L = ⊥) {F : Type v} [Field F] [Finite F] {r : ℕ}
    (e : L ⧸ center L ≃* ClassicalGroup.PSp r F)
    (hk : IsPGroup 2 (universalProjection (ClassicalGroup.PSp r F)).ker) :
    Nonempty (L ≃* ClassicalGroup.PSp r F) := by
  let : IsQuasisimple (ClassicalGroup.PSp r F) := symplectic_quasisimple_of_quotient e
  exact nonempty_mulEquiv_of_universal_two_kernel hcore
    (universalQuasisimpleCover (ClassicalGroup.PSp r F))
    (universalQuasisimpleCover_isUniversal (ClassicalGroup.PSp r F)) hk e

/-- A bound over `ZMod 2` suffices for the same literal projective group over
every field of cardinality two; the output retains that original field. -/
theorem nonempty_mulEquiv_of_binary_symplectic_universal_two_kernel
    (hcore : pCore 2 L = ⊥) {F : Type v} [Field F] [Finite F] {r : ℕ}
    (hF : Nat.card F = 2) (e : L ⧸ center L ≃* ClassicalGroup.PSp r F)
    (hk : IsPGroup 2 (universalProjection (ClassicalGroup.PSp r (ZMod 2))).ker) :
    Nonempty (L ≃* ClassicalGroup.PSp r F) := by
  let a : ClassicalGroup.PSp r F ≃* ClassicalGroup.PSp r (ZMod 2) :=
    Theory.SpecificGroups.Symplectic.fieldEquivPSp
      (Theory.SpecificGroups.Symplectic.fieldEquivZModTwo F hF)
  obtain ⟨b⟩ := nonempty_mulEquiv_of_symplectic_universal_two_kernel hcore (e.trans a) hk
  exact ⟨b.trans a.symm⟩

/-- Conditional assembly of the higher-rank source branch. The remaining
inputs are kernel bounds, not whole-group recognition or model simplicity. -/
theorem nonempty_mulEquiv_of_even_higher_symplectic_kernel_bounds
    (hcore : pCore 2 L = ⊥) {r q : ℕ} (hr : 3 ≤ r) (he : Even q)
    (hex : (r, q) ≠ (3, 2))
    (F : Type v) [Field F] [Finite F] (hF : Nat.card F = q)
    (e : L ⧸ center L ≃* ClassicalGroup.PSp r F)
    (hlarge : ∀ [CharP F 2] [Group.IsPerfect (ClassicalGroup.PSp r F)],
      3 ≤ r → 2 < Nat.card F →
        IsPGroup 2 (universalProjection (ClassicalGroup.PSp r F)).ker)
    (hbinary : ∀ [Group.IsPerfect (ClassicalGroup.PSp r (ZMod 2))],
      4 ≤ r → IsPGroup 2 (universalProjection (ClassicalGroup.PSp r (ZMod 2))).ker) :
    Nonempty (L ≃* ClassicalGroup.PSp r F) := by
  by_cases htwo : q = 2
  · have hcard : Nat.card F = 2 := hF.trans htwo
    let a : ClassicalGroup.PSp r F ≃* ClassicalGroup.PSp r (ZMod 2) :=
      Theory.SpecificGroups.Symplectic.fieldEquivPSp
        (Theory.SpecificGroups.Symplectic.fieldEquivZModTwo F hcard)
    let : IsQuasisimple (ClassicalGroup.PSp r (ZMod 2)) :=
      symplectic_quasisimple_of_quotient (e.trans a)
    have hr4 : 4 ≤ r := by
      have hr3 : r ≠ 3 := fun h => hex (Prod.ext h htwo)
      omega
    exact nonempty_mulEquiv_of_binary_symplectic_universal_two_kernel hcore hcard e
      (hbinary hr4)
  · let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := by
      apply ringChar.of_eq
      apply FiniteField.even_card_iff_char_two.mpr
      rw [← Nat.card_eq_fintype_card, hF]
      exact Nat.mod_eq_zero_of_dvd (even_iff_two_dvd.mp he)
    let : IsQuasisimple (ClassicalGroup.PSp r F) := symplectic_quasisimple_of_quotient e
    have hcard : 2 < Nat.card F := by
      have : 1 < Nat.card F := Finite.one_lt_card
      omega
    exact nonempty_mulEquiv_of_symplectic_universal_two_kernel hcore e (hlarge hr hcard)

/-- The `IsPSp` consumer retains the coefficient field selected by its input.
The nonbinary and binary universal-kernel calculations remain explicit. -/
theorem isPSp_of_even_higher_rank_of_kernel_bounds
    (hcore : pCore 2 L = ⊥) {r q : ℕ} (hr : 3 ≤ r) (he : Even q)
    (hex : (r, q) ≠ (3, 2))
    (hlarge : ∀ (F : Type) [Field F] [Finite F] [CharP F 2]
      [Group.IsPerfect (ClassicalGroup.PSp r F)], 3 ≤ r → 2 < Nat.card F →
        IsPGroup 2 (universalProjection (ClassicalGroup.PSp r F)).ker)
    (hbinary : ∀ [Group.IsPerfect (ClassicalGroup.PSp r (ZMod 2))],
      4 ≤ r → IsPGroup 2 (universalProjection (ClassicalGroup.PSp r (ZMod 2))).ker)
    (h : ClassicalGroup.IsPSp (L ⧸ center L) r q) : ClassicalGroup.IsPSp L r q := by
  obtain ⟨F, hfield, hfinite, hcard, ⟨e⟩⟩ := h
  exact ⟨F, hfield, hfinite, hcard,
    nonempty_mulEquiv_of_even_higher_symplectic_kernel_bounds
      hcore hr he hex F hcard e (hlarge F) hbinary⟩

/-- The literal whole-group Lie-type consumer for B.1.13, conditional only on
the two pending model kernel bounds in the stated higher-rank range. -/
theorem isEvenLieGroup_of_even_psp_higher_rank_of_kernel_bounds
    (hcore : pCore 2 L = ⊥) {r q : ℕ} (hr : 3 ≤ r)
    (hp : KnownSimple.SymplecticParameters r q) (he : Even q)
    (hex : (r, q) ≠ (3, 2))
    (hlarge : ∀ (F : Type) [Field F] [Finite F] [CharP F 2]
      [Group.IsPerfect (ClassicalGroup.PSp r F)], 3 ≤ r → 2 < Nat.card F →
        IsPGroup 2 (universalProjection (ClassicalGroup.PSp r F)).ker)
    (hbinary : ∀ [Group.IsPerfect (ClassicalGroup.PSp r (ZMod 2))],
      4 ≤ r → IsPGroup 2 (universalProjection (ClassicalGroup.PSp r (ZMod 2))).ker)
    (h : ClassicalGroup.IsPSp (L ⧸ center L) r q) : IsEvenLieGroup L :=
  .classical (.symplectic r q hp he
    (isPSp_of_even_higher_rank_of_kernel_bounds hcore hr he hex hlarge hbinary h))

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical
