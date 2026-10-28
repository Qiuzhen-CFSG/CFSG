module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.EvenCoverLifting.Descent
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Orthogonal applications of the universal two-kernel calculation

The source simple quotient supplies quasisimplicity of the actual projective
orthogonal carrier. A two-group kernel of its constructed universal perfect
cover then vanishes in any cover with trivial two-core. This keeps model
simplicity as an inherited fact and asks the separate multiplier calculations
only for their kernel bound, including the exceptional two-part of D₄(2).

These are conditional consumers of the higher plus/minus calculations, not
proofs of those calculations. The ordinary scalar kernel alone is insufficient.
Source: GLS3 §6.1, Tables 6.1.2–6.1.3 and Theorem 6.1.4; Aschbacher–Smith
B.1.13, printed pp.73–74.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.EvenOrthogonal
universe u
variable {L : Type u} [Group L] [Finite L] [IsQuasisimple L]

private theorem charTwo_of_even_card {F : Type} [Field F] [Finite F]
    {q : ℕ} (he : Even q) (hc : Nat.card F = q) : CharP F 2 := by
  let : Fintype F := Fintype.ofFinite F
  apply ringChar.of_eq
  apply FiniteField.even_card_iff_char_two.mpr
  rw [← Nat.card_eq_fintype_card, hc]
  exact Nat.mod_eq_zero_of_dvd (even_iff_two_dvd.mp he)

private theorem lift_model (hcore : pCore 2 L = ⊥)
    (S : Type) [Group S] [Finite S] (e : L ⧸ center L ≃* S)
    (hk : ∀ [IsQuasisimple S],
      IsPGroup 2 (PerfectCentralCovering.universalProjection S).ker) :
    Nonempty (L ≃* S) := by
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup S := e.symm.isSimpleGroup
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  let : IsQuasisimple S := IsQuasisimple.of_surjective f
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  exact nonempty_mulEquiv_of_universal_two_kernel hcore
    (PerfectCentralCovering.universalQuasisimpleCover S)
    (PerfectCentralCovering.universalQuasisimpleCover_isUniversal S) hk e

/-- The higher plus kernel calculation applies to the literal projective
carrier. In particular, a two-group exceptional kernel at D₄(2) is sufficient. -/
theorem lift_plus_of_universal_kernel (hcore : pCore 2 L = ⊥) {r q : ℕ}
    (he : Even q)
    (hk : ∀ (F : Type) [Field F] [Finite F] [CharP F 2]
      [IsQuasisimple (ClassicalOrthogonal.POmegaPlus r F)],
      IsPGroup 2 (PerfectCentralCovering.universalProjection
        (ClassicalOrthogonal.POmegaPlus r F)).ker)
    (h : ClassicalGroup.IsPOmegaPlus (L ⧸ center L) r q) :
    ClassicalGroup.IsPOmegaPlus L r q := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := h
  let : CharP F 2 := charTwo_of_even_card he hc
  exact ⟨F, hF, hfin, hc, lift_model hcore _ e (hk F)⟩

/-- The minus kernel bound also needs only the quasisimplicity inherited from
the source quotient, without a separate model simplicity certificate. -/
theorem lift_minus_of_universal_kernel (hcore : pCore 2 L = ⊥) {r q : ℕ}
    (he : Even q)
    (hk : ∀ (F : Type) [Field F] [Finite F] [CharP F 2]
      [IsQuasisimple (ClassicalGroup.POmegaMinus r F)],
      IsPGroup 2 (PerfectCentralCovering.universalProjection
        (ClassicalGroup.POmegaMinus r F)).ker)
    (h : ClassicalGroup.IsPOmegaMinus (L ⧸ center L) r q) :
    ClassicalGroup.IsPOmegaMinus L r q := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := h
  let : CharP F 2 := charTwo_of_even_card he hc
  exact ⟨F, hF, hfin, hc, lift_model hcore _ e (hk F)⟩

/-- The plus multiplier bound discharges precisely the whole-group model
premise of the original even classical catalogue constructor. -/
theorem evenLie_of_plus_kernel (hcore : pCore 2 L = ⊥) {r q : ℕ}
    (hp : KnownSimple.OrthogonalPlusParameters r q) (he : Even q)
    (hk : ∀ (F : Type) [Field F] [Finite F] [CharP F 2]
      [IsQuasisimple (ClassicalOrthogonal.POmegaPlus r F)],
      IsPGroup 2 (PerfectCentralCovering.universalProjection
        (ClassicalOrthogonal.POmegaPlus r F)).ker)
    (h : ClassicalGroup.IsPOmegaPlus (L ⧸ center L) r q) : IsEvenLieGroup L :=
  .classical (.orthogonalPlus r q hp he (lift_plus_of_universal_kernel hcore he hk h))

/-- The minus multiplier bound supplies the corresponding original catalogue
constructor with its rank and field parameter unchanged. -/
theorem evenLie_of_minus_kernel (hcore : pCore 2 L = ⊥) {r q : ℕ}
    (hp : KnownSimple.OrthogonalMinusParameters r q) (he : Even q)
    (hk : ∀ (F : Type) [Field F] [Finite F] [CharP F 2]
      [IsQuasisimple (ClassicalGroup.POmegaMinus r F)],
      IsPGroup 2 (PerfectCentralCovering.universalProjection
        (ClassicalGroup.POmegaMinus r F)).ker)
    (h : ClassicalGroup.IsPOmegaMinus (L ⧸ center L) r q) : IsEvenLieGroup L :=
  .classical (.orthogonalMinus r q hp he (lift_minus_of_universal_kernel hcore he hk h))

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.EvenOrthogonal
