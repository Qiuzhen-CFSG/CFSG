module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlacedNormality
public import Theory.SpecificGroups.SporadicTrivialMultipliers.OddPrimary.Janko
public import Theory.SpecificGroups.Rudvalis.Multiplier.OddPrimary

/-!
# Native carriers for the surviving placed binary-three components

For the actual J₄ and Ru central quotients, the existing odd-primary multiplier
bounds make the entire component center a two-group. Its normality and the
original trivial two-core then force the center to vanish. The native
isomorphism is exactly the full-center quotient followed by its supplied
marking, so subsequent placement and action transports retain that map.

The Chapter12 companion applies this to the same component, residual and whole
natural-dual orbit in the original odd-local alternative. This proves the
simplicity step of Aschbacher--Smith 4.4.3, printed p.622; it does not by itself
prove the subsequent inspection of maximal two-locals on pp.622--623.
Source: refs/quasithin.pdf, 4.4.3 and I.1.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlacedNative
variable {K Q : Type*} [Group K] [Finite K] [Group Q]

/-- The full center vanishes in either surviving placed sporadic row. -/
theorem center_eq_bot [Group.IsPerfect K] (hcore : pCore 2 K = ⊥)
    (he : Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∨
      Nonempty ((K ⧸ center K) ≃* Rudvalis.Model)) : center K = ⊥ := by
  have hp : IsPGroup 2 (center K) := by
    rcases he with he | he
    · obtain ⟨e⟩ := he
      exact Janko4.OddPrimary.center_isPGroup_of_quotient_equiv e
    · obtain ⟨e⟩ := he
      exact Rudvalis.Multiplier.center_isPGroup_of_quotient_equiv e
  have hc : center K ≤ pCore 2 K := le_sSup ⟨inferInstance,hp⟩
  exact le_bot_iff.mp (hc.trans_eq hcore)

/-- The native equivalence is the original full-center quotient map followed
by its original marking. -/
@[expose] def nativeEquiv (hz : center K = ⊥) (e : (K ⧸ center K) ≃* Q) : K ≃* Q :=
  MulEquiv.ofBijective (e.toMonoidHom.comp (QuotientGroup.mk' (center K)))
    ⟨e.injective.comp ((QuotientGroup.mk' (center K)).ker_eq_bot_iff.mp
      (by rw [QuotientGroup.ker_mk',hz])),
      e.surjective.comp (QuotientGroup.mk'_surjective _)⟩

omit [Finite K] in
@[simp] theorem nativeEquiv_apply (hz : center K = ⊥)
    (e : (K ⧸ center K) ≃* Q) (x : K) :
    nativeEquiv hz e x = e (QuotientGroup.mk' (center K) x) := rfl

omit [Finite K] in
/-- Simplicity follows from quasisimplicity and the now-trivial full center. -/
theorem isSimpleGroup [IsQuasisimple K] (hz : center K = ⊥) : IsSimpleGroup K := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  exact (nativeEquiv hz (MulEquiv.refl _)).isSimpleGroup

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlacedNative
