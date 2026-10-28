module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.Models
public import Theory.SpecificGroups.LinearHigher.OddKernelLifts
public import Theory.GroupTheory.Covering
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Higher even linear coverings from the elementary presentation

Trivial two-core makes the kernel of the marked map L → PSL an odd
central group. The unique involutory lifts of elementary roots satisfy
all Steinberg relations. Faithfulness of the elementary presentation
then gives a surjection SL → L with central kernel, preserving the
original field and dimension and the prescribed projective marking.

The root-lifting and descent steps are proved here and in the imported
lower modules. The finite-field presentation theorem is still explicit;
these conditional theorems do not assert the completed higher linear
covering calculation. Its source statement has n ≥ 4, even q and the
catalogue parameters; the separately owned (4,2) and (5,2) endpoints
are excluded from this module's final assembly.

Sources: Aschbacher–Smith, B.1.13, printed pp.73–74; GLS3, Section 6.1;
Steinberg, *Lectures on Chevalley Groups*, Theorems 9 and 11, Sections 6–7.
The last source is transcribed in `refs/KGroup/GLS3/Chapter2St1.tex`.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical

universe u
variable {L : Type u} [Group L] [Finite L] [IsQuasisimple L]

/-- The actual SL quotient follows from faithfulness of its elementary
presentation. The field and the projective marking are retained throughout. -/
theorem isCentralQuotient_of_even_linear_matrixMap_injective
    (hcore : pCore 2 L = ⊥) {n : ℕ} (hn : 2 ≤ n)
    (F : Type) [Field F] [Finite F] (he : Even (Nat.card F))
    (hinj : Function.Injective
      (Theory.SpecificGroups.LinearHigher.matrixMap (n := n) (F := F)))
    (e : L ⧸ center L ≃* PSL(n, F)) : IsCentralQuotient L SL(n, F) := by
  let := Fintype.ofFinite F
  have hchar : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr (by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.even_iff.mp he)
  let : CharP F 2 := by rw [← hchar]; infer_instance
  let f : L →* PSL(n, F) := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = center L := by
    change (e.toMonoidHom.comp (QuotientGroup.mk' (center L))).ker = center L
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hcenter : f.ker ≤ center L := hk.le
  have hcop : (Nat.card f.ker).Coprime 2 := by
    rw [hk]
    exact (Nat.prime_two.coprime_iff_not_dvd.mpr
      (PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot hcore (center L) le_rfl)).symm
  obtain ⟨s, hs, _, hcentral⟩ :=
    Theory.SpecificGroups.LinearHigher.exists_covering_of_matrixMap_injective
      f hf hcenter hcop hn hinj
  exact ⟨s.ker, inferInstance, hcentral,
    ⟨(QuotientGroup.quotientKerEquivOfSurjective s hs).symm⟩⟩

/-- Application to the exact even classical catalogue constructor. The only
remaining model premise is the finite-field elementary presentation. -/
theorem isEvenLieGroup_of_even_linear_matrixMap_injective
    (hcore : pCore 2 L = ⊥) {n q : ℕ}
    (hp : KnownSimple.LinearParameters n q) (he : Even q)
    (F : Type) [Field F] [Finite F] (hcard : Nat.card F = q)
    (hinj : Function.Injective
      (Theory.SpecificGroups.LinearHigher.matrixMap (n := n) (F := F)))
    (e : L ⧸ center L ≃* PSL(n, F)) : IsEvenLieGroup L :=
  .classical (.linear n q hp he F hcard
    (isCentralQuotient_of_even_linear_matrixMap_injective hcore hp.2.1 F
      (by simpa only [hcard] using he) hinj e))

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical
