module

public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.CoverKernels
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.Initial

/-!
# Consequences of the actual Fitting quotient model

`PrimeSL2FittingQuotient` specifies a genuine isomorphism L/F(L) ≃ SL₂(r),
with r prime and r > 3. Constructing this isomorphism from the source
hypotheses remains a separate obligation. Given it, trivial two-core
identifies F(L) with the odd core and gives a quasisimple Fitting quotient.
The exact prime-field cover input proves [F(L),L] = F(L) and the source's
central-supplement rigidity for every normal N in L.

This is the common interface between construction of the source action
kernel and classification of its individual prime cores. It contains no
core shapes, natural-action equation, or radical-derived assertion.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
A.3.6, printed pp.43–45.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterA.RankActions
namespace CFSG.Quasithin.ChapterA.Section03.NoncentralFitting
universe u

def PrimeSL2FittingQuotient (L : Type u) [Group L] : Prop :=
  ∃ r : ℕ, r.Prime ∧ 3 < r ∧
    Nonempty ((L ⧸ fittingSubgroup L) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod r))

variable {G : Type u} [Group G] [Finite G] {L : Subgroup G}

theorem fitting_eq_oddCore (hL : L.IsCComponent) (hO : pCore 2 G = ⊥)
    (h : PrimeSL2FittingQuotient L) : fittingSubgroup L = pPrimeCore 2 L := by
  obtain ⟨r, hr, hr3, ⟨e⟩⟩ := h
  let : Fact r.Prime := ⟨hr⟩
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (fittingSubgroup L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = fittingSubgroup L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  apply le_antisymm (fitting_le_oddCore hL hO)
  have hi : (pPrimeCore 2 L).map f ≤ pPrimeCore 2 (Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) :=
    le_sSup ⟨Normal.map inferInstance f hf,
      (pPrimeCore_coprime_card (p := 2) (G := L)).of_dvd_right (card_map_dvd _ f)⟩
  have htwo : (2 : ZMod r) ≠ 0 := by
    intro he
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < r)
      ((ZMod.natCast_eq_zero_iff 2 r).mp he)
  rw [Matrix.SpecialLinearGroup.pPrimeCore_two_eq_bot htwo] at hi
  rw [← hk]
  exact (Subgroup.map_eq_bot_iff _).mp (le_bot_iff.mp hi)

omit [Finite G] in
theorem fitting_quotient_quasisimple (h : PrimeSL2FittingQuotient L) :
    IsQuasisimple (L ⧸ fittingSubgroup L) := by
  obtain ⟨r, hr, hr3, ⟨e⟩⟩ := h
  let : Fact r.Prime := ⟨hr⟩
  exact Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv
    (by simpa only [Nat.card_zmod] using hr3) e

theorem fitting_eq_commutator (hrigid : PrimeSL2CoverRigidity.{u})
    (hL : L.IsCComponent) (h : PrimeSL2FittingQuotient L) :
    fittingSubgroup L = ⁅fittingSubgroup L, (⊤ : Subgroup L)⁆ := by
  let : Group.IsPerfect L := hL.perfect
  obtain ⟨r, hr, hr3, ⟨e⟩⟩ := h
  let : Fact r.Prime := ⟨hr⟩
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (fittingSubgroup L))
  have hk : f.ker = fittingSubgroup L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  simpa only [hk] using kernel_eq_commutator hrigid hr3 f
    (e.surjective.comp (QuotientGroup.mk'_surjective _))

theorem fitting_central_supplement (hrigid : PrimeSL2CoverRigidity.{u})
    (hL : L.IsCComponent) (h : PrimeSL2FittingQuotient L)
    (N : Subgroup L) [N.Normal] (hN : fittingSubgroup L = center L ⊔ N) :
    fittingSubgroup L = N := by
  let : Group.IsPerfect L := hL.perfect
  obtain ⟨r, hr, hr3, ⟨e⟩⟩ := h
  let : Fact r.Prime := ⟨hr⟩
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (fittingSubgroup L))
  have hk : f.ker = fittingSubgroup L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  simpa only [hk] using kernel_eq_of_central_supplement hrigid hr3 f
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) N (hk.trans hN)


end CFSG.Quasithin.ChapterA.Section03.NoncentralFitting
