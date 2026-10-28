module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification.Action
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Statements
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# The odd extensions cannot be quasisimple two-core quotients

A finite group with trivial two-core has odd-order center. For a
quasisimple source, a surjection onto a nontrivial group maps the source
center onto the target center. Odd-characteristic SL2 has center of order
two, so it cannot be such an image. This excludes both genuine odd-kernel
extension constructors in 11.1.1, with no splitting or exponent assumption.

The actual ComponentGeometry quotient application is provided below and
used by FieldFour. No FF or radical-centralization premise is needed.
Source: Aschbacher--Smith 11.1.1(3), p.761, and 11.4.2, p.777.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification
open Chapter1.Section02.LocalModels
variable {A : Type*} [Group A] [Finite A] [IsQuasisimple A]

omit [IsQuasisimple A] in
private theorem center_odd_of_twoCore_eq_bot (hc : pCore 2 A = ⊥) :
    Odd (Nat.card (center A)) := by
  have hz : center A ≤ fittingSubgroup A := le_sSup ⟨inferInstance,inferInstance⟩
  exact Nat.coprime_two_left.mp ((pPrimeCore_coprime_card (p := 2) (G := A)).of_dvd_right
    (card_dvd_of_le (hz.trans (fitting_le_pPrimeCore_of_pCore_eq_bot 2 hc))))

/-- A quasisimple two-core-free group has no odd-characteristic SL₂
quotient. Its odd center maps onto the quotient center, whereas that center
has order two. No hypothesis on a putative extension kernel is needed. -/
theorem not_surjective_odd_sl2 (hc : pCore 2 A = ⊥)
    {F : Type*} [Field F] [Finite F] (ho : Odd (Nat.card F))
    (f : A →* Matrix.SpecialLinearGroup (Fin 2) F) : ¬ Function.Surjective f := by
  intro hf
  have hcard : Nat.card (center (Matrix.SpecialLinearGroup (Fin 2) F)) = 2 := by
    rw [Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin,
      Nat.gcd_eq_left_iff_dvd]
    rcases ho with ⟨k,hk⟩
    omega
  let : Nontrivial (center (Matrix.SpecialLinearGroup (Fin 2) F)) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; decide)
  let : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) F) :=
    (center (Matrix.SpecialLinearGroup (Fin 2) F)).subtype_injective.nontrivial
  have hm : (center A).map f = center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [← IsQuasisimple.comap_center_of_surjective f hf,
      map_comap_eq_self_of_surjective hf]
  have hd : Nat.card (center (Matrix.SpecialLinearGroup (Fin 2) F)) ∣ Nat.card (center A) := by
    rw [← hm]
    exact (center A).card_map_dvd f
  have hh := (center_odd_of_twoCore_eq_bot hc).of_dvd_nat hd
  rw [hcard] at hh
  norm_num at hh

/-- Both source odd-kernel extensions are impossible in the quasisimple
branch, irrespective of whether the normal kernel splits. -/
theorem not_odd_sl2_extension (hc : pCore 2 A = ⊥)
    (P : GroupClass) {q : ℕ} (ho : Odd q) :
    ¬ HasExtension A P (fun Q _ => Source.IsSL Q 2 q) := by
  rintro ⟨N,_,_,F,_,_,hF,⟨e⟩⟩
  exact not_surjective_odd_sl2 hc (hF.symm ▸ ho)
    (e.toMonoidHom.comp (QuotientGroup.mk' N))
    (e.surjective.comp (QuotientGroup.mk'_surjective N))

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- The literal original quotient excludes both extension constructors in
11.1.1. No FF, radical-centralization or smaller-kernel assumption is used. -/
theorem not_fieldFour_extensions [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)] :
    ¬ HasExtension (E.Kz ⧸ pCore 2 E.Kz)
      (fun P _ => Group.IsNilpotent P ∧ Odd (Nat.card P))
      (fun Q _ => Source.IsSL Q 2 5) ∧
    ∀ p, Source.ExceptionalPrime p →
      ¬ HasExtension (E.Kz ⧸ pCore 2 E.Kz) (ElementaryModel p 2)
        (fun Q _ => Source.IsSL Q 2 p) := by
  refine ⟨not_odd_sl2_extension (pCore_quotient_pCore_eq_bot 2) _ (by decide),?_⟩
  intro p hp
  exact not_odd_sl2_extension (pCore_quotient_pCore_eq_bot 2) _
    (hp.1.odd_of_ne_two (by have := hp.2.1; omega))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification
