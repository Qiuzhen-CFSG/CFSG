module

public import Theory.GroupTheory.DihedralEightSections
public import Theory.GroupTheory.SmallSylowObstructions
public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.Janko1.Model.SylowTwo
public import Theory.SpecificGroups.SL2.EvenBorelResidual
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# The elementary-eight models in the dihedral Sylow component branch

The actual J₁ model and PSL₂ over a field of order eight have elementary
Sylow two-subgroups of order eight. A subgroup of an ambient group with
dihedral Sylow of order eight cannot have either model as a quotient. The
applications below use precisely the original quotient map K → K/Z(K).
No extra central-kernel or ambient two-core premise is needed.

Source: Aschbacher--Smith, F.6.18, printed p.310, rows (5)--(7).
-/

@[expose] public section
noncomputable section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve

variable {G : Type*} [Group G] [Finite G]

/-- The exact central quotient retains the ambient Sylow order bound. -/
theorem central_quotient_sylow_card_le (T : Sylow 2 G) (K : Subgroup G)
    (S : Sylow 2 (K ⧸ center K)) : Nat.card S ≤ Nat.card T :=
  sylow_card_section_le T K (QuotientGroup.mk' (center K))
    (QuotientGroup.mk'_surjective (center K)) S

/-- A normal subgroup whose central quotient already uses the full ambient
two-part cannot admit a nontrivial two-group quotient above it. -/
theorem eq_top_of_central_quotient_sylow_eight (T : Sylow 2 G)
    (hT : Nat.card T = 8) (K : Subgroup G) [K.Normal]
    (hquot : IsPGroup 2 (G ⧸ K)) (S : Sylow 2 (K ⧸ center K))
    (hS : Nat.card S = 8) : K = ⊤ := by
  have h8 : 8 ∣ Nat.card K := by
    rw [← hS]
    exact S.card_subgroup_dvd_card.trans (center K).index_dvd_card
  apply Subgroup.index_eq_one.mp
  obtain ⟨n, hn⟩ := hquot.exists_card_eq
  change K.index = 2 ^ n at hn
  cases n with
  | zero => simpa using hn
  | succ n =>
      exfalso
      apply not_sixteen_dvd_of_sylow_le_eight T hT.le
      have h2 : 2 ∣ K.index := by
        rw [hn]
        exact dvd_pow_self 2 (by omega)
      have hd := Nat.mul_dvd_mul h8 h2
      simpa only [K.card_mul_index] using hd

/-- The original central quotient cannot be J₁ under a dihedral-eight Sylow. -/
theorem not_jankoOne_central_quotient (T : Sylow 2 G)
    (eT : T ≃* DihedralGroup 4) (K : Subgroup G)
    (e : (K ⧸ center K) ≃* Janko1.Model) : False := by
  let P : Sylow 2 Janko1.Model := default
  let : IsElementaryAbelian 2 P := Janko1.SylowTwo.elementary P
  exact not_elementary_eight_sylow_section T eT K
    (e.toMonoidHom.comp (QuotientGroup.mk' (center K)))
    (e.surjective.comp (QuotientGroup.mk'_surjective (center K))) P
    (Janko1.SylowTwo.card P)

/-- The field-independent PSL₂(8) source model is excluded for the literal
central quotient, retaining its specified coefficient field. -/
theorem not_pslTwoEight_central_quotient (T : Sylow 2 G)
    (eT : T ≃* DihedralGroup 4) (K : Subgroup G)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ center K) 2 8) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 3) (by
    change Fintype.card F = 8
    simpa only [Nat.card_eq_fintype_card] using hF)
  let P := Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.standardSylow F
  let a : Multiplicative F ≃* P :=
    (MonoidHom.ofInjective
      (Matrix.ProjectiveSpecialLinearGroup.OddBorel.unipotentHom_injective F)).trans
      (MulEquiv.subgroupCongr
        (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.coe_standardSylow F).symm)
  let : IsElementaryAbelian 2 (Multiplicative F) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Multiplicative.toAdd.injective
      simp [pow_two, CharTwo.add_self_eq_zero]) }
  let : IsElementaryAbelian 2 P :=
    IsElementaryAbelian.of_surjective a.toMonoidHom a.surjective
  have hP : Nat.card P = 8 := by
    rw [← Nat.card_congr a.toEquiv]
    exact hF
  exact not_elementary_eight_sylow_section T eT K
    (e.toMonoidHom.comp (QuotientGroup.mk' (center K)))
    (e.surjective.comp (QuotientGroup.mk'_surjective (center K))) P hP

end CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve
