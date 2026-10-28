module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows.Basic

/-!
# Ordinary permutation rows in the terminal comparison

In Aₙ, simplicity makes the nontrivial ambient F* the whole group.
In Sₙ, perfectness and normality identify its image with Aₙ. Every
nontrivial normal subgroup contains Aₙ, so the Thompson image is Aₙ or
Sₙ; the quotient above F* has order two. We specialize to n = 6 and 7,
retaining both possibilities for the Thompson image.

These are complete comparisons once an actual ambient permutation
isomorphism has been obtained. No action or covering identification is
assumed. In particular they complete the ordinary halves of F.6.18(7),(9).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
F.6.18, printed pp.309–310; final proof of 15.3.1, printed p.1155.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
namespace ComponentRows

private theorem fitting_nontrivial {D : Type*} [Group D]
    (hL : IsQuasisimple (generalizedFitting D)) : Nontrivial (generalizedFitting D) := by
  let _ := hL.simple
  exact (QuotientGroup.mk'_surjective (center (generalizedFitting D))).nontrivial

private theorem fitting_top_of_simple {D : Type*} [Group D] [Finite D] [IsSimpleGroup D]
    (hL : IsQuasisimple (generalizedFitting D)) : generalizedFitting D = ⊤ := by
  have hn := (nontrivial_iff_ne_bot _).mp (fitting_nontrivial hL)
  exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal (generalizedFitting D)
    inferInstance).resolve_left hn

private theorem fitting_symmetric_image {D : Type*} [Group D] [Finite D]
    (hL : IsQuasisimple (generalizedFitting D)) {n : ℕ} (hn : 5 ≤ n)
    (e : D ≃* Equiv.Perm (Fin n)) :
    (generalizedFitting D).map e.toMonoidHom = alternatingGroup (Fin n) := by
  let _ := hL
  let _ : Nontrivial (generalizedFitting D) := fitting_nontrivial hL
  let N := (generalizedFitting D).map e.toMonoidHom
  let _ : N.Normal := Subgroup.Normal.map inferInstance _ e.surjective
  let _ : Group.IsPerfect N := Group.IsPerfect.map _
  let _ : Nontrivial N := (e.subgroupMap (generalizedFitting D)).injective.nontrivial
  apply le_antisymm
  · rw [← alternatingGroup.commutator_perm_eq (by simpa using hn)]
    change N ≤ ⁅(⊤ : Subgroup (Equiv.Perm (Fin n))), ⊤⁆
    rw [← N.commutator_eq_self]
    exact commutator_mono le_top le_top
  · exact Equiv.Perm.alternatingGroup_le_of_normal (by simpa using hn) inferInstance

private theorem symmetric_normal_cases {n : ℕ} (hn : 5 ≤ n)
    (N : Subgroup (Equiv.Perm (Fin n))) [N.Normal] [Nontrivial N] :
    N = alternatingGroup (Fin n) ∨ N = ⊤ := by
  let _ : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hd := index_dvd_of_le
    (Equiv.Perm.alternatingGroup_le_of_normal (N := N) (by simpa using hn) inferInstance)
  rw [alternatingGroup.index_eq_two] at hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact Or.inr (index_eq_one.mp h)
  · exact Or.inl (Equiv.Perm.eq_alternatingGroup_of_index_eq_two h)

private theorem fitting_symmetric_quotient {D : Type*} [Group D] [Finite D]
    (hL : IsQuasisimple (generalizedFitting D)) {n : ℕ} (hn : 5 ≤ n)
    (e : D ≃* Equiv.Perm (Fin n)) : IsPGroup 2 (D ⧸ generalizedFitting D) := by
  let _ : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hc : Nat.card (D ⧸ generalizedFitting D) = 2 := by
    change (generalizedFitting D).index = 2
    rw [← index_map_of_bijective (f := e.toMonoidHom) e.bijective,
      fitting_symmetric_image hL hn e, alternatingGroup.index_eq_two]
  exact IsPGroup.iff_card.mpr ⟨1, by simpa using hc⟩

end ComponentRows

namespace SourceInput
variable {H : Type*} [Group H] [Finite H] {V : Subgroup H} (d : SourceInput V)
include d

/-- The actual normal Thompson image in an ambient Sₙ is Aₙ or Sₙ. -/
theorem thompson_image_symmetric_cases {n : ℕ} (hn : 5 ≤ n)
    (e : coreQuotient H ≃* Equiv.Perm (Fin n)) :
    Nonempty ((thompsonGroup H).map coreProjection ≃* alternatingGroup (Fin n)) ∨
      Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin n)) := by
  let X := (thompsonGroup H).map (coreProjection (H := H))
  let N := X.map e.toMonoidHom
  let _ : Nontrivial X := (nontrivial_iff_ne_bot _).mpr d.thompson_image_ne_bot
  let _ : N.Normal := Subgroup.Normal.map inferInstance _ e.surjective
  let _ : Nontrivial N := (e.subgroupMap X).injective.nontrivial
  rcases ComponentRows.symmetric_normal_cases hn N with h | h
  · exact Or.inl ⟨(e.subgroupMap X).trans (MulEquiv.subgroupCongr h)⟩
  · exact Or.inr ⟨(e.subgroupMap X).trans ((MulEquiv.subgroupCongr h).trans topEquiv)⟩

/-- Simplicity fills the Thompson image in the actual ambient alternating model. -/
noncomputable def thompsonEquivAlternating {n : ℕ} (hn : 5 ≤ n)
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (e : coreQuotient H ≃* alternatingGroup (Fin n)) :
    (thompsonGroup H).map coreProjection ≃* alternatingGroup (Fin n) := by
  let _ : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  let _ : IsSimpleGroup (coreQuotient H) := e.isSimpleGroup
  exact (MulEquiv.subgroupCongr (d.thompson_image_eq_top_of_fitting_top hL
    (ComponentRows.fitting_top_of_simple hL))).trans (topEquiv.trans e)

omit d in
private theorem alternating_fitting_quotient {n : ℕ} (hn : 5 ≤ n)
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (e : coreQuotient H ≃* alternatingGroup (Fin n)) :
    IsPGroup 2 (coreQuotient H ⧸ generalizedFitting (coreQuotient H)) := by
  let _ : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  let _ : IsSimpleGroup (coreQuotient H) := e.isSimpleGroup
  exact ComponentRows.quotient_of_fitting_top (ComponentRows.fitting_top_of_simple hL)

/-- All three outputs for an actual A₆ ambient quotient. -/
theorem component_row_alternatingSix
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (e : coreQuotient H ≃* alternatingGroup (Fin 6)) :
    NonS3ImageAlternative ((thompsonGroup H).map coreProjection) ∧
      AmbientAlternative (coreQuotient H) ∧
      IsPGroup 2 (coreQuotient H ⧸ generalizedFitting (coreQuotient H)) :=
  ⟨.alternatingSix (d.thompsonEquivAlternating (by decide) hL e), .alternatingSix e,
    alternating_fitting_quotient (by decide) hL e⟩

/-- All three outputs for the ordinary half of F.6.18(7). -/
theorem component_row_alternatingSeven
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (e : coreQuotient H ≃* alternatingGroup (Fin 7)) :
    NonS3ImageAlternative ((thompsonGroup H).map coreProjection) ∧
      AmbientAlternative (coreQuotient H) ∧
      IsPGroup 2 (coreQuotient H ⧸ generalizedFitting (coreQuotient H)) :=
  ⟨.alternatingSeven (d.thompsonEquivAlternating (by decide) hL e), .alternatingSeven e,
    alternating_fitting_quotient (by decide) hL e⟩

/-- All three outputs for an actual S₆ ambient quotient. -/
theorem component_row_symmetricSix
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (e : coreQuotient H ≃* Equiv.Perm (Fin 6)) :
    NonS3ImageAlternative ((thompsonGroup H).map coreProjection) ∧
      AmbientAlternative (coreQuotient H) ∧
      IsPGroup 2 (coreQuotient H ⧸ generalizedFitting (coreQuotient H)) := by
  have hX : NonS3ImageAlternative ((thompsonGroup H).map coreProjection) := by
    rcases d.thompson_image_symmetric_cases (by decide) e with ha | hs
    · obtain ⟨a⟩ := ha
      exact .alternatingSix a
    · obtain ⟨s⟩ := hs
      exact .symmetricSix s
  exact ⟨hX, .symmetricSix e, ComponentRows.fitting_symmetric_quotient hL (by decide) e⟩

/-- All three outputs for the ordinary half of F.6.18(9). -/
theorem component_row_symmetricSeven
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (e : coreQuotient H ≃* Equiv.Perm (Fin 7)) :
    NonS3ImageAlternative ((thompsonGroup H).map coreProjection) ∧
      AmbientAlternative (coreQuotient H) ∧
      IsPGroup 2 (coreQuotient H ⧸ generalizedFitting (coreQuotient H)) := by
  have hX : NonS3ImageAlternative ((thompsonGroup H).map coreProjection) := by
    rcases d.thompson_image_symmetric_cases (by decide) e with ha | hs
    · obtain ⟨a⟩ := ha
      exact .alternatingSeven a
    · obtain ⟨s⟩ := hs
      exact .symmetricSeven s
  exact ⟨hX, .symmetricSeven e, ComponentRows.fitting_symmetric_quotient hL (by decide) e⟩

end SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
