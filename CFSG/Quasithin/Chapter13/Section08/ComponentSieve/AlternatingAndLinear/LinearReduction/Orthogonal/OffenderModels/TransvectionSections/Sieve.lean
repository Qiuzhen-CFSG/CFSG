module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.ModuleSieve
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Local strong-offender exclusions in the transvection branch

The exclusions in 13.8.25 concern best strong offenders contained in the
chosen critical actor. They are not assertions that either section has no
strong offenders. Applying the complete 13.8.22 sieve preserves the position
of the critical line, the containment or supplement, and its actual
commutator. Faithfulness turns the resulting line bound into transvections.
The fixed-critical-subspace case is impossible by the same local exclusion.

The final elementary sign argument applies once transvection geometry has
shown that every nonidentity element of the actor is odd. It does not
assume that the actor already has rank one.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.22–25, printed pp.957–960, especially p.960 (PDF p.977).
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.TransvectionSections
open Representation.BinaryOffender Subgroup

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U] (ρ : Representation (ZMod 2) H U)

private theorem fixedCodim_zpowers_le_displacement (a : H) (S : Submodule (ZMod 2) U)
    (hS : ∀ v, ρ a v - v ∈ S) :
    fixedCodim ρ (zpowers a) ≤ Module.finrank (ZMod 2) S := by
  let f : U →ₗ[ZMod 2] U := ρ a - LinearMap.id
  have hk : f.ker = fixedSpace ρ (zpowers a) := by
    ext v
    have hg : ∀ x : zpowers a, x ∈ zpowers (⟨a, mem_zpowers a⟩ : zpowers a) := by
      intro x
      obtain ⟨n, hn⟩ := mem_zpowers_iff.mp x.property
      exact mem_zpowers_iff.mpr ⟨n, Subtype.ext hn⟩
    rw [show v ∈ fixedSpace ρ (zpowers a) ↔ ρ a v = v from
      Representation.mem_invariants_iff_of_forall_mem_zpowers
        (ρ.comp (zpowers a).subtype) ⟨a, mem_zpowers a⟩ hg v]
    exact sub_eq_zero
  have hr : LinearMap.range f ≤ S := by
    rintro v ⟨u, rfl⟩
    exact hS u
  have hn := f.finrank_range_add_finrank_ker
  have hc := fixedCodim_add_finrank ρ (zpowers a)
  have hs := Submodule.finrank_mono hr
  rw [hk] at hn
  omega

/-- A faithful group with a common displacement line consists of transvections
and the identity. This alone does not assert that the group is cyclic. -/
theorem transvections_of_displacement_line (hρ : Function.Injective ρ)
    (A : Subgroup H) (S : Submodule (ZMod 2) U)
    (hS : Module.finrank (ZMod 2) S ≤ 1)
    (hcomm : subspaceCommutator ρ ⊤ A ≤ S) :
    ∀ a ∈ A, a ≠ 1 → fixedCodim ρ (zpowers a) = 1 := by
  intro a ha hne
  have hl := fixedCodim_zpowers_le_displacement ρ a S (fun v =>
    hcomm (Submodule.subset_span ⟨a, ha, v, Submodule.mem_top, rfl⟩))
  have hp := fixedCodim_pos_of_faithful ρ hρ (by simpa using hne : zpowers a ≠ ⊥)
  omega

/-- The complete local alternative, including a critical line outside the
ambient module. The two surviving branches retain the literal commutators
and the source distinction between containment and supplement. -/
theorem local_transvection_alternatives [Finite H]
    (W : Subrepresentation ρ) (D : Submodule (ZMod 2) U)
    (hW : Function.Injective W.toRepresentation)
    (hQ : Function.Injective W.quotientRepresentation) {A : Subgroup H}
    (hA : IsElementaryTwo A)
    (hcritical : D ≤ fixedSpace ρ A ∨ ∃ S : Submodule (ZMod 2) U,
      IsAtom S ∧ ∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ S)
    (hdim : Module.finrank (ZMod 2) (U ⧸ D) ≤ rank A)
    (hnoW : ¬ ∃ B ≤ A, IsBestOffender W.toRepresentation B ∧
      IsStrongOffender W.toRepresentation B)
    (hnoQ : ¬ ∃ B ≤ A, IsBestOffender W.quotientRepresentation B ∧
      IsStrongOffender W.quotientRepresentation B) :
    ∃ S : Submodule (ZMod 2) U, IsAtom S ∧
      (∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ S) ∧
      ((S ≤ W.toSubmodule ∧ W.toSubmodule ≤ D ∧
        subspaceCommutator ρ W.toSubmodule A = S ∧
        (∃ B ≤ A, IsBestOffender W.quotientRepresentation B) ∧
        (∀ a ∈ A, a ≠ 1 → fixedCodim W.toRepresentation (zpowers a) = 1)) ∨
      (¬ S ≤ W.toSubmodule ∧ W.toSubmodule ⊔ D = ⊤ ∧
        subspaceCommutator W.quotientRepresentation ⊤ A = S.map W.toSubmodule.mkQ ∧
        (∃ B ≤ A, IsBestOffender W.toRepresentation B) ∧
        (∀ a ∈ A, a ≠ 1 → fixedCodim W.quotientRepresentation (zpowers a) = 1))) := by
  obtain ⟨S, hS, hcomm⟩ : ∃ S : Submodule (ZMod 2) U,
      IsAtom S ∧ ∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ S := by
    rcases hcritical with hfixed | hline
    · exact (hnoW (strong_submodule_offender_of_fixed_subspace
        ρ W D hQ hA hfixed hdim)).elim
    · exact hline
  refine ⟨S, hS, hcomm, ?_⟩
  have hSdim : Module.finrank (ZMod 2) S = 1 :=
    Submodule.isAtom_iff_finrank_eq_one.mp hS
  rcases offender_alternatives_of_critical_line ρ W D S hS hW hQ hA hcomm hdim with
      ⟨hSW, _, hb, hs | ⟨hWD, hc⟩⟩ | ⟨hSW, _, hb, hs | ⟨hWD, hc⟩⟩
  · exact (hnoQ hs).elim
  · refine Or.inl ⟨hSW, hWD, hc, hb, ?_⟩
    have hdimS : Module.finrank (ZMod 2) (S.comap W.toSubmodule.subtype) ≤ 1 := by
      have he : (S.comap W.toSubmodule.subtype).map W.toSubmodule.subtype = S := by
        rw [Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right.mpr hSW]
      have hf := W.toSubmodule.finrank_map_subtype_eq (S.comap W.toSubmodule.subtype)
      rw [he, hSdim] at hf
      exact hf.ge
    apply transvections_of_displacement_line W.toRepresentation hW A
      (S.comap W.toSubmodule.subtype) hdimS
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, w, _, rfl⟩
    change ρ a w - w ∈ S
    rw [← hc]
    exact Submodule.subset_span ⟨a, ha, w, w.property, rfl⟩
  · exact (hnoW hs).elim
  · exact Or.inr ⟨hSW, hWD, hc, hb,
      transvections_of_displacement_line W.quotientRepresentation hQ A
        (S.map W.toSubmodule.mkQ)
        ((Submodule.finrank_map_le W.toSubmodule.mkQ S).trans hSdim.le) hc.le⟩

omit [FiniteDimensional (ZMod 2) U] in
/-- If every nonidentity permutation in an elementary actor is odd, sign
embeds the actor in the group of order two. -/
theorem rank_one_of_nonidentity_odd [Finite H] {n : ℕ} (φ : H →* Equiv.Perm (Fin n))
    {A : Subgroup H} (hA : IsElementaryTwo A)
    (hodd : ∀ a ∈ A, a ≠ 1 → (φ a).sign = -1) : rank A = 1 := by
  let f : A →* ℤˣ := Equiv.Perm.sign.comp (φ.comp A.subtype)
  have hf : f.ker = ⊥ := by
    apply eq_bot_iff.mpr
    intro a ha
    apply Subtype.ext
    by_contra hn
    have hs := hodd a a.property hn
    have ha' : (φ a).sign = 1 := ha
    rw [ha'] at hs
    norm_num at hs
  have hc := Nat.card_le_card_of_injective f ((MonoidHom.ker_eq_bot_iff f).mp hf)
  have htwo : Nat.card ℤˣ = 2 := by rw [Nat.card_eq_fintype_card]; decide
  rw [htwo] at hc
  have hl := Nat.log_monotone (b := 2) hc
  have hp := hA.rank_pos
  change rank A ≤ Nat.log 2 2 at hl
  rw [show Nat.log 2 2 = 1 by decide] at hl
  omega

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.TransvectionSections
