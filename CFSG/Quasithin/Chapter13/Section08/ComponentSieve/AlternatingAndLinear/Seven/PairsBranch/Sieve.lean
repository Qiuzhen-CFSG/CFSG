module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.Terminal

/-!
# Module deductions in the three-pairs branch

For the literal subrepresentation W and quotient of the representation on
Ũ_H, commutator generation implies nontrivial component action on the quotient.
Once the component acts nontrivially on W as well, the monolith condition makes
both sections faithful. We retain both alternatives of 13.8.22 and exclude their
strong-offender cases using explicit B.4 inputs. The remaining one-dimensional
commutator gives a group of transvections on one of the sections. A compatible
B.3 recognition implication then gives rank one by the seven-point sign argument.
The 13.8.23 codimension bound supplies transvections and compatible natural
submodules in both sections, including the actual fixed-vector lifting equality.

The critical line S here represents Ã₁ or its image. It is not V̂₃, whose
source rank is two. The case A₁ ∩ U_H = 1 is included as the fixed-critical-subspace
alternative and is eliminated by its strong offender on W.

This is a conditional part of the three-pairs branch, not the completed 13.8.24.
The pair-stabilizer rank calculation, selection of the natural quotient from all
4/6/8-dimensional alternatives, and the proof that K is nontrivial on W remain
separate obligations. The B.3 recognition and B.4 strong-FF exclusion implications
are explicit inputs; they must be instantiated for the same faithful seven-point
action. No natural submodule of either section or transvection actor is assumed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.22–24, printed pp.957–959, combined manuscript of 1 March 2004.
-/

public section
open Representation.BinaryOffender Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch
variable {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E] (ρ : Representation (ZMod 2) H E)

private theorem fixedCodim_zpowers_le_displacement (a : H) (S : Submodule (ZMod 2) E)
    (hS : ∀ v, ρ a v - v ∈ S) :
    fixedCodim ρ (zpowers a) ≤ Module.finrank (ZMod 2) S := by
  let f : E →ₗ[ZMod 2] E := ρ a - LinearMap.id
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

private theorem transvections_of_displacement_line (hρ : Function.Injective ρ)
    (A : Subgroup H) (S : Submodule (ZMod 2) E)
    (hS : Module.finrank (ZMod 2) S ≤ 1)
    (hcomm : subspaceCommutator ρ ⊤ A ≤ S) :
    ∀ a ∈ A, a ≠ 1 → fixedCodim ρ (zpowers a) = 1 := by
  intro a ha hne
  have hl := fixedCodim_zpowers_le_displacement ρ a S (fun v =>
    hcomm (Submodule.subset_span ⟨a, ha, v, Submodule.mem_top, rfl⟩))
  have hp := fixedCodim_pos_of_faithful ρ hρ (by simpa using hne : zpowers a ≠ ⊥)
  omega

/-- Both source offender alternatives yield a transvection group once their
strong cases have been excluded. The acting group and both sections are literal. -/
theorem transvection_alternative_of_no_strong [Finite H]
    (W : Subrepresentation ρ) (D S : Submodule (ZMod 2) E)
    (hS : IsAtom S) (hW : Function.Injective W.toRepresentation)
    (hQ : Function.Injective W.quotientRepresentation) {A : Subgroup H}
    (hA : IsElementaryTwo A)
    (hcomm : ∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ S)
    (hdim : Module.finrank (ZMod 2) (E ⧸ D) ≤ rank A)
    (hnoW : ¬ IsStrongFFModule W.toRepresentation)
    (hnoQ : ¬ IsStrongFFModule W.quotientRepresentation) :
    (∀ a ∈ A, a ≠ 1 → fixedCodim W.toRepresentation (zpowers a) = 1) ∨
      (∀ a ∈ A, a ≠ 1 → fixedCodim W.quotientRepresentation (zpowers a) = 1) := by
  have hSdim : Module.finrank (ZMod 2) S = 1 :=
    Submodule.isAtom_iff_finrank_eq_one.mp hS
  rcases offender_alternatives_of_critical_line ρ W D S hS hW hQ hA hcomm hdim with
      ⟨hSW, _, _, hs | ⟨_, hc⟩⟩ | ⟨_, _, _, hs | ⟨_, hc⟩⟩
  · obtain ⟨B, _, _, hB⟩ := hs
    exact (hnoQ ⟨B, hB⟩).elim
  · left
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
  · obtain ⟨B, _, _, hB⟩ := hs
    exact (hnoW ⟨B, hB⟩).elim
  · right
    apply transvections_of_displacement_line W.quotientRepresentation hQ A
      (S.map W.toSubmodule.mkQ)
      ((Submodule.finrank_map_le W.toSubmodule.mkQ S).trans hSdim.le)
    exact hc.le

private theorem natural_of_fixedCodim_one
    (φ : H →* Equiv.Perm (Fin 7)) (hρ : Function.Injective ρ)
    (hrecognition : Function.Injective ρ → ∀ a : H, a ≠ 1 → a ^ 2 = 1 →
      fixedCodim ρ (zpowers a) = 1 → HasNaturalSubmodule ρ φ)
    {A : Subgroup H} (hA : IsElementaryTwo A) (hc : fixedCodim ρ A = 1) :
    HasNaturalSubmodule ρ φ := by
  obtain ⟨a, ha, hne⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra! h
    exact hA.1 (eq_bot_iff.mpr h)
  let : IsElementaryAbelian 2 A := hA.2
  apply hrecognition hρ a hne (elemPow_eq_one_of_isElementaryAbelian a ha)
  have hle : fixedSpace ρ A ≤ fixedSpace ρ (zpowers a) :=
    fun v hv b => hv ⟨b, (zpowers_le.mpr ha) b.property⟩
  have hn := Submodule.finrank_mono hle
  have hnA := fixedCodim_add_finrank ρ A
  have hna := fixedCodim_add_finrank ρ (zpowers a)
  have hp := fixedCodim_pos_of_faithful ρ hρ (by simpa using hne : zpowers a ≠ ⊥)
  omega

omit [FiniteDimensional (ZMod 2) E] in
/-- Every proper quotient of a commutator-generated module has nontrivial
component action. Maximality of the proper subrepresentation is unnecessary. -/
theorem nontrivial_on_quotient_of_generated
    (W : Subrepresentation ρ) (K : Subgroup H) (hW : W ≠ ⊤)
    (hgen : subspaceCommutator ρ ⊤ K = ⊤) :
    ∃ k ∈ K, ∃ q : E ⧸ W.toSubmodule, W.quotientRepresentation k q ≠ q := by
  by_contra! h
  apply hW
  apply Subrepresentation.toSubmodule_injective
  change W.toSubmodule = ⊤
  apply top_unique
  rw [← hgen]
  apply Submodule.span_le.mpr
  rintro _ ⟨k, hk, v, _, rfl⟩
  apply (Submodule.Quotient.mk_eq_zero W.toSubmodule).mp
  change W.toSubmodule.mkQ (ρ k v - v) = 0
  rw [map_sub, ← Subrepresentation.quotientRepresentation_mk, h k hk, sub_self]

/-- The module-theoretic final-branch outputs, conditional on nontrivial K-action
on W and the precise B.3/B.4 recognition implications. This derives rank one and
both compatible natural submodules; it does not use the final A₇ exclusion or the
strict pointwise-centralizer conclusion of 13.8.23(4). -/
theorem rank_one_and_natural_sections [Finite H]
    (φ : H →* Equiv.Perm (Fin 7)) (hφ : Function.Injective φ)
    (W : Subrepresentation ρ) (K A : Subgroup H)
    (hK : ∀ N : Subgroup H, N.Normal → N ≠ ⊥ → K ≤ N)
    (hproper : W ≠ ⊤) (hgen : subspaceCommutator ρ ⊤ K = ⊤)
    (hKW : ∃ k ∈ K, ∃ w : W.toSubmodule, W.toRepresentation k w ≠ w)
    (hA : IsElementaryTwo A) (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (D : Submodule (ZMod 2) E)
    (hcritical : D ≤ fixedSpace ρ A ∨ ∃ S : Submodule (ZMod 2) E,
      IsAtom S ∧ ∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ S)
    (hdim : Module.finrank (ZMod 2) (E ⧸ D) ≤ rank A)
    (hnoW : Function.Injective W.toRepresentation → ¬ IsStrongFFModule W.toRepresentation)
    (hnoQ : Function.Injective W.quotientRepresentation →
      ¬ IsStrongFFModule W.quotientRepresentation)
    (hrecW : Function.Injective W.toRepresentation → ∀ a : H, a ≠ 1 → a ^ 2 = 1 →
      fixedCodim W.toRepresentation (zpowers a) = 1 →
      HasNaturalSubmodule W.toRepresentation φ)
    (hrecQ : Function.Injective W.quotientRepresentation → ∀ a : H, a ≠ 1 → a ^ 2 = 1 →
      fixedCodim W.quotientRepresentation (zpowers a) = 1 →
      HasNaturalSubmodule W.quotientRepresentation φ) :
    rank A = 1 ∧ Function.Injective W.toRepresentation ∧
      Function.Injective W.quotientRepresentation ∧
      HasNaturalSubmodule W.toRepresentation φ ∧
      HasNaturalSubmodule W.quotientRepresentation φ ∧
      fixedCodim W.toRepresentation A = 1 ∧ fixedCodim W.quotientRepresentation A = 1 ∧
      fixedCodim ρ A = 2 ∧
      (fixedSpace ρ A).map W.toSubmodule.mkQ = fixedSpace W.quotientRepresentation A := by
  have hKQ := nontrivial_on_quotient_of_generated ρ W K hproper hgen
  have hW := faithful_of_nontrivial_on_monolith W.toRepresentation K hK hKW
  have hQ := faithful_of_nontrivial_on_monolith W.quotientRepresentation K hK hKQ
  obtain ⟨S, hS, hcomm⟩ : ∃ S : Submodule (ZMod 2) E,
      IsAtom S ∧ ∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ S := by
    rcases hcritical with hfixed | hline
    · obtain ⟨B, _, _, hB⟩ :=
        strong_submodule_offender_of_fixed_subspace ρ W D hQ hA hfixed hdim
      exact (hnoW hW ⟨B, hB⟩).elim
    · exact hline
  have ht := transvection_alternative_of_no_strong ρ W D S hS hW hQ hA hcomm hdim
    (hnoW hW) (hnoQ hQ)
  obtain ⟨a, ha, hne⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra! h
    exact hA.1 (eq_bot_iff.mpr h)
  let : IsElementaryAbelian 2 A := hA.2
  have hpow : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a ha
  have hr : rank A = 1 := by
    rcases ht with ht | ht
    · obtain ⟨j, hj, he⟩ := hrecW hW a hne hpow (ht a ha hne)
      exact rank_one_of_transvections W.toRepresentation φ hφ j hj he hA ht
    · obtain ⟨j, hj, he⟩ := hrecQ hQ a hne hpow (ht a ha hne)
      exact rank_one_of_transvections W.quotientRepresentation φ hφ j hj he hA ht
  obtain ⟨_, _, hw, hq, hu, hfix⟩ :=
    rank_one_faithful_sections ρ W K A hK hKW hKQ hA.1 hr hbound
  exact ⟨hr, hW, hQ,
    natural_of_fixedCodim_one W.toRepresentation φ hW hrecW hA hw,
    natural_of_fixedCodim_one W.quotientRepresentation φ hQ hrecQ hA hq,
    hw, hq, hu, hfix⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch
