module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Basic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Codimension

/-!
# The conditional numerical sieve for a six-dimensional chief factor

This file isolates the numerical and offender part of the six-dimensional
branch of Aschbacher--Smith 13.8.25 (printed p.961).  The actor, the marked
radical, and the critical pair are kept as explicit source inputs.  In
particular, the subgroup in the denominator is the literal image of `D_H`,
and the quotient is the literal quotient by the chosen maximal submodule.

The final interface is conditional: its `SixFactorInput` includes rank two,
absence of offenders on the maximal submodule, and the strict critical-pair
inclusion. Those are new deductions in 13.8.25, not earlier source inputs.
In particular constructing that record is already a contradiction, so the
record must not be assumed in a source-theorem assembly. The later `Sections`
and `SourceSix` leaves prove the factor-to-submodule transfer and the actual
source index and subgroup consequences; the marked B.3.2(6) calculation and
reversal still have to supply their remaining premises.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), 13.8.22--25, printed pp.957--961.
-/

public section

open Representation Representation.BinaryOffender Subgroup

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

private theorem fixedCodim_cyclic_le_displacement
    (ρ : Representation (ZMod 2) H U) (a : H) (S : Submodule (ZMod 2) U)
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

/- This numerical lemma needs absence of offenders on W. B.3.2(6) applies
to the chief factor; `Sections.no_bestOffender_of_section` supplies that
distinct transfer. The strictness premise is a later critical-pair deduction. -/
theorem six_factor_critical_data
    [Finite H] (ρ : Representation (ZMod 2) H U)
    (W : Subrepresentation ρ) (D S : Submodule (ZMod 2) U)
    (hS : Module.finrank (ZMod 2) S ≤ 1) (A V : Subgroup H)
    (hA : IsElementaryTwo A) (hAV : A ≤ V) (hV : IsElementaryTwo V)
    (hVrank : rank V = 2)
    (hcomm : ∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ S)
    (hdim : Module.finrank (ZMod 2) (U ⧸ D) ≤ rank A)
    (hno : ∀ B ≤ A, ¬ IsBestOffender W.toRepresentation B)
    (hfaith : Function.Injective W.quotientRepresentation)
    (hstrict : A < V) : False := by
  have hSW : S ≤ W.toSubmodule := by
    by_contra hn
    have hS0 : S ≠ ⊥ := fun he => hn (he ▸ bot_le)
    have hpos : 0 < Module.finrank (ZMod 2) S :=
      Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hS0)
    have hAtom : IsAtom S :=
      Submodule.isAtom_iff_finrank_eq_one.mpr (by omega)
    have hi : S ⊓ W.toSubmodule = ⊥ :=
      disjoint_iff.mp (hAtom.not_le_iff_disjoint.mp hn)
    have hfixed : W.toSubmodule ⊓ D ≤ fixedSpace ρ A := by
      intro w hw a
      have hm : ρ a w - w ∈ S ⊓ W.toSubmodule :=
        ⟨hcomm a a.property w hw.2,
          W.toSubmodule.sub_mem (W.apply_mem_toSubmodule a hw.1) hw.1⟩
      rw [hi] at hm
      exact sub_eq_zero.mp hm
    obtain ⟨E, hEA, hbest⟩ :=
      (submodule_offender_sieve ρ W D hA hfixed hdim).1.exists_bestOffender _
    exact hno E hEA hbest
  have hWD : ¬ W.toSubmodule ≤ D := by
    intro hWD
    obtain ⟨a, ha, hne⟩ : ∃ a ∈ A, a ≠ 1 := by
      by_contra! h
      exact hA.1 (eq_bot_iff.mpr h)
    have hcyclic : IsElementaryTwo (zpowers a) :=
      hA.of_le (zpowers_le.mpr ha) (by simpa using hne)
    have hd : Module.finrank (ZMod 2)
        (S.comap W.toSubmodule.subtype) ≤ 1 := by
      rw [(Submodule.comapSubtypeEquivOfLe hSW).finrank_eq]
      exact hS
    have hc := fixedCodim_cyclic_le_displacement W.toRepresentation a
      (S.comap W.toSubmodule.subtype)
      (fun w => hcomm a ha w (hWD w.property))
    have hoff : IsOffender W.toRepresentation (zpowers a) :=
      ⟨hcyclic, hc.trans (hd.trans hcyclic.rank_pos)⟩
    obtain ⟨E, hEA, hbest⟩ := hoff.exists_bestOffender _
    exact hno E ((hEA.trans (zpowers_le.mpr ha))) hbest
  have hstrong : ∃ B ≤ A, IsBestOffender W.quotientRepresentation B ∧
      IsStrongOffender W.quotientRepresentation B := by
    rcases (quotient_offender_sieve ρ W D hA
      (fun a ha d hd => hSW (hcomm a ha d hd)) hdim).2.2 with hs | hs
    · exact hs
    · exact (hWD hs.1).elim
  obtain ⟨B, hBA, hbest, hstrongB⟩ := hstrong
  obtain ⟨he, _, _⟩ := eq_four_group_of_contains_strong_offender
    W.quotientRepresentation hfaith A V hAV hV hVrank
    ⟨B, hBA, hstrongB⟩
  exact hstrict.ne he

/- The numerical form is useful to callers which need the codimension equalities
before applying the strict critical-pair contradiction. -/
theorem six_factor_codimensions
    [Finite H] (ρ : Representation (ZMod 2) H U)
    (W : Subrepresentation ρ) (D S : Submodule (ZMod 2) U)
    (hS : Module.finrank (ZMod 2) S ≤ 1) (A V : Subgroup H)
    (hA : IsElementaryTwo A) (hAV : A ≤ V) (hV : IsElementaryTwo V)
    (hVrank : rank V = 2)
    (hcomm : ∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ S)
    (hdim : Module.finrank (ZMod 2) (U ⧸ D) ≤ rank A)
    (hno : ∀ B ≤ A, ¬ IsBestOffender W.toRepresentation B)
    (hfaith : Function.Injective W.quotientRepresentation) :
    S ≤ W.toSubmodule ∧ ¬ W.toSubmodule ≤ D ∧ A = V ∧ rank A = 2 ∧
      Nat.card A = 4 ∧
      Module.finrank (ZMod 2)
          ((U ⧸ W.toSubmodule) ⧸ D.map W.toSubmodule.mkQ) = 1 ∧
      Module.finrank (ZMod 2) (U ⧸ D) = 2 ∧
      fixedCodim W.quotientRepresentation A = 1 := by
  have hSW : S ≤ W.toSubmodule := by
    by_contra hn
    have hS0 : S ≠ ⊥ := fun he => hn (he ▸ bot_le)
    have hpos : 0 < Module.finrank (ZMod 2) S :=
      Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hS0)
    have hAtom : IsAtom S :=
      Submodule.isAtom_iff_finrank_eq_one.mpr (by omega)
    have hi : S ⊓ W.toSubmodule = ⊥ :=
      disjoint_iff.mp (hAtom.not_le_iff_disjoint.mp hn)
    have hfixed : W.toSubmodule ⊓ D ≤ fixedSpace ρ A := by
      intro w hw a
      have hm : ρ a w - w ∈ S ⊓ W.toSubmodule :=
        ⟨hcomm a a.property w hw.2,
          W.toSubmodule.sub_mem (W.apply_mem_toSubmodule a hw.1) hw.1⟩
      rw [hi] at hm
      exact sub_eq_zero.mp hm
    obtain ⟨E, hEA, hbest⟩ :=
      (submodule_offender_sieve ρ W D hA hfixed hdim).1.exists_bestOffender _
    exact hno E hEA hbest
  have hWD : ¬ W.toSubmodule ≤ D := by
    intro hWD
    obtain ⟨a, ha, hne⟩ : ∃ a ∈ A, a ≠ 1 := by
      by_contra! h
      exact hA.1 (eq_bot_iff.mpr h)
    have hcyclic : IsElementaryTwo (zpowers a) :=
      hA.of_le (zpowers_le.mpr ha) (by simpa using hne)
    have hd : Module.finrank (ZMod 2)
        (S.comap W.toSubmodule.subtype) ≤ 1 := by
      rw [(Submodule.comapSubtypeEquivOfLe hSW).finrank_eq]
      exact hS
    have hc := fixedCodim_cyclic_le_displacement W.toRepresentation a
      (S.comap W.toSubmodule.subtype)
      (fun w => hcomm a ha w (hWD w.property))
    have hoff : IsOffender W.toRepresentation (zpowers a) :=
      ⟨hcyclic, hc.trans (hd.trans hcyclic.rank_pos)⟩
    obtain ⟨E, hEA, hbest⟩ := hoff.exists_bestOffender _
    exact hno E ((hEA.trans (zpowers_le.mpr ha))) hbest
  have hstrong : ∃ B ≤ A, IsBestOffender W.quotientRepresentation B ∧
      IsStrongOffender W.quotientRepresentation B := by
    rcases (quotient_offender_sieve ρ W D hA
      (fun a ha d hd => hSW (hcomm a ha d hd)) hdim).2.2 with hs | hs
    · exact hs
    · exact (hWD hs.1).elim
  obtain ⟨hAeq, hArank, hAcard⟩ := eq_four_group_of_contains_strong_offender
    W.quotientRepresentation hfaith A V hAV hV hVrank
    ⟨hstrong.choose, hstrong.choose_spec.1, hstrong.choose_spec.2.2⟩
  obtain ⟨hq, hu, hf⟩ := quotient_codimension_one_of_rank_two ρ W D A hfaith
    hA.1 (by simpa only [hArank] using hdim) hWD
    (by
      rintro _ ⟨d, hd, rfl⟩ a
      exact (Submodule.Quotient.eq W.toSubmodule).mpr
        (hSW (hcomm a a.property d hd)))
  exact ⟨hSW, hWD, hAeq, hArank, hAcard, hq, hu, hf⟩

/- A conditional numerical certificate, not an earlier source setup.
Its strictness and rank/offender premises must be derived in the source
argument; the theorem below shows that this record cannot be inhabited. -/
structure SixFactorInput (ρ : Representation (ZMod 2) H U) where
  W : Subrepresentation ρ
  D : Submodule (ZMod 2) U
  S : Submodule (ZMod 2) U
  hS : Module.finrank (ZMod 2) S ≤ 1
  A : Subgroup H
  V : Subgroup H
  hA : IsElementaryTwo A
  hAV : A ≤ V
  hV : IsElementaryTwo V
  hVrank : rank V = 2
  hcomm : ∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ S
  hdim : Module.finrank (ZMod 2) (U ⧸ D) ≤ rank A
  hno : ∀ B ≤ A, ¬ IsBestOffender W.toRepresentation B
  hfaith : Function.Injective W.quotientRepresentation
  hstrict : A < V

theorem SixFactorInput.false [Finite H]
    {ρ : Representation (ZMod 2) H U} (h : SixFactorInput ρ) : False := by
  exact six_factor_critical_data ρ h.W h.D h.S h.hS h.A h.V h.hA h.hAV h.hV
    h.hVrank h.hcomm h.hdim h.hno h.hfaith h.hstrict

/- A conditional reduction with its historical name preserved. The `hsix`
premise still requires the complete six-dimensional source contradiction;
this theorem by itself does not prove that source exclusion. -/
theorem noncentralChiefFactorsNaturalOrDual_of_source
    (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* BinaryLinear.GL NaturalSpace)
    (hfactor_dim : ∀ A B : Subrepresentation ρ, A ⋖ B →
      ¬ IsCentralSection ρ A B →
      Module.finrank (ZMod 2) (↥B.toSubmodule ⧸ (sectionLower ρ A B).toSubmodule) = 4 ∨
      Module.finrank (ZMod 2) (↥B.toSubmodule ⧸ (sectionLower ρ A B).toSubmodule) = 6)
    (hfour : ∀ A B : Subrepresentation ρ, (hAB : A ⋖ B) →
      (hcentral : ¬ IsCentralSection ρ A B) →
      Module.finrank (ZMod 2) (↥B.toSubmodule ⧸ (sectionLower ρ A B).toSubmodule) = 4 →
      IsNaturalOrDual (sectionRepresentation ρ A B) eH)
    (hsix : ∀ A B : Subrepresentation ρ, (hAB : A ⋖ B) →
      (hcentral : ¬ IsCentralSection ρ A B) →
      Module.finrank (ZMod 2) (↥B.toSubmodule ⧸ (sectionLower ρ A B).toSubmodule) = 6 →
      SixFactorInput ρ) [Finite H] :
    NoncentralChiefFactorsNaturalOrDual ρ eH := by
  intro A B hAB hcentral
  rcases hfactor_dim A B hAB hcentral with h4 | h6
  · exact hfour A B hAB hcentral h4
  · exact ((hsix A B hAB hcentral h6).false).elim

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
