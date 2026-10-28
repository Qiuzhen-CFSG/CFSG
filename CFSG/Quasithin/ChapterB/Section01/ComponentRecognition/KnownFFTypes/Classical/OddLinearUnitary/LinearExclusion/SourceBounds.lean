module

public import CFSG.KnownSimple.CarrierCatalogue
public import Theory.Representation.BinaryOffender.CubicConjugateBound
public import Theory.Representation.BinaryOffender.CubicEndField
public import Theory.SpecificGroups.PSL2.OddAutomorphismRank
public import Theory.GroupTheory.Covering
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing

/-!
# Actual-actor bounds for the odd linear branch of K.2

The source input records finite SQTK for the complete known-simple catalogue,
quasisimple F*(G), and a faithful binary action irreducible on that subgroup.
It contains neither a representation classification nor a ratio conclusion.

For a PSL₂ central quotient, faithful conjugation of elementary two-subgroups
and descent of automorphisms through the perfect central cover bound the
two-rank of G by two over a prime field, and by three over a quadratic field.
Consequently cubic ratio at most two supplies an involution of displacement
at most four or six. The degree bound still needs genuine conjugate generators.

Source: Aschbacher--Smith K.2, printed p.453; Guralnick--Malle,
Classification of 2F-modules I, (2.5)--(2.6) and Proposition 4.1.
These bounds do not assert the remaining parameter exclusion.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The actual hypotheses at the beginning of Chapter K, before imposing a ratio bound. -/
structure SourceAction (ρ : Representation (ZMod 2) G V) : Prop where
  sqtk : IsSQTK KnownSimple.IsKnownSimple G
  quasisimple : IsQuasisimple (generalizedFitting G)
  faithful : Function.Injective ρ
  irreducible : IsIrreducible (ρ.comp (generalizedFitting G).subtype)

variable (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)
include h

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- Irreducibility on the actual F* implies irreducibility on G. -/
theorem source_ambient_irreducible : IsIrreducible ρ := by
  let : IsIrreducible (ρ.comp (generalizedFitting G).subtype) := h.irreducible
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial
    (ρ.comp (generalizedFitting G).subtype)
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  let T : Subrepresentation (ρ.comp (generalizedFitting G).subtype) :=
    ⟨S.toSubmodule, fun l _ hv => S.apply_mem_toSubmodule l hv⟩
  rcases eq_bot_or_eq_top T with hT | hT
  · left
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun U : Subrepresentation
      (ρ.comp (generalizedFitting G).subtype) => U.toSubmodule) hT
  · right
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun U : Subrepresentation
      (ρ.comp (generalizedFitting G).subtype) => U.toSubmodule) hT

/-- All scalar-action hypotheses and the literal squared-offender inequality
needed for GM02 hold for the endomorphism field of the original G-action. -/
theorem source_absolute_twoF (hq : cubicRatio ρ ≤ 2) :
    letI : IsIrreducible ρ := source_ambient_irreducible ρ h
    Function.Injective ρ.endFieldRep ∧ IsAbsolutelyIrreducible ρ.endFieldRep ∧
      IsIrreducible (ρ.endFieldRep.comp (generalizedFitting G).subtype) ∧
      ∃ A, IsElementaryTwo A ∧ IsCubic ρ A ∧
        Nat.card ρ.asModule ≤ Nat.card A ^ 2 *
          Nat.card (invariants (ρ.endFieldRep.comp A.subtype)) := by
  let : IsIrreducible ρ := source_ambient_irreducible ρ h
  let : IsIrreducible (ρ.comp (generalizedFitting G).subtype) := h.irreducible
  exact ⟨EndFieldTransfer.faithful ρ h.faithful, endFieldRep_isAbsolutelyIrreducible ρ,
    EndFieldTransfer.restrict_irreducible ρ _, exists_endField_twoF_actor ρ hq⟩

omit [FiniteDimensional (ZMod 2) V] in
/-- Prime-field and quadratic-field actors retain their different rank bounds. -/
theorem source_two_rank_pslTwo {p e : ℕ} (hp : p.Prime) (ho : Odd p)
    (he : e = 1 ∨ e = 2) (hq : 4 ≤ p ^ e)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 (p ^ e)) :
    primeRank 2 G ≤ if e = 1 then 2 else 3 := by
  let : IsQuasisimple (generalizedFitting G) := h.quasisimple
  let : IsIrreducible (ρ.comp (generalizedFitting G).subtype) := h.irreducible
  obtain ⟨F, hF, hfin, hc, ⟨f⟩⟩ := hm
  have hr := primeRank_le_central_quotient_automorphisms_of_irreducible ρ
    (generalizedFitting G) h.faithful f
  rcases he with rfl | rfl
  · simp only [pow_one] at hc hq
    let : Fact p.Prime := ⟨hp⟩
    simpa only [ite_true] using hr.trans
      (Theory.PSL2.prime_card_automorphism_two_rank F hc (by omega))
  · have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
      ⟨p, 2, hp, ho, by decide, hc⟩
    simpa only [show ¬ (2 : ℕ) = 1 by decide, ite_false] using hr.trans
      (Theory.PSL2.odd_automorphism_two_rank F hodd (by omega))

/-- The involution is in the original G and acts by the original representation. -/
theorem source_small_involution_pslTwo {p e : ℕ} (hp : p.Prime) (ho : Odd p)
    (he : e = 1 ∨ e = 2) (hq : 4 ≤ p ^ e)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 (p ^ e))
    (hratio : cubicRatio ρ ≤ 2) :
    ∃ t : G, t ≠ 1 ∧ t ^ 2 = 1 ∧
      fixedCodim ρ (zpowers t) ≤ if e = 1 then 4 else 6 := by
  obtain ⟨t, ht, ht2, hd⟩ := exists_involution_of_cubicRatio_le_nat ρ
    (a := 2) hratio
  have hr := source_two_rank_pslTwo ρ h hp ho he hq hm
  refine ⟨t, ht, ht2, ?_⟩
  split_ifs at hr ⊢ <;> omega

/-- Source application of (2.6), with only the model generation bound outstanding. -/
theorem source_degree_pslTwo_of_conjugates {p e k : ℕ} (hp : p.Prime) (ho : Odd p)
    (he : e = 1 ∨ e = 2) (hq : 4 ≤ p ^ e)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 (p ^ e))
    (hgen : ∀ t : G, t ≠ 1 → t ^ 2 = 1 →
      ∃ g : Fin k → G, generalizedFitting G ≤
        closure (Set.range fun i => g i * t * (g i)⁻¹))
    (hratio : cubicRatio ρ ≤ 2) :
    Module.finrank (ZMod 2) V ≤ k * (if e = 1 then 4 else 6) := by
  let : IsQuasisimple (generalizedFitting G) := h.quasisimple
  let : IsSimpleGroup ((generalizedFitting G) ⧸ center (generalizedFitting G)) :=
    h.quasisimple.simple
  let : Nontrivial (generalizedFitting G) :=
    (QuotientGroup.mk'_surjective (center (generalizedFitting G))).nontrivial
  let : IsIrreducible (ρ.comp (generalizedFitting G).subtype) := h.irreducible
  obtain ⟨t, ht, ht2, hd⟩ := source_small_involution_pslTwo ρ h hp ho he hq hm hratio
  obtain ⟨g, hg⟩ := hgen t ht ht2
  exact (finrank_le_mul_fixedCodim_of_conjugate_generation ρ (generalizedFitting G)
    (fixedSpace_eq_bot_of_faithful_irreducible_restriction ρ _ h.faithful) t g hg).trans
      (Nat.mul_le_mul_left k hd)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion
