module

public import Theory.Character.Generalized
public import Theory.Character.NilpotentBrauerGeneration

/-!
# Recognizing generalized characters by nilpotent restrictions

Brauer induction expresses the principal character as an integer combination
of characters induced from nilpotent subgroups. Multiply this identity by a
conjugacy-invariant function. The projection formula rewrites each term as
induction of a character times the restricted function. Consequently genuine
generalized-character restrictions imply a genuine generalized character on
the ambient group, without a separate numerical integrality assumption.

Source: Brauer's restriction criterion, Serre, *Linear Representations of
Finite Groups*, Chapter 10.
-/

public section
noncomputable section

variable {G : Type*} [Group G] [Fintype G]

/-- Induction preserves differences of actual representation characters. -/
theorem IsGeneralizedCharacter.induced (H : Subgroup G) {f : ClassFunction H}
    (hf : IsGeneralizedCharacter f) : IsGeneralizedCharacter (inducedClassFunction H f) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hf
  refine ⟨_, _, BrauerInduction.inducedClassFunction_isCharacter H ha,
    BrauerInduction.inducedClassFunction_isCharacter H hb, ?_⟩
  exact (inducedClassFunctionIntLinear H).map_sub a b

/-- A class function is a generalized character if all its nilpotent subgroup
restrictions are generalized characters. -/
theorem isGeneralizedCharacter_of_nilpotent_restrictions {f : ClassFunction G}
    (hf : IsClassFunction f)
    (hlocal : ∀ H : Subgroup G, Group.IsNilpotent H →
      IsGeneralizedCharacter (fun x : H => f (x : G))) : IsGeneralizedCharacter f := by
  have hspan (k : ClassFunction G) (hk : k ∈ BrauerInduction.nilpotentInducedSpan G) :
      IsGeneralizedCharacter (k * f) := by
    induction hk using Submodule.span_induction with
    | mem k hk =>
      obtain ⟨H, hH, a, ha, rfl⟩ := hk
      rw [← inducedClassFunction_mul_restrict H a hf]
      exact (ha.mul_generalized (hlocal H hH)).induced H
    | zero => simpa using isGeneralizedCharacter_zero (G := G)
    | add a b ha hb iha ihb => simpa only [add_mul] using iha.add ihb
    | smul n a ha ih => simpa only [smul_mul_assoc] using ih.zsmul n
  simpa using hspan 1 (BrauerInduction.character_mem_nilpotentInducedSpan isCharacter_one)

/-- Brauer's nilpotent restriction criterion, with conjugacy invariance
retained explicitly on the right. -/
theorem isGeneralizedCharacter_iff_nilpotent_restrictions {f : ClassFunction G} :
    IsGeneralizedCharacter f ↔ IsClassFunction f ∧
      ∀ H : Subgroup G, Group.IsNilpotent H →
        IsGeneralizedCharacter (fun x : H => f (x : G)) := by
  constructor
  · intro hf
    exact ⟨hf.isClassFunction, fun H _ => isGeneralizedCharacter_comp_hom H.subtype hf⟩
  · rintro ⟨hf, hlocal⟩
    exact isGeneralizedCharacter_of_nilpotent_restrictions hf hlocal

end
