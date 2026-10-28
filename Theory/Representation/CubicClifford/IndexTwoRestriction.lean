module

public import Theory.Representation.CubicClifford.Inertia.TwoCosets

/-!
# Simple constituents at index two

The actual conjugate subrepresentation and its sum with a simple constituent exhaust the ambient simple module. Either the constituent is the whole restriction or the two summands are disjoint and the existing product equivalence gives the decomposition. Simplicity of the normal subgroup makes each constituent faithful.

Source: Isaacs, Character Theory of Finite Groups, Theorem 6.5; application to Aschbacher–Smith 13.8.24, printed pp.958–959.
-/

public section

open scoped MonoidAlgebra

namespace Representation.CubicClifford.Inertia

variable {F H V : Type*} [Field F] [Group H] [Finite H]
  [AddCommGroup V] [Module F V]

omit [Finite H] in
private theorem inner_stable (ρ : Representation F H V) (K : Subgroup H) [K.Normal]
    (A : Subrepresentation (ρ.comp K.subtype)) (x : K) :
    conjugateSubrepresentationOrderIso ρ K (x : H) A = A := by
  apply Subrepresentation.toSubmodule_injective
  rw [conjugateSubrepresentationOrderIso_toSubmodule]
  apply le_antisymm
  · rintro v ⟨w, hw, rfl⟩
    exact A.apply_mem_toSubmodule x hw
  · intro v hv
    refine ⟨ρ (x : H)⁻¹ v, A.apply_mem_toSubmodule x⁻¹ hv, ?_⟩
    simp

/-- An index-two restriction is irreducible or is the actual sum of a simple
constituent and its conjugate. The product keeps the literal conjugation map. -/
theorem restriction_dichotomy (ρ : Representation F H V) [IsIrreducible ρ]
    (K : Subgroup H) [K.Normal] (hindex : K.index = 2) (g : H) (hg : g ∉ K)
    (A : Subrepresentation (ρ.comp K.subtype)) (hA : IsIrreducible A.toRepresentation) :
    IsIrreducible (ρ.comp K.subtype) ∨
      (Disjoint A.toSubmodule (Submodule.map (ρ g⁻¹) A.toSubmodule) ∧
        Nonempty (Representation.Equiv (ρ.comp K.subtype)
          (Representation.prod A.toRepresentation (conjugateRep A.toRepresentation g)))) := by
  let D := conjugateSubrepresentationOrderIso ρ K g⁻¹ A
  have htop : A ⊔ D = ⊤ :=
    pair_sup_top ρ K K hindex g hg A A hA le_rfl (inner_stable ρ K A)
  have hAa := (Subrepresentation.irreducible_iff_isAtom A).mp hA
  have hDa : IsAtom D :=
    ((conjugateSubrepresentationOrderIso ρ K g⁻¹).isAtom_iff A).mpr hAa
  by_cases he : A = D
  · left
    have hAtop : A = ⊤ := by simpa only [← he, sup_idem] using htop
    exact isSimpleOrder_iff_isAtom_top.mpr (hAtop ▸ hAa)
  · right
    have hdisj : Disjoint A D := hAa.disjoint_of_ne hDa he
    have hdisj' : Disjoint A.toSubmodule (Submodule.map (ρ g⁻¹) A.toSubmodule) := by
      rw [← conjugateSubrepresentationOrderIso_toSubmodule ρ K g⁻¹ A]
      apply disjoint_iff.mpr
      exact congrArg Subrepresentation.toSubmodule hdisj.eq_bot
    exact ⟨hdisj', ⟨productEquiv ρ K A g hdisj' htop⟩⟩

omit [Finite H] in
private theorem sup_submodule (ρ : Representation F H V) (A B : Subrepresentation ρ) :
    (A ⊔ B).toSubmodule = A.toSubmodule ⊔ B.toSubmodule := by
  let e : Subrepresentation ρ ≃o Submodule F[H] ρ.asModule :=
    Subrepresentation.subrepresentationSubmoduleOrderIso
  have he := e.map_sup A B
  have he' := congrArg (fun p : Submodule F[H] ρ.asModule => p.restrictScalars F) he
  rw [Submodule.restrictScalars_sup] at he'
  exact he'

/-- Faithfulness on the ambient group makes every simple constituent of a
normal simple subgroup of index two faithful. This supplies the hypothesis
needed by the A₇ module results on the two actual Clifford constituents. -/
theorem constituent_faithful (ρ : Representation F H V) [IsIrreducible ρ]
    (hf : Function.Injective ρ) (K : Subgroup H) [K.Normal] [IsSimpleGroup K]
    (hindex : K.index = 2) (g : H) (hg : g ∉ K)
    (A : Subrepresentation (ρ.comp K.subtype)) (hA : IsIrreducible A.toRepresentation) :
    Function.Injective A.toRepresentation := by
  classical
  rcases (inferInstance : A.toRepresentation.ker.Normal).eq_bot_or_eq_top with hk | hk
  · exact (MonoidHom.ker_eq_bot_iff _).mp hk
  have hfix (k : K) (v : V) (hv : v ∈ A.toSubmodule) : ρ (k : H) v = v := by
    have hm : k ∈ A.toRepresentation.ker := by rw [hk]; trivial
    have he := LinearMap.congr_fun (MonoidHom.mem_ker.mp hm) (⟨v, hv⟩ : A.toSubmodule)
    exact congrArg Subtype.val he
  let D := conjugateSubrepresentationOrderIso ρ K g⁻¹ A
  have htop : A.toSubmodule ⊔ D.toSubmodule = ⊤ := by
    rw [← sup_submodule]
    have hs := pair_sup_top ρ K K hindex g hg A A hA le_rfl (inner_stable ρ K A)
    change (A ⊔ D).toSubmodule = ⊤
    rw [hs]
    rfl
  have hfixD (k : K) (v : V) (hv : v ∈ D.toSubmodule) : ρ (k : H) v = v := by
    rw [show D.toSubmodule = Submodule.map (ρ g⁻¹) A.toSubmodule from
      conjugateSubrepresentationOrderIso_toSubmodule ρ K g⁻¹ A] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    let k' : K := ⟨g * (k : H) * g⁻¹,
      (inferInstance : K.Normal).conj_mem _ k.property g⟩
    have he : ρ (k : H) (ρ g⁻¹ w) = ρ g⁻¹ (ρ (k' : H) w) := by
      simp only [← Module.End.mul_apply, ← map_mul]
      congr 2
      dsimp [k']
      group
    rw [he, hfix k' w hw]
  have hfixAll (k : K) (v : V) : ρ (k : H) v = v := by
    have hv : v ∈ A.toSubmodule ⊔ D.toSubmodule := by rw [htop]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, hfix k a ha, hfixD k b hb]
  obtain ⟨k, hk⟩ := exists_ne (1 : K)
  apply False.elim
  apply hk
  apply Subtype.ext
  apply hf
  ext v
  simpa only [Subgroup.coe_one, map_one, Module.End.one_apply] using hfixAll k v

end Representation.CubicClifford.Inertia
