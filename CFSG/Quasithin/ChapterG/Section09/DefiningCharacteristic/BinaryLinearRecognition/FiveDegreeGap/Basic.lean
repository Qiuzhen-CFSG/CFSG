module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.HeckeAction
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Empty
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Multiple.Separated.Extraction
public import Theory.Representation.ZeroHecke.TypeA4Eigenvector

/-!
# Highest vectors and invariant spans for the binary degree gap

Every nonzero finite-dimensional binary SL₅ module has a local highest vector:
apply the type-A₄ zero-Hecke eigenvector theorem to upper-unitriangular invariants.
Faithfulness excludes empty support. For the singleton-support calculation, a
finite family stable under all transvection differences spans an irreducible
module as soon as it contains a nonzero vector.

These are dimension-independent tools for G.9.3(13), Aschbacher--Smith,
combined manuscript (1 March 2004), printed pp.354,356–357/PDF pp.365,367–368.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FiveDegreeGap

open Representation Representation.SL5TenDimensional
open Representation.SL5TenDimensional.Classification
open Representation.SL5TenDimensional.Classification.HeckeAction
open Representation.SL5TenDimensional.Classification.Separated

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Highest vectors exist without a prescribed degree or absolute irreducibility. -/
theorem exists_localHighestVector [FiniteDimensional (ZMod 2) V] [Nontrivial V]
    (ρ : Representation (ZMod 2) Group V) :
    ∃ (J : Finset (Fin 4)) (v : V), v ≠ 0 ∧ LocalHighestVector ρ J v := by
  classical
  let : Nontrivial (upperFixedSubmodule ρ) := upperFixedSubmodule_nontrivial ρ
  have hrelations : ZeroHecke.TypeA4Relations (restrictedOperator ρ) :=
    ⟨restrictedOperator_sq ρ,
      fun i j hij => (restrictedOperator_commute ρ i j (Or.inl hij)).eq,
      restrictedOperator_braid ρ⟩
  obtain ⟨v, hv, heigen⟩ :=
    ZeroHecke.exists_common_zero_or_fixed (restrictedOperator ρ) hrelations
  let J : Finset (Fin 4) := Finset.univ.filter (fun i => restrictedOperator ρ i v = v)
  refine ⟨J, (v : V), fun h => hv (Subtype.ext h), v.property, ?_, ?_⟩
  · intro i hi
    have hnot : restrictedOperator ρ i v ≠ v := by simpa [J] using hi
    exact (restrictedOperator_eq_zero_iff ρ i v).mp ((heigen i).resolve_left hnot)
  · intro i hi
    exact (restrictedOperator_eq_self_iff ρ i v).mp ((Finset.mem_filter.mp hi).2)

/-- In a faithful irreducible module, a nonzero highest vector has nonempty support. -/
theorem support_nonempty [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) Group V} [IsIrreducible ρ]
    (hf : Function.Injective ρ) {J : Finset (Fin 4)} {v : V}
    (hv : v ≠ 0) (h : LocalHighestVector ρ J v) : J.Nonempty := by
  by_contra hn
  have hJ : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  subst J
  have hd := h.finrank_eq_one_of_empty hv
  have he : ρ (simpleUpper 0) = ρ 1 := by
    ext x
    obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' v hv).mp hd x
    simp only [map_smul, h.fixed_of_empty, map_one, Module.End.one_apply]
  have he' := hf he
  exact (by decide : simpleUpper 0 ≠ 1) he'

/-- Stability on a finite spanning family extends from binary transvections
 to the whole group. Irreducibility makes its nonzero span the entire module. -/
theorem span_eq_top_of_root_differences {ι : Type*}
    {ρ : Representation (ZMod 2) Group V} [IsIrreducible ρ]
    (f : ι → V) (k : ι) (hk : f k ≠ 0)
    (ha : ∀ (a b : Fin 5), a ≠ b → ∀ i,
      difference ρ (rootElement a b) (f i) ∈ Submodule.span (ZMod 2) (Set.range f)) :
    Submodule.span (ZMod 2) (Set.range f) = ⊤ := by
  let W := Submodule.span (ZMod 2) (Set.range f)
  have hmem (i : ι) : f i ∈ W := Submodule.subset_span ⟨i, rfl⟩
  let stable (g : Group) : Prop := ∀ x ∈ W, ρ g x ∈ W
  have hone : stable 1 := by intro x hx; simpa using hx
  have hmul (g l : Group) (hg : stable g) (hl : stable l) : stable (g * l) := by
    intro x hx
    rw [map_mul]
    exact hg _ (hl x hx)
  have hroot (a b : Fin 5) (hab : a ≠ b) : stable (rootElement a b) := by
    change W ≤ W.comap (ρ (rootElement a b))
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change ρ (rootElement a b) (f i) ∈ W
    have hh := W.add_mem (ha a b hab i) (hmem i)
    simpa only [difference, LinearMap.sub_apply, LinearMap.id_apply, sub_add_cancel] using hh
  have hall (g : Group) : stable g := by
    apply Matrix.SpecialLinearGroup.diagonal_transvection_induction' stable g
    · intro i j hij c hc
      have hc1 : c = 1 := by
        have : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
        exact this c hc
      subst c
      have hd : Matrix.SpecialLinearGroup.diag2n hij (1 : ZMod 2) hc = 1 := by
        apply Subtype.ext
        simp [Matrix.SpecialLinearGroup.diag2n_coe]
      rw [hd]
      exact hone
    · intro i j hij c
      have hc : c = 0 ∨ c = 1 := by
        have : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
        exact this c
      rcases hc with rfl | rfl
      · simpa only [Matrix.SpecialLinearGroup.transvection_coeff_zero] using hone
      · simpa only [rootElement, dif_pos hij] using hroot i j hij
    · exact hmul
  let S : Subrepresentation ρ := { toSubmodule := W, apply_mem_toSubmodule := hall }
  have hS : S = ⊤ := (eq_bot_or_eq_top S).resolve_left (by
    intro hS
    have : f k ∈ (⊥ : Submodule (ZMod 2) V) := by
      change f k ∈ (⊥ : Subrepresentation ρ)
      rw [← hS]
      exact hmem k
    exact hk (by simpa using this))
  exact congrArg Subrepresentation.toSubmodule hS

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FiveDegreeGap
