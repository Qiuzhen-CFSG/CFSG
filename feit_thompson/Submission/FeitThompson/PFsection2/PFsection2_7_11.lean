module

public import Submission.FeitThompson.PFsection2.PFsection2_6

/-!
# Peterfalvi, Section 2, Propositions (2.7)-(2.11)

This file exports Peterfalvi Section 2 items (2.7) through (2.11) in a
separate module, reusing the proven helper lemmas from `PFsection2_6`.

No BG result is imported here.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section2

universe u
open Section1 Section2

public theorem CFOn_mono
    {G : Type u} [Group G]
    {L : Subgroup G}
    {A B : Set G}
    {α : Section1.ClassFunction L}
    (hAB : A ⊆ B)
    (hα : CFOn L A α) :
    CFOn L B α := by
  refine ⟨hα.1, ?_⟩
  intro l hlB
  exact hα.2 l (fun hlA => hlB (hAB hlA))

public theorem proposition_2_7 {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) [Finite L] (H : G → Subgroup G)
    (h : Hypothesis2 A L H) (hAL : ∀ a ∈ A, a ∈ L) :
    proposition_2_7_statement A L H h hAL := by
  have hstmt :
      ∀ (α : Section1.ClassFunction L) (χ : Section1.ClassFunction G),
        CFOn L A α →
          Section1.IsClassFunction χ →
            ∀ ψ : Section1.ClassFunction L,
              Section1.IsClassFunction ψ →
                (∀ ⦃a : G⦄, (ha : a ∈ A) →
                  ψ ⟨a, hAL a ha⟩ = dadeAveragingFunction L H χ ⟨a, hAL a ha⟩) →
                  Section1.scalarProduct G (dadeTransform H hAL α) χ =
                    Section1.scalarProduct L α ψ ∧
                  (constantOnDadeCosets A H χ →
                    Section1.scalarProduct G (dadeTransform H hAL α) χ =
                      Section1.scalarProduct L α (Section1.subgroupRestriction L χ)) := by
    intro α χ hα hχclass ψ _hψclass hψ
    constructor
    · calc
        Section1.scalarProduct G (dadeTransform H hAL α) χ =
            Section1.scalarProduct L α (dadeAveragingFunction L H χ) := by
          exact theorem_2_6_inner_product_core A L H h hAL α χ hα hχclass
        _ = Section1.scalarProduct L α ψ := by
          exact scalarProduct_right_congr_on_left_support
            (A := {l : L | (l : G) ∈ A}) (φ := α)
            (ψ := dadeAveragingFunction L H χ) (χ := ψ)
            (by
              intro l hlA
              exact hα.2 l hlA)
            (by
              intro l hlA
              have hsub : (⟨(l : G), hAL (l : G) hlA⟩ : L) = l := by
                ext
                rfl
              simpa [hsub] using (hψ (a := (l : G)) hlA).symm)
    · intro hχ
      exact theorem_2_6_inner_product_restrict_core A L H h hAL α χ hα hχclass hχ
  simpa [proposition_2_7_statement] using hstmt

public theorem dadeTransform_eq_inducedCF_of_coset_constancy_on_support
    {G : Type u} [Group G] [Finite G]
    (A B : Set G) (L : Subgroup G) [Finite L] (H : G → Subgroup G)
    (hBA : B ⊆ A)
    (h : Hypothesis2 A L H) (hAL : ∀ a : G, a ∈ A → a ∈ L)
    (α : Section1.ClassFunction L)
    (hα : CFOn L B α)
    (hconst : ∀ χ : Representation.ClassFunction G,
      Representation.IsIrreducibleCharacter χ →
        ∀ ⦃a h0 : G⦄, a ∈ B → h0 ∈ H a →
          Section1.ofConjClassFunction χ (a * h0) =
            Section1.ofConjClassFunction χ a) :
    dadeTransform H hAL α = Section1.inducedCF L α := by
  classical
  let χfun : Representation.ClassFunction G → Section1.ClassFunction G :=
    fun χ => Section1.ofConjClassFunction χ
  have hαA : CFOn L A α := CFOn_mono hBA hα
  have hDadeclass :
      Section1.IsClassFunction (dadeTransform H hAL α) :=
    dadeTransform_isClassFunction_of_CFOn A L H h hAL α hαA
  have hIndclass : Section1.IsClassFunction (Section1.inducedCF L α) :=
    Section1.inducedCF_isClassFunction L α
  apply Section1.classFunction_eq_of_inner_irreducible
    (phi := dadeTransform H hAL α)
    (psi := Section1.inducedCF L α) hDadeclass hIndclass
  intro chi hchi
  have havg_restrict :
      Section1.scalarProduct L α
          (dadeAveragingFunction L H (χfun chi)) =
        Section1.scalarProduct L α
          (Section1.subgroupRestriction L (χfun chi)) := by
    exact scalarProduct_right_congr_on_left_support
      (A := {l : L | (l : G) ∈ B}) (φ := α)
      (ψ := dadeAveragingFunction L H (χfun chi))
      (χ := Section1.subgroupRestriction L (χfun chi))
      (by
        intro l hlB
        exact hα.2 l hlB)
      (by
        intro l hlB
        letI : Fintype (H (l : G)) := Fintype.ofFinite (H (l : G))
        have hsum :
            (∑ x : H (l : G), χfun chi ((l : G) * (x : G))) =
              (Nat.card (H (l : G)) : ℂ) * χfun chi (l : G) := by
          calc
            (∑ x : H (l : G), χfun chi ((l : G) * (x : G))) =
                ∑ _x : H (l : G), χfun chi (l : G) := by
              refine Finset.sum_congr rfl ?_
              intro x _hx
              exact hconst chi hchi hlB x.property
            _ = (Nat.card (H (l : G)) : ℂ) * χfun chi (l : G) := by
              simp [Finset.card_univ]
        have hcard_ne : (Nat.card (H (l : G)) : ℂ) ≠ 0 := by
          exact_mod_cast (Nat.card_pos (α := H (l : G))).ne'
        have havg :
            dadeAveragingFunction L H (χfun chi) l =
              χfun chi (l : G) := by
          unfold dadeAveragingFunction
          have hmul :
              (Nat.card (H (l : G)) : ℂ)⁻¹ *
                  ∑ x : H (l : G), χfun chi ((l : G) * (x : G)) =
                (Nat.card (H (l : G)) : ℂ)⁻¹ *
                  ((Nat.card (H (l : G)) : ℂ) * χfun chi (l : G)) := by
            exact congrArg (fun z : ℂ =>
              (Nat.card (H (l : G)) : ℂ)⁻¹ * z) hsum
          rw [hmul]
          field_simp [hcard_ne]
        simpa [Section1.subgroupRestriction] using havg)
  calc
    Representation.classFunctionInner
        (Section1.toConjClassFunction
          (dadeTransform H hAL α) hDadeclass) chi
        = Section1.scalarProduct G (dadeTransform H hAL α)
            (χfun chi) := by
            simpa using
              (Section1.representation_inner_toConjClassFunction_right
                (phi := dadeTransform H hAL α)
                (hphi := hDadeclass) chi)
    _ = Section1.scalarProduct L α
        (dadeAveragingFunction L H (χfun chi)) := by
          exact theorem_2_6_inner_product_core
            A L H h hAL α (χfun chi) hαA
            (Section1.ofConjClassFunction_isClassFunction chi)
    _ = Section1.scalarProduct L α
        (Section1.subgroupRestriction L (χfun chi)) := havg_restrict
    _ = Section1.scalarProduct G (Section1.inducedCF L α) (χfun chi) := by
          symm
          exact Section1.scalarProduct_inducedCF_left L α (χfun chi)
            (Section1.ofConjClassFunction_isClassFunction chi)
    _ = Representation.classFunctionInner
        (Section1.toConjClassFunction
          (Section1.inducedCF L α) hIndclass) chi := by
          symm
          simpa using
            (Section1.representation_inner_toConjClassFunction_right
              (phi := Section1.inducedCF L α)
              (hphi := hIndclass) chi)

public theorem dadeTransform_eq_inducedCF_of_trivial_signalizer_on_support
    {G : Type u} [Group G] [Finite G]
    (A B : Set G) (L : Subgroup G) [Finite L] (H : G → Subgroup G)
    (hBA : B ⊆ A)
    (h : Hypothesis2 A L H) (hAL : ∀ a : G, a ∈ A → a ∈ L)
    (α : Section1.ClassFunction L)
    (hα : CFOn L B α)
    (htriv : ∀ ⦃a h0 : G⦄, a ∈ B → h0 ∈ H a → h0 = 1) :
    dadeTransform H hAL α = Section1.inducedCF L α := by
  exact dadeTransform_eq_inducedCF_of_coset_constancy_on_support
    A B L H hBA h hAL α hα
    (by
      intro χ _hχ a h0 ha hh0
      have hh01 : h0 = 1 := htriv ha hh0
      simp [hh01])

public theorem proposition_2_8 {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G) :
    proposition_2_8_statement A L H := by
  have hstmt :
      Hypothesis2 A L H →
        ∀ ⦃B : Set G⦄, B.Nonempty → B ⊆ A →
          IsInternalSemidirectProduct
            (MOfSet H L B) (HInter H B) (normalizerIn L B) := by
    intro h B hB hBA
    exact MOfSet_isInternalSemidirectProduct A L H h hB hBA
  simpa [proposition_2_8_statement] using hstmt

public theorem notation_2_9 {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) [Finite L] (H : G → Subgroup G)
    (h : Hypothesis2 A L H) (α : Section1.ClassFunction L) :
    notation_2_9_statement A L H h α := by
  have hstmt :
      CFOn L A α →
        ∀ ⦃B : Set G⦄, B.Nonempty → B ⊆ A →
          ∃ αB : Section1.ClassFunction (MOfSet H L B),
            alphaBSpec H α B αB ∧
              (Representation.IsVirtualCharacter α →
                Representation.IsVirtualCharacter αB) := by
    intro _hα B hB hBA
    refine ⟨alphaBFromProjection A L H h hB hBA α, ?_⟩
    constructor
    · exact alphaBFromProjection_spec A L H h hB hBA α
    · intro hα
      exact alphaBFromProjection_isVirtualCharacter A L H h hB hBA α hα
  simpa [notation_2_9_statement] using hstmt

public theorem proposition_2_10_1 {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) [Finite L] (H : G → Subgroup G)
    (h : Hypothesis2 A L H) (α : Section1.ClassFunction L) :
    proposition_2_10_1_statement A L H h α := by
  have hstmt :
      CFOn L A α →
        ∀ ⦃B : Set G⦄, B.Nonempty → B ⊆ A →
          ∀ x : L,
            ∀ (αB : Section1.ClassFunction (MOfSet H L B))
              (αBx : Section1.ClassFunction (MOfSet H L (setConjugateBy (x : G) B))),
                alphaBSpec H α B αB →
                  alphaBSpec H α (setConjugateBy (x : G) B) αBx →
                    Section1.inducedCF (MOfSet H L (setConjugateBy (x : G) B)) αBx =
                      Section1.inducedCF (MOfSet H L B) αB := by
    intro hα B hB hBA x αB αBx hαB hαBx
    exact inducedCF_alphaB_setConjugateBy_eq
      (A := A) (L := L) (H := H) (B := B) (h := h) (hα := hα)
      (hB := hB) (hBA := hBA) (x := x) (αB := αB) (αBx := αBx)
      hαB hαBx
  simpa [proposition_2_10_1_statement] using hstmt

public theorem proposition_2_10_2 {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (h : Hypothesis2 A L H) :
    proposition_2_10_2_statement A L H h := by
  have hstmt :
      ∀ ⦃B : Set G⦄, B.Nonempty → B ⊆ A →
        ∀ ⦃a : G⦄, a ∈ A →
          centralizerIn (HInter H B) a = HInter H (B ∪ {a}) := by
    intro B hB hBA a ha
    exact centralizerIn_hInter_eq_hInter_union_singleton
      (A := A) (L := L) (H := H) h hB hBA ha
  simpa [proposition_2_10_2_statement] using hstmt

public theorem proposition_2_10_3 {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) [Finite L] (H : G → Subgroup G)
    (h : Hypothesis2 A L H) (hAL : ∀ a ∈ A, a ∈ L)
    (α : Section1.ClassFunction L) :
    proposition_2_10_3_statement A L H h hAL α := by
  have hstmt :
      CFOn L A α →
        ∀ ⦃B : Set G⦄, B.Nonempty → B ⊆ A →
          ∀ αB : Section1.ClassFunction (MOfSet H L B),
            alphaBSpec H α B αB →
              (∀ g : G, g ∉ dadeSupport A H →
                Section1.inducedCF (MOfSet H L B) αB g = 0) ∧
              (∀ ⦃g a : G⦄, (ha : a ∈ A) → g ∈ conjugateSet (cosetProduct a (H a)) →
                Section1.inducedCF (MOfSet H L B) αB g =
                  dadeInductionFormulaTerm A L H α g a B hAL ha) := by
    intro hα B hB hBA αB hαB
    constructor
    · intro g hg
      exact inducedCF_alphaB_eq_zero_of_not_mem_dadeSupport
        (A := A) (L := L) (H := H) h hB hBA hα.2 hαB hg
    · intro g a ha hgpiece
      exact inducedCF_alphaB_support_piece_formula
        (A := A) (L := L) (H := H) (hAL := hAL)
        h hB hBA hα.1 hα.2 hαB ha hgpiece
  simpa [proposition_2_10_3_statement] using hstmt

public theorem proposition_2_10 {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) [Finite L] (H : G → Subgroup G)
    (h : Hypothesis2 A L H) (hAL : ∀ a ∈ A, a ∈ L) :
    proposition_2_10_statement A L H h hAL := by
  have hstmt :
      ∀ (reps : Finset (Set G))
        (α : Section1.ClassFunction L)
        (αB : (B : Set G) → Section1.ClassFunction (MOfSet H L B)),
          IsRepresentativeSystemForNonemptySubsets A L reps →
            CFOn L A α →
              (∀ B ∈ reps, alphaBSpec H α B (αB B)) →
                dadeTransform H hAL α =
                  dadeInclusionExclusionSum L H reps αB := by
    intro reps α αB hreps hα hαBspec
    classical
    ext g
    by_cases hg : g ∈ dadeSupport A H
    · rcases hg with ⟨a, ha, h₀, hh₀, hconj⟩
      have hgpiece : g ∈ conjugateSet (cosetProduct a (H a)) :=
        dadeSupport_piece_mem_conjugateSet hh₀ hconj
      have hleft :
        dadeTransform H hAL α g =
            α ⟨a, hAL a ha⟩ := by
        exact dadeTransform_eq_on_conjugateSet_cosetProduct
          A L H h hAL α hα.1 ha hgpiece
      have hterm :
          ∀ B ∈ reps,
            Section1.inducedCF (MOfSet H L B) (αB B) g =
              dadeInductionFormulaTerm A L H α g a B hAL ha := by
        intro B hBmem
        have hBprops : B.Nonempty ∧ B ⊆ A := hreps.1 B hBmem
        exact inducedCF_alphaB_support_piece_formula
          (A := A) (L := L) (H := H) (hAL := hAL)
          h hBprops.1 hBprops.2 hα.1 hα.2
          (hαBspec B hBmem) ha hgpiece
      have hsum :
          dadeInclusionExclusionSum L H reps αB g =
            -(reps.sum fun B =>
              ((-1 : ℂ) ^ Nat.card B) *
                dadeInductionFormulaTerm A L H α g a B hAL ha) := by
        unfold dadeInclusionExclusionSum
        congr 1
        refine Finset.sum_congr rfl ?_
        intro B hBmem
        rw [hterm B hBmem]
      have hcancel :
          (reps.sum fun B =>
            ((-1 : ℂ) ^ Nat.card B) *
              dadeInductionFormulaTerm A L H α g a B hAL ha) =
            -(dadeTransform H hAL α g) := by
        rw [hleft]
        exact dadeInductionFormulaTerm_representative_sum_support_cancel
          A L H h hAL hreps α hα ha hgpiece
      calc
        dadeTransform H hAL α g = dadeTransform H hAL α g := rfl
        _ = dadeInclusionExclusionSum L H reps αB g := by
          rw [hsum]
          rw [hcancel]
          ring
    · have hleft : dadeTransform H hAL α g = 0 :=
        dadeTransform_eq_zero_of_not_mem_support H hAL α hg
      have hsum :
          reps.sum (fun B =>
            ((-1 : ℂ) ^ Nat.card B) *
              Section1.inducedCF (MOfSet H L B) (αB B) g) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro B hBmem
        have hBprops : B.Nonempty ∧ B ⊆ A := hreps.1 B hBmem
        have hterm :
            Section1.inducedCF (MOfSet H L B) (αB B) g = 0 :=
          inducedCF_alphaB_eq_zero_of_not_mem_dadeSupport
            (A := A) (L := L) (H := H) h hBprops.1 hBprops.2
            hα.2 (hαBspec B hBmem) hg
        rw [hterm, mul_zero]
      calc
        dadeTransform H hAL α g = 0 := hleft
        _ = dadeInclusionExclusionSum L H reps αB g := by
          rw [dadeInclusionExclusionSum, hsum]
          simp
  simpa [proposition_2_10_statement] using hstmt

public theorem proposition_2_11 {G : Type u} [Group G] [Finite G]
    (A A1 : Set G) (L : Subgroup G) [Finite L] (H : G → Subgroup G) :
    proposition_2_11_statement A A1 L H := by
  have hstmt :
      A1 ⊆ A →
        L ≤ setNormalizer A1 →
          Hypothesis2 A L H →
            Hypothesis2 A1 L H ∧
              ∀ (hAL : ∀ a ∈ A, a ∈ L) (hA1L : ∀ a ∈ A1, a ∈ L),
                ∀ α : Section1.ClassFunction L,
                  CFOn L A1 α →
                    dadeTransform H hAL α = dadeTransform H hA1L α := by
    intro hsub hnorm h
    let hA1 : Hypothesis2 A1 L H := proposition_2_11_hypothesis h hsub hnorm
    refine ⟨hA1, ?_⟩
    intro hAL hA1L α hα
    have hαA : CFOn L A α := by
      refine ⟨hα.1, ?_⟩
      intro l hlA
      exact hα.2 l (by
        intro hlA1
        exact hlA (hsub hlA1))
    ext g
    by_cases hgA1 : g ∈ dadeSupport A1 H
    · rcases hgA1 with ⟨a, ha1, h₀, hh₀, hconj⟩
      have ha : a ∈ A := hsub ha1
      have hleft :
          dadeTransform H hAL α g = α ⟨a, hAL a ha⟩ :=
        ((definition_2_5 A L H h hAL α hαA).1)
          (g := g) (a := a) (h' := h₀) ha hh₀ hconj
      have hright :
          dadeTransform H hA1L α g = α ⟨a, hA1L a ha1⟩ :=
        ((definition_2_5 A1 L H hA1 hA1L α hα).1)
          (g := g) (a := a) (h' := h₀) ha1 hh₀ hconj
      have hsubeq : (⟨a, hAL a ha⟩ : L) = ⟨a, hA1L a ha1⟩ := by
        ext
        rfl
      have hright' :
          dadeTransform H hA1L α g = α ⟨a, hAL a ha⟩ := by
        simpa [← hsubeq] using hright
      exact hleft.trans hright'.symm
    · have hright : dadeTransform H hA1L α g = 0 :=
        (definition_2_5 A1 L H hA1 hA1L α hα).2 g hgA1
      by_cases hgA : g ∈ dadeSupport A H
      · rcases hgA with ⟨a, ha, h₀, hh₀, hconj⟩
        have ha1not : a ∉ A1 := by
          intro ha1
          exact hgA1 ⟨a, ha1, h₀, hh₀, hconj⟩
        have hleft :
            dadeTransform H hAL α g = α ⟨a, hAL a ha⟩ :=
          ((definition_2_5 A L H h hAL α hαA).1)
            (g := g) (a := a) (h' := h₀) ha hh₀ hconj
        have hzero : α ⟨a, hAL a ha⟩ = 0 :=
          hα.2 ⟨a, hAL a ha⟩ ha1not
        rw [hleft, hzero, hright]
      · have hleft : dadeTransform H hAL α g = 0 :=
          (definition_2_5 A L H h hAL α hαA).2 g hgA
        rw [hleft, hright]
  simpa [proposition_2_11_statement] using hstmt

end Section2
