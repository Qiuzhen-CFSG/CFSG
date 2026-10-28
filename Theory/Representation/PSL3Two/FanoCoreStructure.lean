module

public import Theory.Representation.PSL3Two.IrreducibleCatalogue.SimpleQuotients
public import Theory.Representation.SimpleHeadQuotient
public import Theory.Representation.SimpleHeadQuotient.BinaryCoreObstruction

/-!
# Structure of the binary Fano point and line cores

The odd-degree point permutation module splits into its six-dimensional core
and its constant line. Evaluation and weighted sum identify the literal
line-complement subspace with the natural dual, and its quotient with the
natural module. The line core has the inverse pair of identifications.

Every simple quotient of the point core is natural: the exact sequence gives
two possibilities, and the independently proved vanishing of all maps to the
dual excludes one. Inverse transpose proves the corresponding line statement.
The kernels are then the unique maximal submodules and the unique simple
submodules. This proves their radical, socle and indecomposability assertions
without using the false general kernel-containment claim printed as H.6.4.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.5.1,
H.5.3(1–2,5), and the two cores in H.6.2, printed pp.385–388.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Representation BinaryLinearThree BinaryLinearThree.FanoDecomposition

namespace BinaryLinearThree.FanoCoreStructure

abbrev pointRepresentation : Representation (ZMod 2) Group (BinaryPermutation.Full Point) :=
  (BinaryPermutation.representation Point).comp pointPerm

private theorem augmentation_one :
    BinaryPermutation.augmentation Point (BinaryPermutation.allOne Point) = 1 := by
  rw [BinaryPermutation.augmentation_allOne, Matrix.PSL3Two.Fano.card_point]
  decide

noncomputable def pointSplitLinear : BinaryPermutation.Full Point ≃ₗ[ZMod 2]
    Core × ZMod 2 where
  toFun a := (⟨a - BinaryPermutation.augmentation Point a • BinaryPermutation.allOne Point, by
    change BinaryPermutation.augmentation Point _ = 0
    simp only [map_sub, map_smul, augmentation_one, smul_eq_mul, mul_one, sub_self]⟩, BinaryPermutation.augmentation Point a)
  invFun x := x.1.val + x.2 • BinaryPermutation.allOne Point
  left_inv a := sub_add_cancel _ _
  right_inv x := by
    have hx : BinaryPermutation.augmentation Point x.1.val = 0 := x.1.property
    apply Prod.ext
    · apply Subtype.ext
      simp only [map_add, map_smul, hx, augmentation_one, smul_eq_mul, mul_one, zero_add, add_sub_cancel_right]
    · simp only [map_add, map_smul, hx, augmentation_one, smul_eq_mul, mul_one, zero_add]
  map_add' a b := by
    apply Prod.ext
    · apply Subtype.ext
      simp [add_smul]
      abel
    · exact map_add _ _ _
  map_smul' c a := by
    apply Prod.ext
    · apply Subtype.ext
      simp [smul_sub, smul_smul]
    · exact map_smul _ _ _

noncomputable def pointSplit : pointRepresentation.Equiv
    (U₂.prod (Representation.trivial (ZMod 2) Group (ZMod 2))) :=
  .mk pointSplitLinear (by
    intro g
    apply LinearMap.ext
    intro a
    apply Prod.ext
    · apply Subtype.ext
      change pointRepresentation g a -
          BinaryPermutation.augmentation Point (pointRepresentation g a) •
            BinaryPermutation.allOne Point =
        pointRepresentation g (a - BinaryPermutation.augmentation Point a •
            BinaryPermutation.allOne Point)
      simp [pointRepresentation]
    · exact BinaryPermutation.augmentation_permute Point (pointPerm g) a)

def pointKernel : Subrepresentation U₂ := pointWeightedSum.ker

def lineKernel : Subrepresentation lineCoreRepresentation := lineWeightedSum.ker

noncomputable def pointKernelEquiv : W.dual.Equiv pointKernel.toRepresentation := by
  let f : W.dual.IntertwiningMap pointKernel.toRepresentation :=
    { toLinearMap := pointEvaluation.toLinearMap.codRestrict pointKernel.toSubmodule (by
        intro v
        change pointEvaluation v ∈ LinearMap.ker pointWeightedSum.toLinearMap
        rw [← point_exact]
        exact ⟨v, rfl⟩)
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        exact LinearMap.congr_fun (pointEvaluation.isIntertwining' g) v }
  apply f.ofBijective
  constructor
  · intro v w h
    apply pointEvaluation_injective
    exact congrArg Subtype.val h
  · intro a
    obtain ⟨v, hv⟩ := (show a.val ∈ LinearMap.range pointEvaluation.toLinearMap by
      rw [point_exact]; exact a.property)
    exact ⟨v, Subtype.ext hv⟩

noncomputable def pointQuotientEquiv : pointKernel.quotientRepresentation.Equiv W :=
  .mk (pointWeightedSum.toLinearMap.quotKerEquivOfSurjective pointWeightedSum_surjective)
    (by
      intro g
      apply LinearMap.ext
      intro a
      induction a using Submodule.Quotient.induction_on with
      | _ a => exact LinearMap.congr_fun (pointWeightedSum.isIntertwining' g) a)

noncomputable def lineKernelEquiv : W.Equiv lineKernel.toRepresentation := by
  let f : W.IntertwiningMap lineKernel.toRepresentation :=
    { toLinearMap := lineEvaluation.toLinearMap.codRestrict lineKernel.toSubmodule (by
        intro v
        change lineEvaluation v ∈ LinearMap.ker lineWeightedSum.toLinearMap
        rw [← line_exact]
        exact ⟨v, rfl⟩)
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        exact LinearMap.congr_fun (lineEvaluation.isIntertwining' g) v }
  apply f.ofBijective
  constructor
  · intro v w h
    apply lineEvaluation_injective
    exact congrArg Subtype.val h
  · intro a
    obtain ⟨v, hv⟩ := (show a.val ∈ LinearMap.range lineEvaluation.toLinearMap by
      rw [line_exact]; exact a.property)
    exact ⟨v, Subtype.ext hv⟩

noncomputable def lineQuotientEquiv : lineKernel.quotientRepresentation.Equiv W.dual :=
  .mk (lineWeightedSum.toLinearMap.quotKerEquivOfSurjective lineWeightedSum_surjective)
    (by
      intro g
      apply LinearMap.ext
      intro a
      induction a using Submodule.Quotient.induction_on with
      | _ a => exact LinearMap.congr_fun (lineWeightedSum.isIntertwining' g) a)

/-- The vector supported on the four points outside the given Fano line. -/
def lineComplement (l : Line) : Core := pointEvaluation (lineFunctional l)

@[simp] theorem lineComplement_apply (l : Line) (p : Point) :
    (lineComplement l).val p = if Matrix.PSL3Two.Fano.Incident p l then 0 else 1 := by
  change (pointEvaluation (lineFunctional l)).val p = _
  rw [pointEvaluation_apply]
  by_cases h : Matrix.PSL3Two.Fano.Incident p l
  · simpa only [if_pos h] using (incident_iff p l).mp h
  · rw [if_neg h]
    have hn : lineFunctional l p.val ≠ 0 := fun hz => h ((incident_iff p l).mpr hz)
    have hz : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    exact (hz _).resolve_left hn

/-- The kernel is precisely zero together with the seven line complements,
so this is the literal subspace denoted by W in H.5.3. -/
theorem mem_pointKernel_iff (a : Core) :
    a ∈ pointKernel ↔ a = 0 ∨ ∃ l : Line, lineComplement l = a := by
  constructor
  · intro ha
    have hr : a ∈ LinearMap.range pointEvaluation.toLinearMap := by
      rw [point_exact]
      exact ha
    obtain ⟨φ, rfl⟩ := hr
    by_cases hφ : φ = 0
    · exact Or.inl (by simp [hφ])
    · right
      let e := dotProductEquiv (ZMod 2) (Fin 3)
      have hv : e.symm φ ≠ 0 := by
        intro hv
        apply hφ
        have he := congrArg e hv
        simpa only [LinearEquiv.apply_symm_apply, map_zero] using he
      refine ⟨Matrix.PSL3Two.Fano.duality ⟨e.symm φ, hv⟩, ?_⟩
      change pointEvaluation (e (e.symm φ)) = pointEvaluation φ
      rw [LinearEquiv.apply_symm_apply]
  · rintro (rfl | ⟨l, rfl⟩)
    · exact pointKernel.toSubmodule.zero_mem
    · change lineComplement l ∈ LinearMap.ker pointWeightedSum.toLinearMap
      rw [← point_exact]
      exact ⟨lineFunctional l, rfl⟩

end BinaryLinearThree.FanoCoreStructure

open Representation BinaryLinearThree BinaryLinearThree.FanoDecomposition
namespace BinaryLinearThree.FanoCoreStructure
open SimpleHeadQuotientObstruction

/-- An irreducible quotient of the actual point core is natural. -/
theorem pointCore_simple_quotient
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Representation (ZMod 2) Group M) [IsIrreducible ρ]
    (f : U₂.IntertwiningMap ρ) (hf : Function.Surjective f) : Nonempty (ρ.Equiv W) := by
  let : IsIrreducible W := IrreducibleCatalogue.natural_irreducible
  let : IsIrreducible W.dual := IrreducibleCatalogue.dual_irreducible
  let : Nontrivial M := Subrepresentation.irreducible_module_nontrivial ρ
  have hfn : f ≠ 0 := by
    intro hz
    obtain ⟨m, hm⟩ := exists_ne (0 : M)
    obtain ⟨a, ha⟩ := hf m
    exact hm (ha.symm.trans (by simp [hz]))
  rcases IrreducibleCatalogue.simple_quotient_of_extension
    pointEvaluation pointWeightedSum pointWeightedSum_surjective point_exact f hfn with h | h
  · obtain ⟨e⟩ := h
    exact False.elim (core_to_dual_not_surjective (e.toIntertwiningMap.comp f)
      (e.toLinearEquiv.surjective.comp hf))
  · exact h

/-- Inverse transpose transfers the vanishing on the point core to the line core. -/
theorem lineCore_to_natural_eq_zero (f : lineCoreRepresentation.IntertwiningMap W) : f = 0 := by
  let e := AutomorphismAction.graphNaturalDual
  let F : U₂.IntertwiningMap W.dual := {
    toLinearMap := e.toLinearMap.comp (f.toLinearMap.comp coreDuality.toLinearMap)
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro a
      change e (f (coreDuality (U₂ g a))) = W.dual g (e (f (coreDuality a)))
      have hd : coreDuality (U₂ g a) =
          lineCoreRepresentation (AutomorphismAction.graph g) (coreDuality a) := by
        have he := LinearMap.congr_fun
          (coreDualityEquiv.isIntertwining' (AutomorphismAction.graph g)) a
        change coreDuality (U₂ (AutomorphismAction.graph (AutomorphismAction.graph g)) a) =
          lineCoreRepresentation (AutomorphismAction.graph g) (coreDuality a) at he
        rw [AutomorphismAction.graph_graph] at he
        exact he
      rw [hd, f.isIntertwining]
      exact LinearMap.congr_fun (e.isIntertwining' g) (f (coreDuality a)) }
  have hF := core_to_dual_eq_zero F
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro a
  apply e.toLinearEquiv.injective
  have he := congrArg (fun h : U₂.IntertwiningMap W.dual => h (coreDuality.symm a)) hF
  simpa [F] using he

/-- An irreducible quotient of the actual line core is dual-natural. -/
theorem lineCore_simple_quotient
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Representation (ZMod 2) Group M) [IsIrreducible ρ]
    (f : lineCoreRepresentation.IntertwiningMap ρ) (hf : Function.Surjective f) :
    Nonempty (ρ.Equiv W.dual) := by
  let : IsIrreducible W := IrreducibleCatalogue.natural_irreducible
  let : IsIrreducible W.dual := IrreducibleCatalogue.dual_irreducible
  let : Nontrivial M := Subrepresentation.irreducible_module_nontrivial ρ
  have hfn : f ≠ 0 := by
    intro hz
    obtain ⟨m, hm⟩ := exists_ne (0 : M)
    obtain ⟨a, ha⟩ := hf m
    exact hm (ha.symm.trans (by simp [hz]))
  rcases IrreducibleCatalogue.simple_quotient_of_extension
    lineEvaluation lineWeightedSum lineWeightedSum_surjective line_exact f hfn with h | h
  · obtain ⟨e⟩ := h
    have hz := lineCore_to_natural_eq_zero (e.toIntertwiningMap.comp f)
    have he : f = 0 := by
      apply IntertwiningMap.ext
      apply LinearMap.ext
      intro a
      apply e.toLinearEquiv.injective
      simpa using congrArg (fun h : lineCoreRepresentation.IntertwiningMap W => h a) hz
    exact False.elim (hfn he)
  · exact h

private theorem maximal_eq_kernel_of_quotient_equiv
    {A X B : Type*} [AddCommGroup A] [Module (ZMod 2) A]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup B] [Module (ZMod 2) B]
    {α : Representation (ZMod 2) Group A} {ξ : Representation (ZMod 2) Group X}
    {β : Representation (ZMod 2) Group B} [IsIrreducible α] [IsIrreducible β]
    (i : α.IntertwiningMap ξ) (π : ξ.IntertwiningMap β)
    (hπ : Function.Surjective π)
    (hex : LinearMap.range i.toLinearMap = LinearMap.ker π.toLinearMap)
    (hneq : ¬ Nonempty (β.Equiv α))
    (N : Subrepresentation ξ) (hN : IsCoatom N)
    (e : N.quotientRepresentation.Equiv β) : N = π.ker := by
  let q : ξ.IntertwiningMap N.quotientRepresentation := {
    toLinearMap := N.toSubmodule.mkQ
    isIntertwining' _ := rfl }
  let f := e.toIntertwiningMap.comp (q.comp i)
  have hf : f = 0 := by
    rcases IsIrreducible.bijective_or_eq_zero f with h | h
    · exact False.elim (hneq ⟨(f.ofBijective h).symm⟩)
    · exact h
  have hk : π.ker ≤ N := by
    intro x hx
    obtain ⟨a, rfl⟩ := (show x ∈ LinearMap.range i.toLinearMap by rw [hex]; exact hx)
    apply (Submodule.Quotient.mk_eq_zero _).mp
    apply e.toLinearEquiv.injective
    have hh := congrArg (fun h : α.IntertwiningMap β => h a) hf
    change e (q (i a)) = 0 at hh
    change e (q (i a)) = e 0
    rw [map_zero]
    exact hh
  rcases eq_or_lt_of_le hk with he | hlt
  · exact he.symm
  · exact False.elim (hN.1
      ((SimpleHeadQuotient.isCoatom_ker_of_surjective π hπ).2 N hlt))

/-- The weighted-sum kernel is the unique maximal invariant subspace of the point core. -/
theorem pointKernel_unique_maximal (N : Subrepresentation U₂) (hN : IsCoatom N) :
    N = pointKernel := by
  let : IsIrreducible W := IrreducibleCatalogue.natural_irreducible
  let : IsIrreducible W.dual := IrreducibleCatalogue.dual_irreducible
  let : IsIrreducible N.quotientRepresentation :=
    SimpleHeadQuotient.irreducible_quotient_of_isCoatom N hN
  let q : U₂.IntertwiningMap N.quotientRepresentation := {
    toLinearMap := N.toSubmodule.mkQ
    isIntertwining' _ := rfl }
  obtain ⟨e⟩ := pointCore_simple_quotient N.quotientRepresentation q N.toSubmodule.mkQ_surjective
  exact maximal_eq_kernel_of_quotient_equiv pointEvaluation pointWeightedSum
    pointWeightedSum_surjective point_exact AutomorphismAction.natural_not_equiv_dual N hN e

/-- The weighted-sum kernel is the unique maximal invariant subspace of the line core. -/
theorem lineKernel_unique_maximal (N : Subrepresentation lineCoreRepresentation) (hN : IsCoatom N) :
    N = lineKernel := by
  let : IsIrreducible W := IrreducibleCatalogue.natural_irreducible
  let : IsIrreducible W.dual := IrreducibleCatalogue.dual_irreducible
  let : IsIrreducible N.quotientRepresentation :=
    SimpleHeadQuotient.irreducible_quotient_of_isCoatom N hN
  let q : lineCoreRepresentation.IntertwiningMap N.quotientRepresentation := {
    toLinearMap := N.toSubmodule.mkQ
    isIntertwining' _ := rfl }
  obtain ⟨e⟩ := lineCore_simple_quotient N.quotientRepresentation q N.toSubmodule.mkQ_surjective
  apply maximal_eq_kernel_of_quotient_equiv lineEvaluation lineWeightedSum
    lineWeightedSum_surjective line_exact ?_ N hN e
  rintro ⟨e'⟩
  exact AutomorphismAction.natural_not_equiv_dual ⟨e'.symm⟩

/-- The point core has the source's dual-natural radical. -/
theorem pointKernel_eq_radical :
    pointKernel = sInf {N : Subrepresentation U₂ | IsCoatom N} := by
  let : IsIrreducible W := IrreducibleCatalogue.natural_irreducible
  apply le_antisymm
  · exact le_sInf fun N hN => (pointKernel_unique_maximal N hN).symm.le
  · exact sInf_le (SimpleHeadQuotient.isCoatom_ker_of_surjective
      pointWeightedSum pointWeightedSum_surjective)

/-- The line core has the source's natural radical. -/
theorem lineKernel_eq_radical :
    lineKernel = sInf {N : Subrepresentation lineCoreRepresentation | IsCoatom N} := by
  let : IsIrreducible W.dual := IrreducibleCatalogue.dual_irreducible
  apply le_antisymm
  · exact le_sInf fun N hN => (lineKernel_unique_maximal N hN).symm.le
  · exact sInf_le (SimpleHeadQuotient.isCoatom_ker_of_surjective
      lineWeightedSum lineWeightedSum_surjective)


/-- The natural-dual evaluation submodule in the point core is simple. -/
theorem pointKernel_isAtom : IsAtom pointKernel := by
  apply (Subrepresentation.irreducible_iff_isAtom _).mp
  exact (RepEquiv.ofRepresentationEquiv pointKernelEquiv.symm).irreducible_of_euqiv
    IrreducibleCatalogue.dual_irreducible

/-- The natural evaluation submodule in the line core is simple. -/
theorem lineKernel_isAtom : IsAtom lineKernel := by
  apply (Subrepresentation.irreducible_iff_isAtom _).mp
  exact (RepEquiv.ofRepresentationEquiv lineKernelEquiv.symm).irreducible_of_euqiv
    IrreducibleCatalogue.natural_irreducible

private theorem three_subrepresentations
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
    {ξ : Representation (ZMod 2) Group X}
    (K : Subrepresentation ξ) (hK : IsAtom K)
    (hmax : ∀ N : Subrepresentation ξ, IsCoatom N → N = K)
    (N : Subrepresentation ξ) : N = ⊥ ∨ N = K ∨ N = ⊤ := by
  let : IsCoatomic (Subrepresentation ξ) := SimpleHeadQuotient.subrepresentation_coatomic ξ
  rcases eq_top_or_exists_le_coatom N with h | ⟨P, hP, hNP⟩
  · exact Or.inr (Or.inr h)
  · rw [hmax P hP] at hNP
    rcases eq_or_lt_of_le hNP with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl (hK.2 N h)

/-- The point core has precisely three invariant subspaces. -/
theorem pointCore_subrepresentations (N : Subrepresentation U₂) :
    N = ⊥ ∨ N = pointKernel ∨ N = ⊤ :=
  three_subrepresentations pointKernel pointKernel_isAtom pointKernel_unique_maximal N

/-- The line core has precisely three invariant subspaces. -/
theorem lineCore_subrepresentations (N : Subrepresentation lineCoreRepresentation) :
    N = ⊥ ∨ N = lineKernel ∨ N = ⊤ :=
  three_subrepresentations lineKernel lineKernel_isAtom lineKernel_unique_maximal N

private theorem simple_socle
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    {ξ : Representation (ZMod 2) Group X}
    (K : Subrepresentation ξ) (hK : IsAtom K) (hKt : K ≠ ⊤)
    (hthree : ∀ N : Subrepresentation ξ, N = ⊥ ∨ N = K ∨ N = ⊤) :
    sSup {N : Subrepresentation ξ | IsAtom N} = K := by
  apply le_antisymm
  · apply sSup_le
    intro N hN
    rcases hthree N with h | h | h
    · exact False.elim (hN.1 h)
    · exact h.le
    · subst N
      exact False.elim (hK.1 (hN.2 K (lt_top_iff_ne_top.mpr hKt)))
  · exact le_sSup hK

/-- The literal span of all simple submodules is the dual-natural kernel. -/
theorem pointKernel_eq_socle :
    pointKernel = sSup {N : Subrepresentation U₂ | IsAtom N} := by
  let : IsIrreducible W := IrreducibleCatalogue.natural_irreducible
  exact (simple_socle pointKernel pointKernel_isAtom
    (SimpleHeadQuotient.isCoatom_ker_of_surjective pointWeightedSum pointWeightedSum_surjective).1
    pointCore_subrepresentations).symm

/-- The literal span of all simple submodules is the natural kernel. -/
theorem lineKernel_eq_socle :
    lineKernel = sSup {N : Subrepresentation lineCoreRepresentation | IsAtom N} := by
  let : IsIrreducible W.dual := IrreducibleCatalogue.dual_irreducible
  exact (simple_socle lineKernel lineKernel_isAtom
    (SimpleHeadQuotient.isCoatom_ker_of_surjective lineWeightedSum lineWeightedSum_surjective).1
    lineCore_subrepresentations).symm

private theorem no_decomposition
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    {ξ : Representation (ZMod 2) Group X}
    (K : Subrepresentation ξ) (hKt : K ≠ ⊤)
    (hthree : ∀ N : Subrepresentation ξ, N = ⊥ ∨ N = K ∨ N = ⊤)
    (A B : Subrepresentation ξ) (h : IsCompl A B) : A = ⊥ ∨ B = ⊥ := by
  rcases hthree A with hA | hA | hA
  · exact Or.inl hA
  · rcases hthree B with hB | hB | hB
    · exact Or.inr hB
    · exact False.elim (hKt (by simpa [hA, hB] using h.sup_eq_top))
    · left
      simpa [hB] using h.inf_eq_bot
  · right
    have hz := h.inf_eq_bot
    simpa [hA] using hz

/-- H.5.3(5): every internal direct-sum decomposition of the point core has a zero summand. -/
theorem pointCore_indecomposable (A B : Subrepresentation U₂) (h : IsCompl A B) :
    A = ⊥ ∨ B = ⊥ := by
  let : IsIrreducible W := IrreducibleCatalogue.natural_irreducible
  exact no_decomposition pointKernel
    (SimpleHeadQuotient.isCoatom_ker_of_surjective pointWeightedSum pointWeightedSum_surjective).1
    pointCore_subrepresentations A B h

/-- The dual point-line statement: the line core is indecomposable. -/
theorem lineCore_indecomposable (A B : Subrepresentation lineCoreRepresentation)
    (h : IsCompl A B) : A = ⊥ ∨ B = ⊥ := by
  let : IsIrreducible W.dual := IrreducibleCatalogue.dual_irreducible
  exact no_decomposition lineKernel
    (SimpleHeadQuotient.isCoatom_ker_of_surjective lineWeightedSum lineWeightedSum_surjective).1
    lineCore_subrepresentations A B h

end BinaryLinearThree.FanoCoreStructure
