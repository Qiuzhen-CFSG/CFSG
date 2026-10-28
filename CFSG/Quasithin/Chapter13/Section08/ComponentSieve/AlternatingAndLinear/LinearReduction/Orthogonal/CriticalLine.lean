module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalBounds
public import Theory.Representation.BinaryOffender.SmallRank
public import Theory.Representation.BinaryPermutation.OffenderFixedSpace

/-!
# The critical centralizer in the orthogonal branch of 13.8.25

On the six-dimensional natural S₈ module and the seven-dimensional augmentation
core, the four disjoint transpositions have distinct nonzero centers. If their
displacements on a subspace lie in a common binary line, at most one generator
moves that subspace, so its pointwise centralizer has index at most two.

For the source's two sections, a critical line contained in W would force the
critical subspace to have codimension at most one on the model inside W, which
is impossible. The line therefore misses W, and projection to the quotient
preserves the critical centralizer. The already proved six-versus-five argument
then gives the contradiction, without assuming the centralizer index.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 13.8.25, printed p.960, PDF p.977. These are linear
geometric deductions; selection of the maximal submodule, recognition of its
sections and transport from the actual critical-pair subgroups remain separate
source obligations.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction
open Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders

private def pairVector (i : Fin 4) : Full (Fin 8) :=
  Pi.single ⟨2 * i.val, by omega⟩ 1 + Pi.single ⟨2 * i.val + 1, by omega⟩ 1
private def coreCenter (i : Fin 4) : core (Fin 8) :=
  ⟨pairVector i, by simp [pairVector, mem_core, Finset.sum_add_distrib,
    CharTwo.add_self_eq_zero]⟩
private def naturalCenter (i : Fin 4) : natural (Fin 8) :=
  ⟨(constants (Fin 8)).mkQ (pairVector i), ⟨pairVector i, (coreCenter i).property, rfl⟩⟩

private theorem pair_displacement (i : Fin 4) (v : Full (Fin 8)) :
    representation (Fin 8) (pairSwap 8 i) v - v = 0 ∨
    representation (Fin 8) (pairSwap 8 i) v - v = pairVector i := by
  have h : v ⟨2 * i.val + 1, by omega⟩ - v ⟨2 * i.val, by omega⟩ = 0 ∨
      v ⟨2 * i.val + 1, by omega⟩ - v ⟨2 * i.val, by omega⟩ = 1 := by
    exact (by decide : ∀ x : (ZMod 2), x = 0 ∨ x = 1) _
  have he : representation (Fin 8) (pairSwap 8 i) v - v =
      (v ⟨2 * i.val + 1, by omega⟩ - v ⟨2 * i.val, by omega⟩) • pairVector i := by
    ext k
    fin_cases i <;> fin_cases k <;>
      simp [pairSwap, pairVector, representation_apply, sub_eq_add_neg,
        CharTwo.neg_eq, add_comm, Equiv.swap_apply_def, CharTwo.add_self_eq_zero]
  rcases h with h | h
  · exact Or.inl (by rw [he, h, zero_smul])
  · exact Or.inr (by rw [he, h, one_smul])

private theorem core_displacement (i : Fin 4) (v : core (Fin 8)) :
    coreRepresentation (Fin 8) (pairSwap 8 i) v - v = 0 ∨
    coreRepresentation (Fin 8) (pairSwap 8 i) v - v = coreCenter i := by
  rcases pair_displacement i v with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

private theorem natural_displacement (i : Fin 4) (v : natural (Fin 8)) :
    naturalRepresentation (Fin 8) (pairSwap 8 i) v - v = 0 ∨
    naturalRepresentation (Fin 8) (pairSwap 8 i) v - v = naturalCenter i := by
  obtain ⟨w, _, hw⟩ := v.property
  rcases pair_displacement i w with h | h
  · left
    apply Subtype.ext
    change deletedRepresentation (Fin 8) (pairSwap 8 i) v.val - v.val = 0
    rw [← hw, deletedRepresentation_mk, ← map_sub, h, map_zero]
  · right
    apply Subtype.ext
    change deletedRepresentation (Fin 8) (pairSwap 8 i) v.val - v.val =
      (constants (Fin 8)).mkQ (pairVector i)
    rw [← hw, deletedRepresentation_mk, ← map_sub, h]

private theorem pair_eq_of_quotient_eq (i j : Fin 4)
    (h : (constants (Fin 8)).mkQ (pairVector i) =
      (constants (Fin 8)).mkQ (pairVector j)) : i = j := by
  have hc := (Submodule.Quotient.eq _).mp h
  obtain ⟨c, hc⟩ := (mem_constants_iff (pairVector i - pairVector j)).mp hc
  have ht : ∀ i j : Fin 4, ∀ c : (ZMod 2),
      (∀ k : Fin 8, (pairVector i - pairVector j) k = c) → i = j := by
    decide +kernel
  exact ht i j c hc

private theorem naturalCenter_injective : Function.Injective naturalCenter := by
  intro i j h
  exact pair_eq_of_quotient_eq i j (congrArg Subtype.val h)

private theorem naturalCenter_ne_zero (i : Fin 4) : naturalCenter i ≠ 0 := by
  intro h
  have hc : pairVector i ∈ constants (Fin 8) :=
    (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (mem_constants_iff _).mp hc
  have ht : ∀ i : Fin 4, ∀ c : (ZMod 2), ¬ ∀ k : Fin 8, pairVector i k = c := by decide +kernel
  exact ht i c hc

private theorem coreCenter_injective : Function.Injective coreCenter := by
  intro i j h
  exact pair_eq_of_quotient_eq i j (congrArg (fun x : core (Fin 8) =>
    (constants (Fin 8)).mkQ x.val) h)

private theorem coreCenter_ne_zero (i : Fin 4) : coreCenter i ≠ 0 := by
  intro h
  apply naturalCenter_ne_zero i
  apply Subtype.ext
  exact congrArg (fun x : core (Fin 8) => (constants (Fin 8)).mkQ x.val) h

private theorem index_of_all_but_one (C : Subgroup (Equiv.Perm (Fin 8))) (i : Fin 4)
    (hC : ∀ j : Fin 4, j ≠ i → pairSwap 8 j ∈ C) : C.relIndex (D 8) ∣ 2 := by
  have hmul : ∀ i j : Fin 4, pairSwap 8 i * pairSwap 8 j =
      pairSwap 8 j * pairSwap 8 i := by decide +kernel
  have hinv : ∀ i : Fin 4, (pairSwap 8 i)⁻¹ = pairSwap 8 i := by decide +kernel
  have hsq : ∀ i : Fin 4, pairSwap 8 i * pairSwap 8 i = 1 := by decide +kernel
  let a := pairSwap 8 i
  have hcentral : ∀ b ∈ D 8, b * a = a * b := by
    intro b hb
    induction hb using Subgroup.closure_induction with
    | mem b hb => obtain ⟨j, _, rfl⟩ := hb; exact hmul j i
    | one => simp
    | mul b c _ _ hb hc => calc
        b * c * a = b * (c * a) := mul_assoc _ _ _
        _ = b * (a * c) := by rw [hc]
        _ = (b * a) * c := (mul_assoc _ _ _).symm
        _ = (a * b) * c := by rw [hb]
        _ = a * (b * c) := mul_assoc _ _ _
    | inv b _ hb => exact (Commute.inv_left (show Commute b a from hb)).eq
  apply Subgroup.relIndex_dvd_two_iff.mpr
  refine ⟨a, pairSwap_mem (n := 8) (m := 4) i i.isLt, ?_⟩
  intro b hb
  induction hb using Subgroup.closure_induction with
  | mem b hb =>
      obtain ⟨j, _, rfl⟩ := hb
      by_cases hji : j = i
      · subst j; exact Or.inl (by simpa only [a, hsq] using C.one_mem)
      · exact Or.inr (hC j hji)
  | one => exact Or.inr C.one_mem
  | mul b c hb hc ihb ihc =>
      rcases ihb with ihb | ihb <;> rcases ihc with ihc | ihc
      · right
        have h := C.mul_mem ihb ihc
        have he : (b * a) * (c * a) = b * c := by
          calc
            _ = b * (a * c) * a := by simp only [mul_assoc]
            _ = b * (c * a) * a := by rw [← hcentral c hc]
            _ = b * c := by simp only [mul_assoc, a, hsq, mul_one]
        exact he ▸ h
      · left
        have h := C.mul_mem ihb ihc
        simpa only [mul_assoc, ← hcentral c hc] using h
      · left; simpa only [mul_assoc] using C.mul_mem ihb ihc
      · exact Or.inr (C.mul_mem ihb ihc)
  | inv b hb ih =>
      rcases ih with ih | ih
      · left
        have h := C.inv_mem ih
        rw [mul_inv_rev, show a⁻¹ = a from hinv i] at h
        have hc := (Commute.inv_left (show Commute b a from hcentral b hb)).eq
        rwa [hc]
      · exact Or.inr (C.inv_mem ih)

private theorem binary_line_unique {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] (S : Submodule (ZMod 2) E) (hS : Module.finrank (ZMod 2) S ≤ 1)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) (hx0 : x ≠ 0) (hy0 : y ≠ 0) : x = y := by
  have hs0 : S ≠ ⊥ := by intro h; exact hx0 (by simpa [h] using hx)
  have hpos := Submodule.finrank_lt_finrank_of_lt (bot_lt_iff_ne_bot.mpr hs0)
  have hdim : Module.finrank (ZMod 2) S = 1 := by simp only [finrank_bot] at hpos; omega
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hdim hx hx0
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hy)
  have hc0 : c ≠ 0 := by intro hz; exact hy0 (by simpa [hz] using hc.symm)
  have hc1 : c = 1 := (by decide : ∀ c : (ZMod 2), c ≠ 0 → c = 1) c hc0
  simpa [hc1] using hc

private theorem index_of_distinct_centers {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] (σ : Representation (ZMod 2) (Equiv.Perm (Fin 8)) E) (c : Fin 4 → E)
    (hc : Function.Injective c) (hc0 : ∀ i, c i ≠ 0)
    (hdisp : ∀ i v, σ (pairSwap 8 i) v - v = 0 ∨ σ (pairSwap 8 i) v - v = c i)
    (X S : Submodule (ZMod 2) E) (hS : Module.finrank (ZMod 2) S ≤ 1)
    (hcomm : ∀ a ∈ D 8, ∀ x ∈ X, σ a x - x ∈ S) :
    (subspaceKernel σ X (D 8)).relIndex (D 8) ∣ 2 := by
  classical
  have hu : ∀ i j, c i ∈ S → c j ∈ S → i = j := by
    intro i j hi hj
    exact hc (binary_line_unique S hS hi hj (hc0 i) (hc0 j))
  obtain ⟨i, hi⟩ : ∃ i : Fin 4, ∀ j : Fin 4, j ≠ i → c j ∉ S := by
    by_cases he : ∃ i, c i ∈ S
    · obtain ⟨i, hi⟩ := he
      exact ⟨i, fun j hji hj => hji (hu j i hj hi)⟩
    · exact ⟨0, fun j _ hj => he ⟨j, hj⟩⟩
  apply index_of_all_but_one _ i
  intro j hji
  refine ⟨pairSwap_mem (n := 8) (m := 4) j j.isLt, ?_⟩
  intro x hx
  rcases hdisp j x with h | h
  · exact sub_eq_zero.mp h
  · exact (hi j hji (h ▸ hcomm _ (pairSwap_mem (n := 8) (m := 4) j j.isLt) x hx)).elim

private theorem transport_index {H U E : Type*} [Group H]
    [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) U] [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) H U) (σ : Representation (ZMod 2) (Equiv.Perm (Fin 8)) E)
    (eH : H ≃* (Equiv.Perm (Fin 8))) (e : U ≃ₗ[(ZMod 2)] E)
    (he : ∀ g u, e (ρ g u) = σ (eH g) (e u))
    (A : Subgroup H) (hA : A.map eH.toMonoidHom = D 8)
    (X S : Submodule (ZMod 2) U) (hS : Module.finrank (ZMod 2) S ≤ 1)
    (hcomm : ∀ a ∈ A, ∀ x ∈ X, ρ a x - x ∈ S)
    (hmodel : ∀ X S : Submodule (ZMod 2) E, Module.finrank (ZMod 2) S ≤ 1 →
      (∀ a ∈ D 8, ∀ x ∈ X, σ a x - x ∈ S) →
      (subspaceKernel σ X (D 8)).relIndex (D 8) ∣ 2) :
    (subspaceKernel ρ X A).relIndex A ∣ 2 := by
  have hindex := hmodel (X.map e.toLinearMap) (S.map e.toLinearMap)
    ((Submodule.finrank_map_le _ _).trans hS) (by
      intro a ha x hx
      rw [← hA] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      obtain ⟨u, hu, rfl⟩ := hx
      refine ⟨ρ b u - u, hcomm b hb u hu, ?_⟩
      exact (map_sub e _ _).trans (congrArg (fun z => z - e u) (he b u)))
  obtain ⟨a, ha, hc⟩ := Subgroup.relIndex_dvd_two_iff.mp hindex
  have haf : eH.symm a ∈ A := by
    rw [← hA] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    simpa using hb
  have hfix (b : H) (hb : b ∈ A)
      (h : eH b ∈ subspaceKernel σ (X.map e.toLinearMap) (D 8)) :
      b ∈ subspaceKernel ρ X A := by
    refine ⟨hb, fun x hx => e.injective ?_⟩
    rw [he]
    exact h.2 (e x) (Submodule.mem_map_of_mem hx)
  apply Subgroup.relIndex_dvd_two_iff.mpr
  refine ⟨eH.symm a, haf, ?_⟩
  intro b hb
  have hb' : eH b ∈ D 8 := hA ▸ Subgroup.mem_map_of_mem eH.toMonoidHom hb
  rcases hc (eH b) hb' with h | h
  · left
    apply hfix (b * eH.symm a) (A.mul_mem hb haf)
    simpa only [map_mul, eH.apply_symm_apply] using h
  · exact Or.inr (hfix b hb h)

/-- For the actual natural or augmentation action, a common commutator line
on a subspace permits at most one disjoint transposition to move that subspace.
Thus its pointwise centralizer has index at most two in the marked E₁₆. -/
theorem eightNaturalOrCover_critical_centralizer_index {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U] (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* (Equiv.Perm (Fin 8))) (hmodel : IsEightNaturalOrCover ρ eH)
    (A : Subgroup H) (hA : A.map eH.toMonoidHom = D 8)
    (X S : Submodule (ZMod 2) U) (hS : Module.finrank (ZMod 2) S ≤ 1)
    (hcomm : ∀ a ∈ A, ∀ x ∈ X, ρ a x - x ∈ S) :
    (subspaceKernel ρ X A).relIndex A ∣ 2 := by
  rcases hmodel with ⟨e, he⟩ | ⟨e, he⟩
  · apply transport_index ρ (naturalRepresentation (Fin 8)) eH e he A hA X S hS hcomm
    exact index_of_distinct_centers _ naturalCenter naturalCenter_injective
      naturalCenter_ne_zero natural_displacement
  · apply transport_index ρ (coreRepresentation (Fin 8)) eH e he A hA X S hS hcomm
    exact index_of_distinct_centers _ coreCenter coreCenter_injective
      coreCenter_ne_zero core_displacement

private theorem finrank_comap_le {V E : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
    (f : V →ₗ[(ZMod 2)] E) (hf : Function.Injective f) (S : Submodule (ZMod 2) E) :
    Module.finrank (ZMod 2) (S.comap f) ≤ Module.finrank (ZMod 2) S := by
  rw [(Submodule.equivMapOfInjective f hf (S.comap f)).finrank_eq]
  exact Submodule.finrank_mono (Submodule.map_comap_le _ _)

private theorem line_disjoint {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U] (S W : Submodule (ZMod 2) U) (hS : Module.finrank (ZMod 2) S ≤ 1)
    (hSW : ¬ S ≤ W) : S ⊓ W = ⊥ := by
  by_contra hn
  have hpos := Submodule.finrank_lt_finrank_of_lt (bot_lt_iff_ne_bot.mpr hn)
  simp only [finrank_bot] at hpos
  have he : S ⊓ W = S := Submodule.eq_of_le_of_finrank_le inf_le_left (by omega)
  exact hSW (he.symm.le.trans inf_le_right)

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U] (ρ : Representation (ZMod 2) H U)

/-- The critical line cannot lie in W. If it did, the quotient contributes
three to the critical codimension, leaving at most one on the model inside W.
The distinct-center bound on that model then contradicts its fixed codimension
three. The model may be [W,H], rather than all of W. -/
theorem critical_line_not_le_of_orthogonal_sections
    (W : Subrepresentation ρ) (J : Subrepresentation W.toRepresentation)
    (eH : H ≃* (Equiv.Perm (Fin 8))) (hJ : IsEightNaturalOrCover J.toRepresentation eH)
    (hQ : IsEightNaturalOrCover W.quotientRepresentation eH)
    (A : Subgroup H) (hA : A.map eH.toMonoidHom = D 8)
    (X S : Submodule (ZMod 2) U) (hX : Module.finrank (ZMod 2) (U ⧸ X) ≤ 4)
    (hS : Module.finrank (ZMod 2) S ≤ 1)
    (hcomm : ∀ a ∈ A, ∀ x ∈ X, ρ a x - x ∈ S) :
    ¬ S ≤ W.toSubmodule := by
  intro hSW
  let XW := X.comap W.toSubmodule.subtype
  let XJ := XW.comap J.toSubmodule.subtype
  let f := W.toSubmodule.subtype.comp J.toSubmodule.subtype
  let SJ := S.comap f
  have hSJ : Module.finrank (ZMod 2) SJ ≤ 1 :=
    (finrank_comap_le f (W.toSubmodule.subtype_injective.comp
      J.toSubmodule.subtype_injective) S).trans hS
  have hcommJ : ∀ a ∈ A, ∀ x ∈ XJ, J.toRepresentation a x - x ∈ SJ := by
    intro a ha x hx
    exact hcomm a ha (f x) hx
  have hindex := eightNaturalOrCover_critical_centralizer_index J.toRepresentation eH hJ A hA XJ SJ hSJ hcommJ
  have hjbound := fixedCodim_le_of_critical_centralizer J.toRepresentation
    XJ SJ A hcommJ hindex
  have hjcodim := fixedCodim_eightNaturalOrCover J.toRepresentation eH hJ A hA
  have hqcodim := fixedCodim_eightNaturalOrCover W.quotientRepresentation eH hQ A hA
  have hfix : X.map W.toSubmodule.mkQ ≤ fixedSpace W.quotientRepresentation A := by
    rintro _ ⟨x, hx, rfl⟩ a
    exact (Submodule.Quotient.eq _).mpr (hSW (hcomm a a.property x hx))
  have hdim := Submodule.finrank_mono hfix
  have hquot := (X.map W.toSubmodule.mkQ).finrank_quotient_add_finrank
  have hfixed := fixedCodim_add_finrank W.quotientRepresentation A
  have hsup := (Submodule.quotientQuotientEquivQuotientSup W.toSubmodule X).finrank_eq
  have hwdec := codim_decomposition W.toSubmodule X
  have hjdec := codim_decomposition J.toSubmodule XW
  change _ + Module.finrank (ZMod 2) (J.toSubmodule ⧸ XJ) =
    Module.finrank (ZMod 2) (W.toSubmodule ⧸ XW) at hjdec
  change _ + Module.finrank (ZMod 2) (W.toSubmodule ⧸ XW) = _ at hwdec
  omega

private theorem section_index
    (W : Subrepresentation ρ) (J : Subrepresentation W.toRepresentation)
    (eH : H ≃* (Equiv.Perm (Fin 8))) (hJ : IsEightNaturalOrCover J.toRepresentation eH)
    (hQ : IsEightNaturalOrCover W.quotientRepresentation eH)
    (A : Subgroup H) (hA : A.map eH.toMonoidHom = D 8)
    (X S : Submodule (ZMod 2) U) (hX : Module.finrank (ZMod 2) (U ⧸ X) ≤ 4)
    (hS : Module.finrank (ZMod 2) S ≤ 1)
    (hcomm : ∀ a ∈ A, ∀ x ∈ X, ρ a x - x ∈ S) :
    (subspaceKernel ρ X A).relIndex A ∣ 2 := by
  have hSW := line_disjoint S W.toSubmodule hS
    (critical_line_not_le_of_orthogonal_sections ρ W J eH hJ hQ A hA X S hX hS hcomm)
  have hqcomm : ∀ a ∈ A, ∀ x ∈ X.map W.toSubmodule.mkQ,
      W.quotientRepresentation a x - x ∈ S.map W.toSubmodule.mkQ := by
    intro a ha x hx
    obtain ⟨u, hu, rfl⟩ := hx
    exact ⟨ρ a u - u, hcomm a ha u hu, map_sub _ _ _⟩
  have hindex := eightNaturalOrCover_critical_centralizer_index W.quotientRepresentation eH hQ A hA
    (X.map W.toSubmodule.mkQ) (S.map W.toSubmodule.mkQ)
    ((Submodule.finrank_map_le _ _).trans hS) hqcomm
  have he : subspaceKernel W.quotientRepresentation (X.map W.toSubmodule.mkQ) A =
      subspaceKernel ρ X A := by
    apply le_antisymm
    · rintro a ⟨ha, hfix⟩
      refine ⟨ha, fun x hx => sub_eq_zero.mp ?_⟩
      have hw : ρ a x - x ∈ W.toSubmodule :=
        (Submodule.Quotient.eq _).mp (hfix _ (Submodule.mem_map_of_mem hx))
      have hmem : ρ a x - x ∈ S ⊓ W.toSubmodule := ⟨hcomm a ha x hx, hw⟩
      simpa only [hSW, Submodule.mem_bot] using hmem
    · rintro a ⟨ha, hfix⟩
      refine ⟨ha, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact congrArg W.toSubmodule.mkQ (hfix x hx)
  rwa [he] at hindex

/-- The critical pointwise centralizer is a hyperplane in the actual marked
E₁₆. The line misses W by the preceding argument, so projection to the quotient
preserves this centralizer. The six-dimensional lower bound excludes index one. -/
theorem critical_centralizer_index_two_of_orthogonal_sections
    (W : Subrepresentation ρ) (J : Subrepresentation W.toRepresentation)
    (eH : H ≃* (Equiv.Perm (Fin 8))) (hJ : IsEightNaturalOrCover J.toRepresentation eH)
    (hQ : IsEightNaturalOrCover W.quotientRepresentation eH)
    (A : Subgroup H) (hA : A.map eH.toMonoidHom = D 8)
    (X S : Submodule (ZMod 2) U) (hX : Module.finrank (ZMod 2) (U ⧸ X) ≤ rank A)
    (hS : Module.finrank (ZMod 2) S ≤ 1)
    (hcomm : ∀ a ∈ A, ∀ x ∈ X, ρ a x - x ∈ S) :
    (subspaceKernel ρ X A).relIndex A = 2 := by
  have hrank : rank A = 4 := by
    rw [← rank_map_injective eH.toMonoidHom eH.injective A, hA, Eight.rank_D]
  have hi := section_index ρ W J eH hJ hQ A hA X S (by omega) hS hcomm
  have hn := critical_subspace_not_fixed_of_orthogonal_sections ρ W J eH hJ hQ A hA X hX
  rcases (Nat.dvd_prime Nat.prime_two).mp hi with h | h
  · have hle := Subgroup.relIndex_eq_one.mp h
    exact (hn (fun x hx a => (hle a.property).2 x hx)).elim
  · exact h

/-- The strong orthogonal contradiction with the centralizer-index premise
proved from transposition geometry. The actual source application still has to
construct the two compatible models, the marked actor and the critical subspace. -/
theorem orthogonal_sections_critical_line_contradiction
    (W : Subrepresentation ρ) (J : Subrepresentation W.toRepresentation)
    (eH : H ≃* (Equiv.Perm (Fin 8))) (hJ : IsEightNaturalOrCover J.toRepresentation eH)
    (hQ : IsEightNaturalOrCover W.quotientRepresentation eH)
    (A : Subgroup H) (hA : A.map eH.toMonoidHom = D 8)
    (X S : Submodule (ZMod 2) U) (hX : Module.finrank (ZMod 2) (U ⧸ X) ≤ rank A)
    (hS : Module.finrank (ZMod 2) S ≤ 1)
    (hcomm : ∀ a ∈ A, ∀ x ∈ X, ρ a x - x ∈ S) : False := by
  apply orthogonal_sections_contradiction ρ W J eH hJ hQ A hA X S hX hS hcomm
  rw [critical_centralizer_index_two_of_orthogonal_sections ρ W J eH hJ hQ A hA X S hX hS hcomm]

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction
