module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.Defs
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Complete

/-!
# The whole actor in the strong-quotient branch

The degree-eight classification identifies a contained strong offender with a
conjugate of the group of four independent swaps. Any permutation centralizing
those swaps preserves each pair and is one of their sixteen products. Hence an
elementary overgroup equals the contained offender. Applying the inverse
conjugation simultaneously to the actor and the equivariant natural model gives
the required marking. Fixed codimension is then three; subtraction from the
quadratic-family bound on the ambient module gives the bound five on W.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 13.8.25, printed p.960, PDF p.977. Recognition of
the commutator submodule of W remains a separate constituent and extension step.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels
open Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders
open CFSG.Quasithin.ChapterB.Offenders.Eight
open scoped IsMulCommutative

private theorem pair_preserved (g : Perm) (a b : Fin 8) (hab : a ≠ b)
    (hc : Equiv.swap a b * g = g * Equiv.swap a b) : g a = a ∨ g a = b := by
  by_contra! hn
  have h := congrArg (fun p : Perm => p a) hc
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne hn.1 hn.2] at h
  exact hab (g.injective h)

private theorem word_of_pair_images (g : Perm)
    (h0 : g 0 = 0 ∨ g 0 = 1) (h2 : g 2 = 2 ∨ g 2 = 3)
    (h4 : g 4 = 4 ∨ g 4 = 5) (h6 : g 6 = 6 ∨ g 6 = 7)
    (h1 : g 1 = Equiv.swap 0 1 (g 0))
    (h3 : g 3 = Equiv.swap 2 3 (g 2))
    (h5 : g 5 = Equiv.swap 4 5 (g 4))
    (h7 : g 7 = Equiv.swap 6 7 (g 6)) : g ∈ D 8 := by
  apply (mem_D_iff g).mpr
  refine ⟨⟨(if g 0 = 1 then 1 else 0) + (if g 2 = 3 then 2 else 0) +
    (if g 4 = 5 then 4 else 0) + (if g 6 = 7 then 8 else 0), by
      split_ifs <;> omega⟩, ?_⟩
  rcases h0 with h0 | h0 <;> rcases h2 with h2 | h2 <;>
    rcases h4 with h4 | h4 <;> rcases h6 with h6 | h6
  all_goals simp only [h0, h2, h4, h6] at h1 h3 h5 h7
  all_goals simp only [Equiv.swap_apply_left, Equiv.swap_apply_right] at h1 h3 h5 h7
  all_goals ext i; fin_cases i <;>
    simp [dWords, cubeWords, pairSwap, h0, h1, h2, h3, h4, h5, h6, h7,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def]

/-- The four independent swaps are self-centralizing in the symmetric group. -/
theorem centralizer_D8_le : Subgroup.centralizer (D 8 : Set Perm) ≤ D 8 := by
  intro g hg
  have hc (i : Fin 4) := Subgroup.mem_centralizer_iff.mp hg
    (pairSwap 8 i) (pairSwap_mem (n := 8) (m := 4) i i.isLt)
  have h0 := pair_preserved g 0 1 (by decide) (hc 0)
  have h2 := pair_preserved g 2 3 (by decide) (hc 1)
  have h4 := pair_preserved g 4 5 (by decide) (hc 2)
  have h6 := pair_preserved g 6 7 (by decide) (hc 3)
  apply word_of_pair_images g h0 h2 h4 h6
  · simpa [pairSwap, Equiv.Perm.mul_apply] using (congrArg (fun p : Perm => p 0) (hc 0)).symm
  · simpa [pairSwap, Equiv.Perm.mul_apply] using (congrArg (fun p : Perm => p 2) (hc 1)).symm
  · simpa [pairSwap, Equiv.Perm.mul_apply] using (congrArg (fun p : Perm => p 4) (hc 2)).symm
  · simpa [pairSwap, Equiv.Perm.mul_apply] using (congrArg (fun p : Perm => p 6) (hc 3)).symm


/-- An abelian overgroup of a conjugate of E₁₆ equals that conjugate. -/
theorem eq_of_abelian_overgroup_conjugate_D (A B : Subgroup Perm)
    [IsMulCommutative A] (hBA : B ≤ A) (hB : IsConjugateTo B (D 8)) : A = B := by
  obtain ⟨g, hB⟩ := hB
  apply le_antisymm _ hBA
  intro a ha
  rw [hB]
  let f := MulAut.conj g
  refine ⟨f.symm a, centralizer_D8_le ?_, f.apply_symm_apply a⟩
  apply Subgroup.mem_centralizer_iff.mpr
  intro d hd
  apply f.injective
  simp only [map_mul, f.apply_symm_apply]
  have hdA : f d ∈ A := hBA (by rw [hB]; exact Subgroup.mem_map_of_mem f.toMonoidHom hd)
  exact congrArg Subtype.val (mul_comm (⟨f d, hdA⟩ : A) ⟨a, ha⟩)

/-- A contained strong offender on the natural module is the whole elementary actor. -/
theorem whole_actor_conjugate_D (A B : Subgroup Perm) (hA : IsElementaryTwo A)
    (hBA : B ≤ A) (hB : IsStrongOffender (BinaryPermutation.naturalRepresentation (Fin 8)) B) :
    A = B ∧ IsConjugateTo A (D 8) := by
  let : IsElementaryAbelian 2 A := hA.2
  have hBD := (isStrongOffender_natural_iff B).mp hB
  have he := eq_of_abelian_overgroup_conjugate_D A B hBA hBD
  exact ⟨he, he.symm ▸ hBD⟩


variable {H U E : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup E] [Module (ZMod 2) E]

private noncomputable def operatorEquiv (σ : Representation (ZMod 2) Perm E) (g : Perm) :
    E ≃ₗ[ZMod 2] E :=
  LinearEquiv.ofLinearMap (σ g) (σ g⁻¹)
    (by change σ g * σ g⁻¹ = 1; rw [← map_mul, mul_inv_cancel, map_one])
    (by change σ g⁻¹ * σ g = 1; rw [← map_mul, inv_mul_cancel, map_one])

private theorem conjugate_intertwiner (ρ : Representation (ZMod 2) H U)
    (σ : Representation (ZMod 2) Perm E) (eH : H ≃* Perm) (g : Perm)
    (e : U ≃ₗ[ZMod 2] E) (he : ∀ h u, e (ρ h u) = σ (eH h) (e u)) :
    ∃ e' : U ≃ₗ[ZMod 2] E,
      ∀ h u, e' (ρ h u) = σ (conjugateMarking eH g h) (e' u) := by
  refine ⟨e.trans (operatorEquiv σ g), ?_⟩
  intro h u
  change σ g (e (ρ h u)) = σ (g * eH h * g⁻¹) (σ g (e u))
  rw [he]
  simp only [map_mul, Module.End.mul_apply]
  have hc : σ g⁻¹ (σ g (e u)) = e u := by
    change (σ g⁻¹ * σ g) (e u) = e u
    rw [← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [hc]

/-- Transport the natural module together with its permutation coordinates. -/
theorem IsEightNatural.conjugate (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* Perm) (h : IsEightNatural ρ eH) (g : Perm) :
    IsEightNatural ρ (conjugateMarking eH g) := by
  obtain ⟨e, he⟩ := h
  exact conjugate_intertwiner ρ (naturalRepresentation (Fin 8)) eH g e he

/-- The same coordinate change preserves either of the two permitted section models. -/
theorem naturalOrCover_conjugate (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* Perm) (h : IsEightNaturalOrCover ρ eH) (g : Perm) :
    IsEightNaturalOrCover ρ (conjugateMarking eH g) := by
  rcases h with ⟨e, he⟩ | ⟨e, he⟩
  · exact Or.inl (conjugate_intertwiner ρ (naturalRepresentation (Fin 8)) eH g e he)
  · exact Or.inr (conjugate_intertwiner ρ (coreRepresentation (Fin 8)) eH g e he)

/-- Subgroups use precisely the same coordinate change as the modules. -/
theorem map_conjugateMarking (eH : H ≃* Perm) (g : Perm) (A : Subgroup H) :
    A.map (conjugateMarking eH g).toMonoidHom =
      (A.map eH.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

/-- A conjugacy to a representative gives a marking with exactly that representative. -/
theorem exists_conjugate_marking (eH : H ≃* Perm) (A : Subgroup H) (B : Subgroup Perm)
    (hA : IsConjugateTo (A.map eH.toMonoidHom) B) :
    ∃ g : Perm, A.map (conjugateMarking eH g).toMonoidHom = B := by
  obtain ⟨g, hg⟩ := hA
  refine ⟨g⁻¹, ?_⟩
  rw [map_conjugateMarking, hg, Subgroup.map_map]
  have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id Perm := by
    ext a
    simp [MulAut.conj_apply, mul_assoc]
  rw [he, Subgroup.map_id]


/-- Injective actor transport preserves a nontrivial elementary two-group. -/
theorem elementary_map {G L : Type*} [Group G] [Group L]
    (f : G →* L) (hf : Function.Injective f) {A : Subgroup G}
    (hA : IsElementaryTwo A) : IsElementaryTwo (A.map f) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 A := hA.2
  exact ⟨fun h => hA.1 ((Subgroup.map_eq_bot_iff_of_injective A hf).mp h),
    IsElementaryAbelian.map f⟩

/-- Identify the whole actor, and remark the natural module compatibly. Bestness is not needed. -/
theorem strong_natural_actor_marking (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* Perm) (hmodel : IsEightNatural ρ eH)
    (A B : Subgroup H) (hA : IsElementaryTwo A) (hBA : B ≤ A)
    (hB : IsStrongOffender ρ B) :
    A = B ∧ ∃ g : Perm,
      A.map (conjugateMarking eH g).toMonoidHom = D 8 ∧
      IsEightNatural ρ (conjugateMarking eH g) := by
  obtain ⟨e, he⟩ := hmodel
  have hB' : IsStrongOffender (naturalRepresentation (Fin 8)) (B.map eH.toMonoidHom) := by
    refine ⟨elementary_map eH.toMonoidHom eH.injective hB.1, ?_⟩
    rw [← fixedCodim_map_equivariant ρ (naturalRepresentation (Fin 8))
      eH.toMonoidHom e he, rank_map_injective eH.toMonoidHom eH.injective]
    exact hB.2
  obtain ⟨heq, hconj⟩ := whole_actor_conjugate_D (A.map eH.toMonoidHom)
    (B.map eH.toMonoidHom) (elementary_map eH.toMonoidHom eH.injective hA)
    (Subgroup.map_mono hBA) hB'
  obtain ⟨g, hg⟩ := exists_conjugate_marking eH A (D 8) hconj
  exact ⟨Subgroup.map_injective eH.injective heq, g, hg,
    IsEightNatural.conjugate ρ eH ⟨e, he⟩ g⟩

/-- The strong-quotient branch gives rank four, quotient fixed codimension three,
and fixed codimension at most five on W. The bound on U is the dimension
inequality in membership of the critical actor in the source quadratic family. -/
theorem strong_quotient_marking_and_bounds [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (W : Subrepresentation ρ)
    (eH : H ≃* Perm) (hQ : IsEightNatural W.quotientRepresentation eH)
    (A : Subgroup H) (hA : IsElementaryTwo A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hstrong : ∃ B ≤ A, IsStrongOffender W.quotientRepresentation B) :
    ∃ g : Perm, A.map (conjugateMarking eH g).toMonoidHom = D 8 ∧
      IsEightNatural W.quotientRepresentation (conjugateMarking eH g) ∧
      rank A = 4 ∧ fixedCodim W.quotientRepresentation A = 3 ∧
      fixedCodim W.toRepresentation A ≤ 5 := by
  obtain ⟨B, hBA, hB⟩ := hstrong
  obtain ⟨_, g, hg, hQg⟩ := strong_natural_actor_marking W.quotientRepresentation
    eH hQ A B hA hBA hB
  have hr : rank A = 4 := by
    rw [← rank_map_injective (conjugateMarking eH g).toMonoidHom
      (conjugateMarking eH g).injective A, hg]
    exact Eight.rank_D
  have hq : fixedCodim W.quotientRepresentation A = 3 :=
    fixedCodim_eightNaturalOrCover W.quotientRepresentation
      (conjugateMarking eH g) (Or.inl hQg) A hg
  have hsum := fixedCodim_quotient_add_subrepresentation_le ρ W A
  exact ⟨g, hg, hQg, hr, hq, by omega⟩

/-- Inner coordinate changes preserve the specified alternating component. -/
theorem alternating_marking_conjugate (eH : H ≃* Perm) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8)) (g : Perm) :
    K.map (conjugateMarking eH g).toMonoidHom = alternatingGroup (Fin 8) := by
  rw [map_conjugateMarking, hK]
  exact Subgroup.Normal.map_conj_eq _ g

private theorem strong_equivariant (ρ : Representation (ZMod 2) H U)
    (σ : Representation (ZMod 2) Perm E) (eH : H ≃* Perm)
    (e : U ≃ₗ[ZMod 2] E) (he : ∀ g u, e (ρ g u) = σ (eH g) (e u))
    {B : Subgroup H} (hB : IsStrongOffender ρ B) :
    IsStrongOffender σ (B.map eH.toMonoidHom) := by
  refine ⟨elementary_map eH.toMonoidHom eH.injective hB.1, ?_⟩
  rw [← fixedCodim_map_equivariant ρ σ eH.toMonoidHom e he,
    rank_map_injective eH.toMonoidHom eH.injective]
  exact hB.2

/-- The whole-actor argument also applies after recognizing an augmentation cover.
The elementary overgroup is identified, not just its contained strong offender. -/
theorem strong_model_actor_marking (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* Perm) (hmodel : IsEightNaturalOrCover ρ eH)
    (A B : Subgroup H) (hA : IsElementaryTwo A) (hBA : B ≤ A)
    (hB : IsStrongOffender ρ B) :
    A = B ∧ ∃ g : Perm,
      A.map (conjugateMarking eH g).toMonoidHom = D 8 ∧
      IsEightNaturalOrCover ρ (conjugateMarking eH g) := by
  have hconj : IsConjugateTo (B.map eH.toMonoidHom) (D 8) := by
    rcases hmodel with ⟨e, he⟩ | ⟨e, he⟩
    · exact (isStrongOffender_natural_iff _).mp
        (strong_equivariant ρ (naturalRepresentation (Fin 8)) eH e he hB)
    · exact (isStrongOffender_core_iff _).mp
        (strong_equivariant ρ (coreRepresentation (Fin 8)) eH e he hB)
  have ha := elementary_map eH.toMonoidHom eH.injective hA
  let : IsElementaryAbelian 2 (A.map eH.toMonoidHom) := ha.2
  have he := eq_of_abelian_overgroup_conjugate_D (A.map eH.toMonoidHom)
    (B.map eH.toMonoidHom) (Subgroup.map_mono hBA) hconj
  obtain ⟨g, hg⟩ := exists_conjugate_marking eH A (D 8) (he.symm ▸ hconj)
  exact ⟨Subgroup.map_injective eH.injective he, g, hg,
    naturalOrCover_conjugate ρ eH hmodel g⟩

/-- Remark the actual commutator submodule without changing its inclusion. -/
theorem commutator_model_conjugate (ρ : Representation (ZMod 2) H U)
    (K : Subgroup H) (eH : H ≃* Perm) (h : IsCommutatorNaturalOrCover ρ K eH)
    (g : Perm) : IsCommutatorNaturalOrCover ρ K (conjugateMarking eH g) := by
  obtain ⟨J, hJ, hj⟩ := h
  exact ⟨J, hJ, naturalOrCover_conjugate J.toRepresentation eH hj g⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels
