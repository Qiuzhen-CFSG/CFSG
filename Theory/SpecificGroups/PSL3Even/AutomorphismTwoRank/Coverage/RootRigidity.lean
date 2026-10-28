module

public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeCoverage.RootRigidity

/-!
# Root rigidity over arbitrary fields

A projective automorphism preserving every coordinate root group acts on each
root parameter by an additive bijection. The three-index elementary relation
forces the values at one to be ratios of diagonal entries. After this diagonal
correction all six parameter maps coincide, and the same relation proves
multiplicativity. Thus they define an actual field automorphism. Generation by
transvections identifies the original automorphism with the product of diagonal
conjugation and the entrywise field action on SL₃/Z(SL₃).

No prime-field assumption, automorphism lift, or simplicity hypothesis is used.
The root-preservation premise is explicit; its geometric construction belongs
to the coverage assembly.

Source: the generation assertion in GLS3, Theorem 2.5.12(a), and the matrix
conventions in §2.7 of `refs/KGroup/GLS3/chapter2.tex`, lines 1111–1115.
-/

public section

open scoped MatrixGroups
open Matrix
open Matrix.PSL3.OuterSolvable Matrix.PSL3.OuterSolvable.OddPrimeCoverage
namespace Matrix.PSL3Even.AutomorphismCoverage
variable {F : Type*} [Field F]

private theorem exists_root_maps (α : MulAut PSL(3,F)) (hα : PreservesRootGroups α) :
    ∃ f : ∀ (i j : Fin 3), i ≠ j → F → F,
      (∀ i j hij a, α (rootElement hij a) = rootElement hij (f i j hij a)) ∧
      (∀ i j hij, Function.Bijective (f i j hij)) := by
  have hex (i j : Fin 3) (hij : i ≠ j) (a : F) :
      ∃ b : F, α (rootElement hij a) = rootElement hij b := by
    have hm : α (rootElement hij a) ∈ rootGroup hij := by
      rw [← hα i j hij]
      exact Subgroup.mem_map_of_mem _ (rootElement_mem hij a)
    obtain ⟨b,hb⟩ := hm
    exact ⟨b.toAdd,hb.symm⟩
  choose f hf using hex
  refine ⟨f,hf,?_⟩
  intro i j hij
  constructor
  · intro a b hab
    apply rootElement_injective hij
    apply α.injective
    rw [hf,hf,hab]
  · intro b
    have hm : rootElement hij b ∈ (rootGroup hij).map α.toMonoidHom := by
      rw [hα i j hij]
      exact rootElement_mem hij b
    obtain ⟨_,⟨a,rfl⟩,ha⟩ := hm
    refine ⟨a.toAdd, rootElement_injective hij ?_⟩
    rw [← hf]
    exact ha

private theorem root_maps_chain (α : MulAut PSL(3,F))
    (f : ∀ (i j : Fin 3), i ≠ j → F → F)
    (hf : ∀ i j hij a, α (rootElement hij a) = rootElement hij (f i j hij a))
    {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : F) :
    f i k hik (a*b) = f i j hij a * f j k hjk b := by
  have h := congrArg α (rootElement_chain hij hjk hik a b)
  simp only [map_mul,hf] at h
  have h' := (rootElement_chain hij hjk hik (f i j hij a) (f j k hjk b)).symm.trans h
  exact (rootElement_injective hik (mul_left_cancel (mul_right_cancel h'))).symm

private theorem normalized_root_maps_eq (f : ∀ (i j : Fin 3), i ≠ j → F → F)
    (h1 : ∀ i j hij, f i j hij 1 = 1)
    (hc : ∀ i j k hij hjk hik a b,
      f i k hik (a*b) = f i j hij a * f j k hjk b) :
    ∀ i j hij a, f i j hij a = f 0 1 (by decide) a := by
  have hl (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a : F) :
      f i k hik a = f i j hij a := by simpa only [mul_one,h1] using hc i j k hij hjk hik a 1
  have hr (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a : F) :
      f i k hik a = f j k hjk a := by simpa only [one_mul,h1] using hc i j k hij hjk hik 1 a
  intro i j hij a
  have h02 := hl 0 1 2 (by decide) (by decide) (by decide) a
  have h12 := hr 0 1 2 (by decide) (by decide) (by decide) a
  have h10 := hl 1 0 2 (by decide) (by decide) (by decide) a
  have h20 := hr 2 0 1 (by decide) (by decide) (by decide) a
  have h21 := hl 2 0 1 (by decide) (by decide) (by decide) a
  fin_cases i <;> fin_cases j
  all_goals try exact (hij rfl).elim
  all_goals grind

private theorem eq_fieldAction_of_fixes_root_ones (α : MulAut PSL(3,F))
    (hα : PreservesRootGroups α)
    (h1 : ∀ (i j : Fin 3) (hij : i ≠ j), α (rootElement hij 1) = rootElement hij 1) :
    ∃ σ : F ≃+* F, α = fieldAction F σ := by
  obtain ⟨f,hf,hbij⟩ := exists_root_maps α hα
  have hf1 (i j : Fin 3) (hij : i ≠ j) : f i j hij 1 = 1 :=
    rootElement_injective hij ((hf i j hij 1).symm.trans (h1 i j hij))
  have hc := fun i j k hij hjk hik a b => root_maps_chain α f hf (i:=i) (j:=j) (k:=k) hij hjk hik a b
  have he := normalized_root_maps_eq f hf1 hc
  let σ : F ≃+* F :=
    { Equiv.ofBijective (f 0 1 (by decide)) (hbij 0 1 (by decide)) with
      map_mul' := by
        intro a b
        change f 0 1 _ (a*b) = f 0 1 _ a * f 0 1 _ b
        have h := hc 0 1 2 (by decide) (by decide) (by decide) a b
        simpa only [he] using h
      map_add' := by
        intro a b
        change f 0 1 _ (a+b) = f 0 1 _ a + f 0 1 _ b
        apply rootElement_injective (show (0:Fin 3) ≠ 1 by decide)
        rw [← hf, rootElement_add, map_mul, hf, hf, ← rootElement_add] }
  refine ⟨σ,?_⟩
  apply MulEquiv.toMonoidHom_injective
  apply hom_ext
  intro i j hij a
  change α (rootElement hij a) = fieldAction F σ (rootElement hij a)
  rw [hf,he]
  change rootElement hij (σ a) = fieldAction F σ (rootElement hij a)
  simp only [rootElement, fieldAction_mk]
  apply congrArg (QuotientGroup.mk : SL(3,F) → PSL(3,F))
  apply Subtype.ext
  ext r s
  simp [SpecialLinearGroup.map_apply_coe, SpecialLinearGroup.transvection_coe,
    Matrix.single_apply, Matrix.one_apply, apply_ite σ]

private theorem diagonal_preservesRootGroups (d : Fin 3 → Fˣ) :
    PreservesRootGroups (linearConj F (diagonalGL d)) := by
  intro i j hij
  apply le_antisymm
  · rintro _ ⟨_,⟨a,rfl⟩,rfl⟩
    change linearConj F (diagonalGL d) (rootElement hij a.toAdd) ∈ rootGroup hij
    rw [linearConj_diagonalGL_rootElement]
    exact rootElement_mem hij _
  · rintro _ ⟨a,rfl⟩
    refine ⟨rootElement hij (a.toAdd * (d j : F) * ((d i)⁻¹ : Fˣ)), rootElement_mem hij _, ?_⟩
    change linearConj F (diagonalGL d) (rootElement hij _) = rootElement hij a.toAdd
    rw [linearConj_diagonalGL_rootElement]
    congr 1
    simp [mul_comm,mul_left_comm]

/-- Root-preserving automorphisms have actual diagonal and coefficient-field factors. -/
theorem eq_diagonal_field_of_preservesRootGroups (α : MulAut PSL(3,F))
    (hα : PreservesRootGroups α) :
    ∃ (d : Fin 3 → Fˣ) (σ : F ≃+* F),
      α = linearConj F (diagonalGL d) * fieldAction F σ := by
  choose c hc using fun i j hij => exists_root_scalar α hα (i := i) (j := j) hij
  obtain ⟨d,hd⟩ := root_scalars_diagonal c
    (fun _ _ _ hij hjk hik => root_scalar_chain α c hc hij hjk hik)
  let δ := linearConj F (diagonalGL d)
  let β := δ⁻¹ * α
  have hδ : PreservesRootGroups δ := diagonal_preservesRootGroups d
  have hβ : PreservesRootGroups β := by
    intro i j hij
    change (rootGroup hij).map (δ.symm.toMonoidHom.comp α.toMonoidHom) = rootGroup hij
    rw [← Subgroup.map_map, hα]
    exact (Subgroup.map_symm_eq_iff_map_eq (rootGroup hij) (e := δ)).mpr (hδ i j hij)
  have h1 (i j : Fin 3) (hij : i ≠ j) : β (rootElement hij 1) = rootElement hij 1 := by
    apply δ.injective
    change δ (δ.symm (α (rootElement hij 1))) = δ (rootElement hij 1)
    rw [δ.apply_symm_apply, hc]
    change rootElement hij (c i j hij : F) = linearConj F (diagonalGL d) (rootElement hij 1)
    rw [linearConj_diagonalGL_rootElement, hd, Units.val_mul, one_mul]
  obtain ⟨σ,hσ⟩ := eq_fieldAction_of_fixes_root_ones β hβ h1
  refine ⟨d,σ,?_⟩
  have he := congrArg (fun a : MulAut PSL(3,F) => δ * a) hσ
  simpa only [β,mul_inv_cancel_left] using he

/-- The concrete standard subgroup contains every root-preserving automorphism,
over any field. -/
theorem mem_standard_of_preservesRootGroups (α : MulAut PSL(3,F))
    (hα : PreservesRootGroups α) : α ∈ standard F := by
  obtain ⟨d,σ,rfl⟩ := eq_diagonal_field_of_preservesRootGroups α hα
  exact (standard F).mul_mem (linearConj_mem_standard F _) (fieldAction_mem_standard F _)

end Matrix.PSL3Even.AutomorphismCoverage
