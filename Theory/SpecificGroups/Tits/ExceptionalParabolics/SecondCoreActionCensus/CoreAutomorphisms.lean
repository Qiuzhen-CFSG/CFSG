module
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.SecondCoreActionCensus.CoreGenerators

/-!
# Constructing actual core automorphisms from two right transitions

Positive normal forms in s3 and s7 generate the literal second two-core.
A permutation of their 1024 indices that preserves the two right-generator
transitions therefore defines an automorphism, without assuming a presentation.
This constructor is used for the concrete outer-quotient generator lifts.
Source and marking: Parrott (1972), §5, p.683; see `CoreGenerators`.
-/

@[expose] public section
namespace Tits.ExceptionalParabolics.SecondCoreAction.CoreGenerators

noncomputable def equiv : Fin 1024 ≃ Core := Equiv.ofBijective coreNormalForm coreNormalForm_bijective

theorem equiv_apply (n : Fin 1024) : equiv n = coreNormalForm n := rfl

theorem normalForm_zero : coreNormalForm 0 = 1 := by
  rw [normal_form]
  simp

def pairGenerator : Fin 2 → Core := ![generator 2, generator 6]
def pairIndex : Fin 2 → Fin 1024 := ![4, 256]

theorem pairGenerator_eq (i : Fin 2) : pairGenerator i = coreNormalForm (pairIndex i) := by
  fin_cases i <;> rfl

theorem positive_generates : Submonoid.closure (Set.range pairGenerator) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨n,rfl⟩ := coreNormalForm_bijective.2 x
  let C := Submonoid.closure (Set.range pairGenerator)
  let a : C := ⟨generator 2, Submonoid.subset_closure ⟨0,rfl⟩⟩
  let b : C := ⟨generator 6, Submonoid.subset_closure ⟨1,rfl⟩⟩
  have he : ((normalFormWord a b n : C) : Core) = coreNormalForm n := by
    change C.subtype (normalFormWord a b n) = _
    rw [map_normalFormWord]
    exact normalFormWord_eq n
  exact he ▸ (normalFormWord a b n).property

/-- Right-generator transitions suffice to construct an automorphism on the
literal core, with the prescribed normal-form permutation. -/
noncomputable def ofTransitions
    (next : Fin 1024 → Fin 2 → Fin 1024)
    (hn : ∀ n i, coreNormalForm (next n i) = coreNormalForm n * pairGenerator i)
    (F : Fin 1024 → Fin 1024) (hF : Function.Bijective F) (h0 : F 0 = 0)
    (ht : ∀ n i, coreNormalForm (F (next n i)) =
      coreNormalForm (F n) * coreNormalForm (F (pairIndex i))) : MulAut Core := by
  let f : Core → Core := fun x => equiv (F (equiv.symm x))
  have hf (n : Fin 1024) : f (coreNormalForm n) = coreNormalForm (F n) := by
    change equiv (F (equiv.symm (equiv n))) = _
    rw [equiv.symm_apply_apply]
    rfl
  have hf0 : f 1 = 1 := by rw [← normalForm_zero,hf,h0,normalForm_zero]
  let m : Core →* Core := MonoidHom.ofClosureMEqTopRight f positive_generates hf0 (by
    rintro x _ ⟨i,rfl⟩
    obtain ⟨n,rfl⟩ := coreNormalForm_bijective.2 x
    rw [← hn,hf,pairGenerator_eq,hf,hf]
    exact ht n i)
  have hbi : Function.Bijective m := by
    change Function.Bijective (fun x => equiv (F (equiv.symm x)))
    exact equiv.bijective.comp (hF.comp equiv.symm.bijective)
  exact MulEquiv.ofBijective m hbi

theorem ofTransitions_apply
    (next : Fin 1024 → Fin 2 → Fin 1024)
    (hn : ∀ n i, coreNormalForm (next n i) = coreNormalForm n * pairGenerator i)
    (F : Fin 1024 → Fin 1024) (hF : Function.Bijective F) (h0 : F 0 = 0)
    (ht : ∀ n i, coreNormalForm (F (next n i)) =
      coreNormalForm (F n) * coreNormalForm (F (pairIndex i))) (n : Fin 1024) :
    ofTransitions next hn F hF h0 ht (coreNormalForm n) = coreNormalForm (F n) := by
  change equiv (F (equiv.symm (equiv n))) = _
  rw [equiv.symm_apply_apply]
  rfl

end Tits.ExceptionalParabolics.SecondCoreAction.CoreGenerators
