module
public import CFSG.Quasithin.Chapter6.Section01.SourceBasic
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.GroupTheory.PCoreLocalSetup
/-!
# The kernel of a faithfully marked conjugation module

The literal equivariance in a conjugation model identifies the component's
centralizer of the module with its two-core whenever the marked representation
is faithful. The alternating-five specialization uses the genuine deleted
permutation action. This is the detecting centralizer needed in the A5 row
of Aschbacher–Smith 13.7.4(1), printed p.937.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter6.Source
variable {G A X k : Type*} [Group G] [Group A] [AddCommGroup X]
  [Semiring k] [Module k X] {K I : Subgroup G} {ρ : Representation k A X}

/-- A faithful model detects exactly the intrinsic two-core. -/
theorem IsConjugationModel.centralizer_eq_core
    (h : IsConjugationModel K I ρ) (hρ : Function.Injective ρ) :
    K ⊓ centralizer (I : Set G) = K.pCoreIn 2 := by
  obtain ⟨e,f,hf⟩ := h
  apply le_antisymm
  · intro x hx
    let x' : K := ⟨x,hx.1⟩
    have ha : e (QuotientGroup.mk' (pCore 2 K) x') = 1 := by
      apply hρ
      rw [map_one]
      ext v
      have hv := hf x' (f.symm (Multiplicative.ofAdd v))
      have hc := mem_centralizer_iff.mp hx.2
        (f.symm (Multiplicative.ofAdd v)) (f.symm (Multiplicative.ofAdd v)).property
      have hh : f.symm (Multiplicative.ofAdd
          (ρ (e (QuotientGroup.mk' (pCore 2 K) x')) v)) =
          f.symm (Multiplicative.ofAdd v) := by
        apply Subtype.ext
        simpa only [MulEquiv.apply_symm_apply, toAdd_ofAdd] using
          hv.trans (mul_inv_eq_iff_eq_mul.mpr hc.symm)
      exact congrArg Multiplicative.toAdd (f.symm.injective hh)
    have hxcore : x' ∈ pCore 2 K := by
      apply (QuotientGroup.eq_one_iff _).mp
      exact e.injective (ha.trans (map_one e).symm)
    exact mem_map_of_mem K.subtype hxcore
  · rintro x ⟨x',hx',rfl⟩
    refine ⟨x'.property,?_⟩
    apply mem_centralizer_iff.mpr
    intro i hi
    have he : e (QuotientGroup.mk' (pCore 2 K) x') = 1 := by
      have hq : QuotientGroup.mk' (pCore 2 K) x' = 1 := (QuotientGroup.eq_one_iff x').mpr hx'
      rw [hq,map_one]
    have hh := hf x' ⟨i,hi⟩
    simp only [he,map_one,Module.End.one_apply,ofAdd_toAdd,
      MulEquiv.symm_apply_apply] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
/-- The genuine alternating-five module detects the component's two-core. -/
theorem IsConjugationModel.a5_centralizer_eq_core
    {G : Type*} [Group G] {K I : Subgroup G}
    (h : IsConjugationModel K I a5Module) :
    K ⊓ centralizer (I : Set G) = K.pCoreIn 2 :=
  h.centralizer_eq_core ((BinaryPermutation.naturalRepresentation_injective
    (Fin 5) (by decide)).comp (alternatingGroup (Fin 5)).subtype_injective)
end CFSG.Quasithin.Chapter6.Source
