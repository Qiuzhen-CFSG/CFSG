module
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.Representation.BinaryOffender.ComponentSum

/-!
# Constant kernels in six-letter augmentation movement

The all-one vector spanning the augmentation-to-natural kernel is the sum
of three displacements by even double transpositions. Consequently the kernel
lies in the even moved space of the three-pair actor and every conjugate.
A compatible surjective cover transports this containment to its actual
natural quotient kernel, retaining the supplied group marking.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.3.2–4, printed pp.83–85; application to MS93 (3.6), printed p.871.
-/

public section
open Representation Representation.BinaryOffender
namespace BinaryPermutation.SixCover

private def coreOne : core (Fin 6) :=
  ⟨allOne (Fin 6), by change (∑ _ : Fin 6, (1 : ZMod 2)) = 0; decide⟩

private def corePair (i j : Fin 6) : core (Fin 6) :=
  ⟨Pi.single i 1 + Pi.single j 1, by
    simp [mem_core, Finset.sum_add_distrib, CharTwo.add_self_eq_zero]⟩

private theorem coreOne_displacements :
    coreOne =
      (coreRepresentation (Fin 6) (Equiv.swap 0 1 * Equiv.swap 2 3) (corePair 0 4) -
        corePair 0 4) +
      (coreRepresentation (Fin 6) (Equiv.swap 0 1 * Equiv.swap 2 3) (corePair 2 4) -
        corePair 2 4) +
      (coreRepresentation (Fin 6) (Equiv.swap 0 1 * Equiv.swap 4 5) (corePair 4 2) -
        corePair 4 2) := by
  apply Subtype.ext
  funext i
  fin_cases i <;> decide

private theorem kernel_le_of_coreOne {W : Submodule (ZMod 2) (core (Fin 6))}
    (hW : coreOne ∈ W) : (coreToNatural (Fin 6)).ker ≤ W := by
  intro v hv
  have hc : v.val ∈ constants (Fin 6) := by
    change coreToNatural (Fin 6) v = 0 at hv
    rw [← Subtype.val_inj] at hv
    exact (Submodule.Quotient.mk_eq_zero _).mp hv
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hc
  have he : c • coreOne = v := Subtype.ext hc
  rw [←he]
  exact W.smul_mem c hW

/-- The constant kernel is moved by the even part of any actor containing
the three disjoint pair swaps. -/
theorem kernel_le_even_moved_of_pairSwaps (E : Subgroup (Equiv.Perm (Fin 6)))
    (h01 : Equiv.swap 0 1 ∈ E) (h23 : Equiv.swap 2 3 ∈ E)
    (h45 : Equiv.swap 4 5 ∈ E) :
    (coreToNatural (Fin 6)).ker ≤
      subspaceCommutator (coreRepresentation (Fin 6)) ⊤ (E ⊓ alternatingGroup (Fin 6)) := by
  apply kernel_le_of_coreOne
  have h1 : Equiv.swap (0 : Fin 6) 1 * Equiv.swap 2 3 ∈
      E ⊓ alternatingGroup (Fin 6) := ⟨E.mul_mem h01 h23, by
        change Equiv.Perm.sign _ = 1; decide⟩
  have h2 : Equiv.swap (0 : Fin 6) 1 * Equiv.swap 4 5 ∈
      E ⊓ alternatingGroup (Fin 6) := ⟨E.mul_mem h01 h45, by
        change Equiv.Perm.sign _ = 1; decide⟩
  rw [coreOne_displacements]
  exact Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.subset_span ⟨_,h1,_,Submodule.mem_top,rfl⟩)
    (Submodule.subset_span ⟨_,h1,_,Submodule.mem_top,rfl⟩))
    (Submodule.subset_span ⟨_,h2,_,Submodule.mem_top,rfl⟩)

/-- Conjugating the actor preserves kernel containment in even movement. -/
theorem kernel_le_even_moved_conjugate (E : Subgroup (Equiv.Perm (Fin 6)))
    (g : Equiv.Perm (Fin 6))
    (hE : (coreToNatural (Fin 6)).ker ≤
      subspaceCommutator (coreRepresentation (Fin 6)) ⊤ (E ⊓ alternatingGroup (Fin 6))) :
    (coreToNatural (Fin 6)).ker ≤
      subspaceCommutator (coreRepresentation (Fin 6)) ⊤
        (E.map (MulAut.conj g).toMonoidHom ⊓ alternatingGroup (Fin 6)) := by
  apply kernel_le_of_coreOne
  have hc : coreOne ∈ (coreToNatural (Fin 6)).ker := by
    change coreToNatural (Fin 6) coreOne = 0
    rw [←Subtype.val_inj]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Submodule.subset_span (by simp [coreOne])
  have hh : coreRepresentation (Fin 6) g coreOne ∈
      (subspaceCommutator (coreRepresentation (Fin 6)) ⊤
        (E ⊓ alternatingGroup (Fin 6))).map (coreRepresentation (Fin 6) g) :=
    ⟨coreOne,hE hc,rfl⟩
  have hg : coreRepresentation (Fin 6) g coreOne = coreOne :=
    Subtype.ext (permute_allOne (Fin 6) g)
  rw [hg,moved_map_conjugate] at hh
  apply (show subspaceCommutator (coreRepresentation (Fin 6)) ⊤
      ((E ⊓ alternatingGroup (Fin 6)).map (MulAut.conj g).toMonoidHom) ≤
      subspaceCommutator (coreRepresentation (Fin 6)) ⊤
        (E.map (MulAut.conj g).toMonoidHom ⊓ alternatingGroup (Fin 6)) from ?_) hh
  apply Submodule.span_mono
  rintro _ ⟨_,⟨a,ha,rfl⟩,v,hv,rfl⟩
  refine ⟨_,⟨Subgroup.mem_map_of_mem _ ha.1,?_⟩,v,hv,rfl⟩
  exact Subgroup.Normal.conj_mem inferInstance a ha.2 g

/-- A surjective equivariant cover carries the model kernel containment to
the literal kernel of its compatible natural quotient. -/
theorem kernel_le_moved_of_surjective_cover
    {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (e : H →* Equiv.Perm (Fin 6))
    (B : Subgroup H) (f : core (Fin 6) →ₗ[ZMod 2] U) (hf : Function.Surjective f)
    (he : ∀ g v, f (coreRepresentation (Fin 6) (e g) v) = ρ g (f v))
    (p : U →ₗ[ZMod 2] natural (Fin 6))
    (hp : ∀ v, p (f v) = coreToNatural (Fin 6) v)
    (hmodel : (coreToNatural (Fin 6)).ker ≤
      subspaceCommutator (coreRepresentation (Fin 6)) ⊤ (B.map e)) :
    p.ker ≤ subspaceCommutator ρ ⊤ B := by
  intro u hu
  obtain ⟨v,rfl⟩ := hf u
  have hv : v ∈ (coreToNatural (Fin 6)).ker := by
    change coreToNatural (Fin 6) v = 0
    rw [←hp]
    exact hu
  have hm := subspaceCommutator_map_embedding ρ (coreRepresentation (Fin 6))
    e f (fun g v => (he g v).symm) B ⊤
  rw [Submodule.map_top,LinearMap.range_eq_top.mpr hf] at hm
  rw [hm]
  exact ⟨v,hmodel hv,rfl⟩
end BinaryPermutation.SixCover
