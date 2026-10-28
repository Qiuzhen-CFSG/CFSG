module
public import Theory.Representation.BinaryAlternatingSevenControl.TensorFixedObstruction
public import Theory.Representation.BinaryPermutation.SevenParabolic.Extension
/-!
# A five-free fixed kernel for a normal deleted-seven actor

The actual faithful actor embeds in S7 with its A7 marking preserved.
Extend its original Sylow image to a Sylow of S7. Vectors fixed by the
larger Sylow are still fixed by the original one, so the native five-free
fixed-kernel bound applies without assuming that the actor equals S7.
Source application: Aschbacher--Smith 5.1.13, printed p.637.
-/
public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryAlternatingSevenControl
variable {D V : Type*} [Group D]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- Any faithful normal extension of the original deleted A7 action has a
five-free kernel on its Sylow-fixed space, with both original maps retained. -/
theorem natural_actor_sylow_fixedKernel_five_free
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (N : Subgroup D) [N.Normal] (eN : N ≃* alternatingGroup (Fin 7))
    (eV : V ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 7))
    (he : ∀ (x : N) v, eV (ρ x.val v) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 7) (eN x) (eV v))
    (P : Sylow 2 D) (B : Subgroup D)
    (hB : ∀ b ∈ B, ∀ v ∈ fixedSpace ρ P, ρ b v = v) : ¬5 ∣ Nat.card B := by
  let c := BinaryPermutation.coreEquivNatural (Fin 7) (by decide)
  let l := eV.trans c.symm
  have he' : ∀ (x : N) v, l (ρ x.val v) =
      BinaryPermutation.alternatingCoreRepresentation (Fin 7) (eN x) (l v) := by
    intro x v
    apply c.injective
    change c (c.symm (eV (ρ x.val v))) =
      c (BinaryPermutation.coreRepresentation (Fin 7) (eN x).val (l v))
    rw [c.apply_symm_apply,BinaryPermutation.coreEquivNatural_equivariant]
    change eV (ρ x.val v) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 7) (eN x) (c (c.symm (eV v)))
    rw [c.apply_symm_apply]
    exact he x v
  obtain ⟨f,hfi,_,hact⟩ := BinaryPermutation.SevenParabolic.faithful_extension N ρ hf eN l he'
  obtain ⟨R,hR⟩ := (P.isPGroup'.map f).exists_le_sylow
  have hh := BinaryPermutation.SevenSylowFixed.sylow_fixedKernel_five_free R (B.map f) (by
    rintro _ ⟨b,hb,rfl⟩ v hv
    obtain ⟨w,rfl⟩ := l.surjective v
    have hw : w ∈ fixedSpace ρ P := by
      intro p
      apply l.injective
      change l (ρ p.val w) = l w
      rw [hact]
      exact hv ⟨f p.val,hR (mem_map_of_mem f p.property)⟩
    exact (hact b w).symm.trans (congrArg l (hB b hb w hw)))
  rwa [card_map_of_injective hfi] at hh
end Representation.BinaryAlternatingSevenControl
