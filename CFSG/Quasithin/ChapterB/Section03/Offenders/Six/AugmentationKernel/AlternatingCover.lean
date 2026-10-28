module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.AugmentationKernel

/-!
# Even movement through an alternating-equivariant cover

The universal six-letter cover is equivariant for the alternating component.
This is enough to transport the constant kernel: its model displacement lies
in the even actor, and every automorphism of S6 preserves A6. The supplied
cover, natural quotient and marking are retained throughout. These adapters
consume the cover furnished by the natural-section recognition in MS93 (3.6).

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, B.3.2–4,
printed pp.83–85, and I.1.5–6, printed p.408; MS93 (3.6), printed p.871.
-/

public section
open Representation Representation.BinaryOffender BinaryPermutation
namespace CFSG.Quasithin.ChapterB.Offenders.Six

/-- Alternating equivariance suffices for the literal compatible cover kernel:
every marking automorphism preserves the alternating subgroup. -/
theorem alternating_cover_kernel_le_even_moved
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) U)
    (e : Equiv.Perm (Fin 6) ≃* Equiv.Perm (Fin 6))
    (E : Subgroup (Equiv.Perm (Fin 6))) [IsElementaryAbelian 2 E]
    (hcard : Nat.card E = 8)
    (hcodim : fixedCodim (naturalRepresentation (Fin 6)) (E.map e.toMonoidHom) = 2)
    (f : core (Fin 6) →ₗ[ZMod 2] U) (hf : Function.Surjective f)
    (he : ∀ g ∈ alternatingGroup (Fin 6), ∀ v,
      f (coreRepresentation (Fin 6) (e g) v) = ρ g (f v))
    (p : U →ₗ[ZMod 2] natural (Fin 6))
    (hp : ∀ v, p (f v) = coreToNatural (Fin 6) v) :
    p.ker ≤ subspaceCommutator ρ ⊤ (E ⊓ alternatingGroup (Fin 6)) := by
  let : IsElementaryAbelian 2 (E.map e.toMonoidHom) := IsElementaryAbelian.map _
  have hcard' : Nat.card (E.map e.toMonoidHom) = 8 :=
    (Subgroup.card_map_of_injective e.injective).trans hcard
  have hmodel := augmentation_kernel_le_even_moved (E.map e.toMonoidHom) hcard' hcodim
  have hmap : subspaceCommutator (coreRepresentation (Fin 6)) ⊤
      (E.map e.toMonoidHom ⊓ alternatingGroup (Fin 6)) ≤
      (subspaceCommutator ρ ⊤ (E ⊓ alternatingGroup (Fin 6))).comap f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨_,⟨⟨g,hg,rfl⟩,hgeven⟩,v,_,rfl⟩
    have hge : g ∈ alternatingGroup (Fin 6) :=
      (Subgroup.characteristic_iff_comap_le.mp inferInstance e) hgeven
    change f (coreRepresentation (Fin 6) (e g) v - v) ∈
      subspaceCommutator ρ ⊤ (E ⊓ alternatingGroup (Fin 6))
    rw [map_sub,he g hge v]
    exact Submodule.subset_span ⟨g,⟨hg,hge⟩,f v,Submodule.mem_top,rfl⟩
  intro u hu
  obtain ⟨v,rfl⟩ := hf u
  apply hmap (hmodel ?_)
  change coreToNatural (Fin 6) v = 0
  rw [←hp]
  exact hu

/-- Consumer of the universal alternating cover: its kernel lies in movement
by the original order-eight actor, with no odd-equivariance premise. -/
theorem alternating_cover_kernel_le_moved
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) U)
    (e : Equiv.Perm (Fin 6) ≃* Equiv.Perm (Fin 6))
    (E : Subgroup (Equiv.Perm (Fin 6))) [IsElementaryAbelian 2 E]
    (hcard : Nat.card E = 8)
    (hcodim : fixedCodim (naturalRepresentation (Fin 6)) (E.map e.toMonoidHom) = 2)
    (f : core (Fin 6) →ₗ[ZMod 2] U) (hf : Function.Surjective f)
    (he : ∀ g ∈ alternatingGroup (Fin 6), ∀ v,
      f (coreRepresentation (Fin 6) (e g) v) = ρ g (f v))
    (p : U →ₗ[ZMod 2] natural (Fin 6))
    (hp : ∀ v, p (f v) = coreToNatural (Fin 6) v) :
    p.ker ≤ subspaceCommutator ρ ⊤ E := by
  apply (alternating_cover_kernel_le_even_moved ρ e E hcard hcodim f hf he p hp).trans
  apply Submodule.span_mono
  rintro _ ⟨g,hg,v,hv,rfl⟩
  exact ⟨g,hg.1,v,hv,rfl⟩
end CFSG.Quasithin.ChapterB.Offenders.Six
