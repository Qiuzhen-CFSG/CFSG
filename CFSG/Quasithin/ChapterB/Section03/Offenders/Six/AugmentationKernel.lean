module
public import Theory.Representation.BinaryPermutationSixCover.OffenderKernel
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Structure.Reduction
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Dimensions

/-!
# Augmentation kernels for the order-eight natural offenders

The two maximal elementary classes in degree six are the three-pair actor
and the exceptional actor. Order eight forces equality after conjugation;
the exceptional actor has natural fixed codimension three, so codimension
two selects the three-pair class. Its even displacements contain the constant
kernel of the augmentation cover. The final theorems apply this fact to a
surjective marked cover with its literal compatible natural quotient.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.3.2–4, printed pp.83–85; application to MS93 (3.6), printed p.871.
-/

public section
open Representation Representation.BinaryOffender BinaryPermutation
namespace CFSG.Quasithin.ChapterB.Offenders.Six

/-- An elementary actor of order eight and natural fixed codimension two
moves the constant kernel already through its even part. -/
theorem augmentation_kernel_le_even_moved
    (E : Subgroup (Equiv.Perm (Fin 6))) [IsElementaryAbelian 2 E]
    (hcard : Nat.card E = 8)
    (hcodim : fixedCodim (naturalRepresentation (Fin 6)) E = 2) :
    (coreToNatural (Fin 6)).ker ≤
      subspaceCommutator (coreRepresentation (Fin 6)) ⊤ (E ⊓ alternatingGroup (Fin 6)) := by
  have hE : IsElementaryTwo E := ⟨by
    intro hz
    rw [hz,Subgroup.card_bot] at hcard
    omega, inferInstance⟩
  obtain ⟨B,_,hB,hconj⟩ := exists_conjugate_le_D_or_exceptional hE
  have hcardB : Nat.card B = 8 := hconj.card_eq.symm.trans hcard
  rcases hB with hB | hB
  · have hBD : B = D 6 := Subgroup.eq_of_le_of_card_ge hB (by
      rw [hcardB]
      exact (card_disjointTranspositions 3).le)
    subst B
    obtain ⟨g,rfl⟩ := hconj
    apply SixCover.kernel_le_even_moved_conjugate
    exact SixCover.kernel_le_even_moved_of_pairSwaps (D 6)
      (pairSwap_mem 0 (by decide)) (pairSwap_mem 1 (by decide))
      (pairSwap_mem 2 (by decide))
  · have hBX : B = exceptional 6 (by decide) := Subgroup.eq_of_le_of_card_ge hB (by
      rw [hcardB,card_exceptional])
    subst B
    obtain ⟨g,rfl⟩ := hconj
    rw [fixedCodim_map_conj,fixedCodim_exceptional.2.2.2] at hcodim
    omega

/-- The same actor moves the constant kernel without restricting to its
even part. -/
theorem augmentation_kernel_le_moved
    (E : Subgroup (Equiv.Perm (Fin 6))) [IsElementaryAbelian 2 E]
    (hcard : Nat.card E = 8)
    (hcodim : fixedCodim (naturalRepresentation (Fin 6)) E = 2) :
    (coreToNatural (Fin 6)).ker ≤ subspaceCommutator (coreRepresentation (Fin 6)) ⊤ E := by
  apply (augmentation_kernel_le_even_moved E hcard hcodim).trans
  apply Submodule.span_mono
  rintro _ ⟨g,hg,v,hv,rfl⟩
  exact ⟨g,hg.1,v,hv,rfl⟩

/-- Actual cover application: under the supplied marking, the compatible
natural quotient kernel is moved by the even preimage in the original actor.
The cover and marking are furnished by the natural-section recognition. -/
theorem cover_kernel_le_even_moved
    {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (e : H →* Equiv.Perm (Fin 6))
    (B : Subgroup H) [IsElementaryAbelian 2 (B.map e)]
    (hcard : Nat.card (B.map e) = 8)
    (hcodim : fixedCodim (naturalRepresentation (Fin 6)) (B.map e) = 2)
    (f : core (Fin 6) →ₗ[ZMod 2] U) (hf : Function.Surjective f)
    (he : ∀ g v, f (coreRepresentation (Fin 6) (e g) v) = ρ g (f v))
    (p : U →ₗ[ZMod 2] natural (Fin 6))
    (hp : ∀ v, p (f v) = coreToNatural (Fin 6) v) :
    p.ker ≤ subspaceCommutator ρ ⊤ (B ⊓ (alternatingGroup (Fin 6)).comap e) := by
  apply SixCover.kernel_le_moved_of_surjective_cover ρ e _ f hf he p hp
  have hm : (B ⊓ (alternatingGroup (Fin 6)).comap e).map e =
      B.map e ⊓ alternatingGroup (Fin 6) := by
    ext g
    constructor
    · rintro ⟨b,hb,rfl⟩
      exact ⟨Subgroup.mem_map_of_mem e hb.1,hb.2⟩
    · rintro ⟨⟨b,hb,rfl⟩,heven⟩
      exact ⟨b,⟨hb,heven⟩,rfl⟩
  rw [hm]
  exact augmentation_kernel_le_even_moved (B.map e) hcard hcodim

/-- The literal cover kernel lies in movement by the original actor. -/
theorem cover_kernel_le_moved
    {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (e : H →* Equiv.Perm (Fin 6))
    (B : Subgroup H) [IsElementaryAbelian 2 (B.map e)]
    (hcard : Nat.card (B.map e) = 8)
    (hcodim : fixedCodim (naturalRepresentation (Fin 6)) (B.map e) = 2)
    (f : core (Fin 6) →ₗ[ZMod 2] U) (hf : Function.Surjective f)
    (he : ∀ g v, f (coreRepresentation (Fin 6) (e g) v) = ρ g (f v))
    (p : U →ₗ[ZMod 2] natural (Fin 6))
    (hp : ∀ v, p (f v) = coreToNatural (Fin 6) v) :
    p.ker ≤ subspaceCommutator ρ ⊤ B :=
  SixCover.kernel_le_moved_of_surjective_cover ρ e B f hf he p hp
    (augmentation_kernel_le_moved (B.map e) hcard hcodim)
end CFSG.Quasithin.ChapterB.Offenders.Six
