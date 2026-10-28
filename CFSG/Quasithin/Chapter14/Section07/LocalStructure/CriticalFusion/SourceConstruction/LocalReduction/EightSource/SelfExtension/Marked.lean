module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension.BlockSplitting
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension.CoreSplitting

/-!
# Splitting extensions with an arbitrary symmetric-eight marking

The concrete symmetric-eight calculations apply to a representation of any
group identified with S₈. Pulling the action back along this identification
keeps its specified submodule and quotient. The resulting natural product
coordinates and augmentation-core retraction intertwine the original action.

Source: Aschbacher–Smith 14.7.51, printed p.1065.
-/

public noncomputable section
open Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]

private abbrev markedSubrepresentation (ρ : Representation (ZMod 2) H W)
    (X : Subrepresentation ρ) (eH : H ≃* Equiv.Perm (Fin 8)) :
    Subrepresentation (ρ.comp eH.symm.toMonoidHom) where
  toSubmodule := X.toSubmodule
  apply_mem_toSubmodule g _ hx := X.apply_mem_toSubmodule (eH.symm g) hx

/-- A natural self-extension with a transposition moving at most two dimensions
is a direct sum of two natural modules, with the supplied group marking. -/
theorem natural_pair_equiv
    (ρ : Representation (ZMod 2) H W) (X : Subrepresentation ρ)
    (eH : H ≃* Equiv.Perm (Fin 8))
    (eX : X.toSubmodule ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8))
    (eQ : (W ⧸ X.toSubmodule) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8))
    (heX : ∀ g x, eX (X.toRepresentation g x) =
      BinaryPermutation.naturalRepresentation (Fin 8) (eH g) (eX x))
    (heQ : ∀ g x, eQ (X.quotientRepresentation g x) =
      BinaryPermutation.naturalRepresentation (Fin 8) (eH g) (eQ x))
    (t : H) (ht : (eH t).IsSwap)
    (hr : Module.finrank (ZMod 2) (ρ t-LinearMap.id).range ≤ 2) :
    ∃ E : W ≃ₗ[ZMod 2]
      (BinaryPermutation.natural (Fin 8) × BinaryPermutation.natural (Fin 8)),
      ∀ g w, E (ρ g w) =
        (BinaryPermutation.naturalRepresentation (Fin 8) (eH g) (E w).1,
         BinaryPermutation.naturalRepresentation (Fin 8) (eH g) (E w).2) := by
  let ρ' := ρ.comp eH.symm.toMonoidHom
  let X' := markedSubrepresentation ρ X eH
  have hX : ∀ g x, (eX.trans eNatural) (X'.toRepresentation g x) =
      naturalSix g ((eX.trans eNatural) x) := by
    intro g x
    change eNatural (eX (X.toRepresentation (eH.symm g) x)) = _
    rw [heX,eH.apply_symm_apply,eNatural_equivariant]
    rfl
  have hQ : ∀ g x, (eQ.trans eNatural) (X'.quotientRepresentation g x) =
      naturalSix g ((eQ.trans eNatural) x) := by
    intro g x
    change eNatural (eQ (X.quotientRepresentation (eH.symm g) x)) = _
    rw [heQ,eH.apply_symm_apply,eNatural_equivariant]
    rfl
  obtain ⟨s⟩ := exists_section_data ρ' X' naturalSix naturalSix
    (eX.trans eNatural) (eQ.trans eNatural) hX hQ
  have hr' : Module.finrank (ZMod 2) (ρ' (eH t)-LinearMap.id).range ≤ 2 := by
    change Module.finrank (ZMod 2) (ρ (eH.symm (eH t))-LinearMap.id).range ≤ 2
    rw [eH.symm_apply_apply]
    exact hr
  obtain ⟨K,hK,eK,heK⟩ := s.natural_complement (eH t) ht hr'
  have hX' : ∀ g x, eX (X'.toRepresentation g x) =
      BinaryPermutation.naturalRepresentation (Fin 8) g (eX x) := by
    intro g x
    change eX (X.toRepresentation (eH.symm g) x) = _
    rw [heX,eH.apply_symm_apply]
  have hK' : ∀ g x, (eK.trans eNatural.symm) (K.toRepresentation g x) =
      BinaryPermutation.naturalRepresentation (Fin 8) g ((eK.trans eNatural.symm) x) := by
    intro g x
    apply eNatural.injective
    change eNatural (eNatural.symm (eK (K.toRepresentation g x))) = _
    rw [eNatural.apply_symm_apply,eNatural_equivariant]
    change eK (K.toRepresentation g x) = naturalSix g (eNatural (eNatural.symm (eK x)))
    rw [eNatural.apply_symm_apply,heK]
  obtain ⟨E,hE⟩ := equiv_prod_of_complement ρ' X' K hK
    (BinaryPermutation.naturalRepresentation (Fin 8))
    (BinaryPermutation.naturalRepresentation (Fin 8)) eX (eK.trans eNatural.symm) hX' hK'
  refine ⟨E,?_⟩
  intro g w
  have hh := hE (eH g) w
  change E (ρ (eH.symm (eH g)) w) =
    (BinaryPermutation.naturalRepresentation (Fin 8) (eH g) (E w).1,
     BinaryPermutation.naturalRepresentation (Fin 8) (eH g) (E w).2) at hh
  simpa only [eH.symm_apply_apply] using hh

/-- A core-by-natural extension has a surjective equivariant map onto its
specified augmentation-core constituent, under the supplied group marking. -/
theorem core_surjective_retraction
    (ρ : Representation (ZMod 2) H W) (X : Subrepresentation ρ)
    (eH : H ≃* Equiv.Perm (Fin 8))
    (eX : X.toSubmodule ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 8))
    (eQ : (W ⧸ X.toSubmodule) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8))
    (heX : ∀ g x, eX (X.toRepresentation g x) =
      BinaryPermutation.coreRepresentation (Fin 8) (eH g) (eX x))
    (heQ : ∀ g x, eQ (X.quotientRepresentation g x) =
      BinaryPermutation.naturalRepresentation (Fin 8) (eH g) (eQ x)) :
    ∃ p : W →ₗ[ZMod 2] BinaryPermutation.core (Fin 8),
      Function.Surjective p ∧ ∀ g w, p (ρ g w) =
        BinaryPermutation.coreRepresentation (Fin 8) (eH g) (p w) := by
  let ρ' := ρ.comp eH.symm.toMonoidHom
  let X' := markedSubrepresentation ρ X eH
  have hX : ∀ g x, (eX.trans eCore) (X'.toRepresentation g x) =
      coreSeven g ((eX.trans eCore) x) := by
    intro g x
    change eCore (eX (X.toRepresentation (eH.symm g) x)) = _
    rw [heX,eH.apply_symm_apply,eCore_equivariant]
    rfl
  have hQ : ∀ g x, (eQ.trans eNatural) (X'.quotientRepresentation g x) =
      naturalSix g ((eQ.trans eNatural) x) := by
    intro g x
    change eNatural (eQ (X.quotientRepresentation (eH.symm g) x)) = _
    rw [heQ,eH.apply_symm_apply,eNatural_equivariant]
    rfl
  obtain ⟨s⟩ := exists_section_data ρ' X' coreSeven naturalSix
    (eX.trans eCore) (eQ.trans eNatural) hX hQ
  obtain ⟨K,hK,eK,heK⟩ := s.core_complement
  have hX' : ∀ g x, eX (X'.toRepresentation g x) =
      BinaryPermutation.coreRepresentation (Fin 8) g (eX x) := by
    intro g x
    change eX (X.toRepresentation (eH.symm g) x) = _
    rw [heX,eH.apply_symm_apply]
  have hK' : ∀ g x, (eK.trans eNatural.symm) (K.toRepresentation g x) =
      BinaryPermutation.naturalRepresentation (Fin 8) g ((eK.trans eNatural.symm) x) := by
    intro g x
    apply eNatural.injective
    change eNatural (eNatural.symm (eK (K.toRepresentation g x))) = _
    rw [eNatural.apply_symm_apply,eNatural_equivariant]
    change eK (K.toRepresentation g x) = naturalSix g (eNatural (eNatural.symm (eK x)))
    rw [eNatural.apply_symm_apply,heK]
  obtain ⟨p,hp,hpe⟩ := surjective_retraction_of_complement ρ' X' K hK
    (BinaryPermutation.coreRepresentation (Fin 8))
    (BinaryPermutation.naturalRepresentation (Fin 8)) eX (eK.trans eNatural.symm) hX' hK'
  refine ⟨p,hp,?_⟩
  intro g w
  simpa only [ρ',MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
    eH.symm_apply_apply] using hpe (eH g) w

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension
