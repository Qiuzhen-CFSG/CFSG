module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.RemainingModels.Suzuki
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.RankTwo

/-!
# Exchanged natural components

The second summand is the first action pulled back along conjugation by t⁻¹,
where t is an actual element of the local normalizer. Cross-centralization and
the two-component orbit are retained as explicit kernel and subgroup equalities,
and transported to the literal central quotient. Each of its two Borel images
is specified separately. The concrete Suzuki and SL₂ calculations then imply
fixation of every Borel-fixed lift, without splitting the original extension.

Source: Aschbacher–Smith, 15.3.65(i), printed p.1152 and F.9.18(5)(iii),
printed pp.325–326. Occurrence of these modules remains with source restrictions.
-/

open Representation Representation.BinaryOffender Matrix
open BenderSuzuki BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.RemainingModels

section Pair
variable {D E X : Type*} [Group D] [Group E] [AddCommGroup X] [Module (ZMod 2) X]
    (σ : Representation (ZMod 2) E X) (K : Subgroup D) (t : Subgroup.normalizer (K : Set D))
    (φ : K →* E)

/-- The second summand is transported by the actual normalizing element t:
its action at g is the first summand's action at t⁻¹gt. -/
def exchangedAction : Representation (ZMod 2) K (X × X) :=
  Representation.prod (σ.comp φ) ((σ.comp φ).comp (K.normalizerMonoidHom t).symm.toMonoidHom)

/-- On the conjugate component the second summand has the original action. -/
theorem exchangedAction_conjugate (g : K) (x : X) :
    exchangedAction σ K t φ (K.normalizerMonoidHom t g) (0, x) = (0, σ (φ g) x) := by
  change (σ (φ (K.normalizerMonoidHom t g)) 0,
    σ (φ ((K.normalizerMonoidHom t).symm (K.normalizerMonoidHom t g))) x) = _
  simp

/-- Cross-centralization is retained explicitly. The return equality says
that t² normalizes the first component; the kernel premise is [I,Kᵗ]=0. -/
theorem exchangedAction_cross (C : Subgroup K)
    (hreturn : C.map (K.normalizerMonoidHom t).symm.toMonoidHom =
      C.map (K.normalizerMonoidHom t).toMonoidHom)
    (hcross : C.map (K.normalizerMonoidHom t).toMonoidHom ≤ φ.ker) :
    (∀ (g : C) (x : X), exchangedAction σ K t φ g.val (0, x) = (0, x)) ∧
    (∀ (g : C.map (K.normalizerMonoidHom t).toMonoidHom) (x : X),
      exchangedAction σ K t φ g.val (x, 0) = (x, 0)) := by
  constructor
  · intro g x
    have hg : (K.normalizerMonoidHom t).symm g.val ∈
        C.map (K.normalizerMonoidHom t).toMonoidHom := by
      rw [← hreturn]
      exact Subgroup.mem_map_of_mem _ g.property
    have hz : φ ((K.normalizerMonoidHom t).symm g.val) = 1 := hcross hg
    change (σ (φ g.val) 0, σ (φ ((K.normalizerMonoidHom t).symm g.val)) x) = _
    simp [hz]
  · intro g x
    have hz : φ g.val = 1 := hcross g.property
    change (σ (φ g.val) x, σ (φ ((K.normalizerMonoidHom t).symm g.val)) 0) = _
    simp [hz]

/-- Both Borel image equalities are literal; the second uses t⁻¹gt. -/
private theorem exchangedAction_fixedSpace_eq_bot (B : Subgroup K) (B' : Subgroup E)
    (hB : B.map φ = B')
    (hBt : B.map (φ.comp (K.normalizerMonoidHom t).symm.toMonoidHom) = B')
    (hzero : fixedSpace σ B' = ⊥) :
    fixedSpace (exchangedAction σ K t φ) B = ⊥ := by
  apply fixedSpace_prod_eq_bot
  · exact fixedSpace_eq_bot_of_equivariant _ σ φ (LinearEquiv.refl _ _)
      (fun _ _ => rfl) B B' hB hzero
  · exact fixedSpace_eq_bot_of_equivariant _ σ
      (φ.comp (K.normalizerMonoidHom t).symm.toMonoidHom)
      (LinearEquiv.refl _ _) (fun _ _ => rfl) B B' hBt hzero

end Pair

section SectionTransport
variable {D E V X : Type*} [Group D] [Group E]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup X] [Module (ZMod 2) X]

/-- The exchanged pair calculation on the literal central quotient. -/
private theorem exchanged_centralQuotient_fixed
    (σ : Representation (ZMod 2) E X) (B' : Subgroup E)
    (hzero : fixedSpace σ B' = ⊥)
    (ρ : Representation (ZMod 2) D V) (K B : Subgroup D)
    (I : Submodule (ZMod 2) V) (hI : K ≤ subspaceStabilizer ρ I)
    (t : Subgroup.normalizer (K : Set D)) (φ : K →* E)
    (e : centralQuotient ρ K I ≃ₗ[ZMod 2] (X × X))
    (he : ∀ g v, e (centralQuotientRepresentation ρ K I hI g v) =
      exchangedAction σ K t φ g (e v))
    (hB : (B.subgroupOf K).map φ = B')
    (hBt : (B.subgroupOf K).map
      (φ.comp (K.normalizerMonoidHom t).symm.toMonoidHom) = B') :
    I ⊓ fixedSpace ρ B ≤ fixedSpace ρ K := by
  apply inf_fixedSpace_le_of_centralQuotient ρ K B I hI
  exact fixedSpace_eq_bot_of_equivariant _ (exchangedAction σ K t φ)
    (MonoidHom.id K) e he _ _ (Subgroup.map_id _)
    (exchangedAction_fixedSpace_eq_bot σ K t φ _ B' hB hBt hzero)

/-- The same identification carries cross-centralization to the literal
quotient's two coordinate subspaces, rather than merely to a model-family tag. -/
theorem exchanged_centralQuotient_cross
    (σ : Representation (ZMod 2) E X)
    (ρ : Representation (ZMod 2) D V) (K : Subgroup D)
    (I : Submodule (ZMod 2) V) (hI : K ≤ subspaceStabilizer ρ I)
    (t : Subgroup.normalizer (K : Set D)) (φ : K →* E)
    (e : centralQuotient ρ K I ≃ₗ[ZMod 2] (X × X))
    (he : ∀ g v, e (centralQuotientRepresentation ρ K I hI g v) =
      exchangedAction σ K t φ g (e v))
    (C : Subgroup K)
    (hreturn : C.map (K.normalizerMonoidHom t).symm.toMonoidHom =
      C.map (K.normalizerMonoidHom t).toMonoidHom)
    (hcross : C.map (K.normalizerMonoidHom t).toMonoidHom ≤ φ.ker) :
    (∀ (g : C) (x : X), centralQuotientRepresentation ρ K I hI g.val
      (e.symm (0, x)) = e.symm (0, x)) ∧
    (∀ (g : C.map (K.normalizerMonoidHom t).toMonoidHom) (x : X),
      centralQuotientRepresentation ρ K I hI g.val (e.symm (x, 0)) = e.symm (x, 0)) := by
  have hc := exchangedAction_cross σ K t φ C hreturn hcross
  constructor
  · intro g x
    apply e.injective
    rw [he, e.apply_symm_apply, hc.1]
  · intro g x
    apply e.injective
    rw [he, e.apply_symm_apply, hc.2]

end SectionTransport
section ConcretePairs

/-- The concrete suzuki exchanged-component case on a literal central quotient.
The two Borel images and the actual normalizer conjugation are explicit. -/
theorem suzuki_exchanged_centralQuotient_fixed (m : ℕ) (hm : 0 < m)
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (K B : Subgroup D)
    (I : Submodule (ZMod 2) V) (hI : K ≤ subspaceStabilizer ρ I)
    (t : Subgroup.normalizer (K : Set D)) (φ : K →* SuzukiMatrixGroup m)
    (e : centralQuotient ρ K I ≃ₗ[ZMod 2] ((Fin 4 → BinaryGaloisField (2 * m + 1)) × (Fin 4 → BinaryGaloisField (2 * m + 1))))
    (he : ∀ g v, e (centralQuotientRepresentation ρ K I hI g v) =
      exchangedAction (suzukiNatural m) K t φ g (e v))
    (hB : (B.subgroupOf K).map φ = SuzukiBorelSubgroup m)
    (hBt : (B.subgroupOf K).map
      (φ.comp (K.normalizerMonoidHom t).symm.toMonoidHom) = SuzukiBorelSubgroup m) :
    I ⊓ fixedSpace ρ B ≤ fixedSpace ρ K :=
  exchanged_centralQuotient_fixed (suzukiNatural m) (SuzukiBorelSubgroup m)
    (suzuki_borel_fixedSpace_eq_bot m hm) ρ K B I hI t φ e he hB hBt

/-- The concrete slTwo exchanged-component case on a literal central quotient.
The two Borel images and the actual normalizer conjugation are explicit. -/
theorem slTwo_exchanged_centralQuotient_fixed {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
    (hF : 2 < Nat.card F)
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (K B : Subgroup D)
    (I : Submodule (ZMod 2) V) (hI : K ≤ subspaceStabilizer ρ I)
    (t : Subgroup.normalizer (K : Set D)) (φ : K →* SpecialLinearGroup (Fin 2) F)
    (e : centralQuotient ρ K I ≃ₗ[ZMod 2] ((Fin 2 → F) × (Fin 2 → F)))
    (he : ∀ g v, e (centralQuotientRepresentation ρ K I hI g v) =
      exchangedAction (restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 2)) K t φ g (e v))
    (hB : (B.subgroupOf K).map φ = Matrix.SpecialLinearGroup.rankOneBorel F)
    (hBt : (B.subgroupOf K).map
      (φ.comp (K.normalizerMonoidHom t).symm.toMonoidHom) = Matrix.SpecialLinearGroup.rankOneBorel F) :
    I ⊓ fixedSpace ρ B ≤ fixedSpace ρ K :=
  exchanged_centralQuotient_fixed (restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 2)) (Matrix.SpecialLinearGroup.rankOneBorel F)
    (slTwo_borel_fixedSpace_eq_bot hF) ρ K B I hI t φ e he hB hBt

end ConcretePairs

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.RemainingModels
