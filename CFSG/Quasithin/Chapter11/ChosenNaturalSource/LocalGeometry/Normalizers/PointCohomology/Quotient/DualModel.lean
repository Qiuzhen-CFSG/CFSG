module
public import Theory.Representation.SymplecticFourOrthogonalCover.Universal
public import Theory.Representation.QuadraticDuality
public import Theory.Representation.SymplecticFourOrthogonalCover.Roots.Conjugates

/-!
# The actual dual orthogonal model for natural crossed homomorphisms

Binary self-duality carries natural cocycles to dual-natural cocycles. Dualizing
the universal orthogonal-cover equivalence identifies these with the dual
five-space. The principal layer is exactly the annihilator of the central
radical. Thus the model retains the correct dual action and its natural layer.

Source: Aschbacher–Smith I.2.3(1), used in 11.1.5, printed pp.413,766.
-/

public noncomputable section
open Representation Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- A functional fixed by the literal long root annihilates the central
radical of the orthogonal five-space. This is the dual, not the cover action. -/
theorem dual_root_fixed_annihilates_radical (hF : 2 < Nat.card F)
    (φ : Module.Dual (ZMod 2) (Space (K := F)))
    (hφ : ∀ g ∈ Roots.group, (binaryAction (K := F)).dual g φ = φ) :
    ∀ a : F, φ (0, a) = 0 := by
  have hf : φ ∈ (Representation.dual ((binaryAction (K := F)).comp Roots.group.subtype)).invariants := by
    intro g
    exact hφ g g.property
  rw [← dualAnnihilator_coinvariantsKer] at hf
  have hc : Coinvariants.ker ((binaryAction (K := F)).comp Roots.group.subtype) =
      (Roots.firstPreimage (K := F)).restrictScalars (ZMod 2) := by
    change Coinvariants.ker (restrictScalars (k := ZMod 2)
      ((action (K := F)).comp Roots.group.subtype)) = _
    rw [coinvariants_restrictScalars, Roots.root_commutator hF]
  rw [hc, Submodule.mem_dualAnnihilator] at hf
  intro a
  exact hf (0,a) ((Roots.mem_firstPreimage _).mpr ⟨0, zero_smul _ _⟩)

/-- The same calculation for every conjugate long root; the fixed central
radical itself is unchanged by conjugation. -/
theorem dual_conjugate_root_fixed_annihilates_radical (hF : 2 < Nat.card F)
    (g : Representation.SymplecticFourOrthogonalCover.L (K := F))
    (φ : Module.Dual (ZMod 2) (Space (K := F)))
    (hφ : ∀ r ∈ Roots.conjugateGroup g, (binaryAction (K := F)).dual r φ = φ) :
    ∀ a : F, φ (0, a) = 0 := by
  have hf : φ ∈ (Representation.dual ((binaryAction (K := F)).comp (Roots.conjugateGroup g).subtype)).invariants := by
    intro r
    exact hφ r r.property
  rw [← dualAnnihilator_coinvariantsKer, Submodule.mem_dualAnnihilator] at hf
  intro a
  apply hf (0,a)
  change (0,a) ∈ Coinvariants.ker (restrictScalars (k := ZMod 2)
    ((action (K := F)).comp (Roots.conjugateGroup g).subtype))
  rw [coinvariants_restrictScalars, ← (Roots.conjugate_root_geometry hF g).1]
  change (0 : Natural (K := F)) ∈ Roots.conjugateLine g
  exact Submodule.zero_mem _


namespace DualModel
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

local instance : Fintype (Representation.SymplecticFourOrthogonalCover.L (K := F)) :=
  Fintype.ofFinite _

local instance : FiniteDimensional (ZMod 2) (Natural (K := F)) :=
  Module.Finite.of_finite

local instance : FiniteDimensional (ZMod 2) (cocycles (binaryNatural (K := F)).dual) :=
  Module.Finite.of_injective (cocycles (binaryNatural (K := F)).dual).subtype Subtype.val_injective

private def t : cocycles (binaryNatural (K := F)) ≃ₗ[ZMod 2]
    cocycles (binaryNatural (K := F)).dual :=
  cocyclesCongr _ _ (MulEquiv.refl _) binarySelfDual (fun g v => binarySelfDual_equivariant g v)

private def e : Module.Dual (ZMod 2) (cocycles (binaryNatural (K := F)).dual) ≃ₗ[ZMod 2]
    Space (K := F) := (universal_equiv (K := F)).choose

private theorem e_intertwines (g : Representation.SymplecticFourOrthogonalCover.L (K := F))
    (u : Module.Dual (ZMod 2) (cocycles (binaryNatural (K := F)).dual)) :
    e ((universalAction (binaryNatural (K := F)).dual).dual g u) = binaryAction g (e u) :=
  (universal_equiv (K := F)).choose_spec.1 g u

private theorem e_projection (u : Module.Dual (ZMod 2) (cocycles (binaryNatural (K := F)).dual)) :
    binaryProjection (e u) = universalCoverProjection (binaryNatural (K := F)) u :=
  (universal_equiv (K := F)).choose_spec.2 u

/-- The cocycle module is the literal binary dual of the orthogonal five-space. -/
def equiv : cocycles (binaryNatural (K := F)) ≃ₗ[ZMod 2]
    Module.Dual (ZMod 2) (Space (K := F)) :=
  (t (F := F)).trans ((Module.evalEquiv (ZMod 2) _).trans (e (F := F)).symm.dualMap)

/-- Equivariance uses the contragredient action on the five-space. -/
theorem equiv_intertwines (g : Representation.SymplecticFourOrthogonalCover.L (K := F))
    (f : cocycles (binaryNatural (K := F))) :
    equiv (universalAction (binaryNatural (K := F)) g f) =
      (binaryAction (K := F)).dual g (equiv f) := by
  apply LinearMap.ext
  intro w
  have ht : t (universalAction (binaryNatural (K := F)) g f) =
      universalAction (binaryNatural (K := F)).dual g (t f) :=
    cocyclesCongr_universalAction (binarySelfDual (K := F)) (fun g v => binarySelfDual_equivariant g v) g f
  change (e (F := F)).symm w (t (universalAction (binaryNatural (K := F)) g f)) =
    (e (F := F)).symm (binaryAction g⁻¹ w) (t f)
  rw [ht]
  have he : (e (F := F)).symm (binaryAction g⁻¹ w) =
      (universalAction (binaryNatural (K := F)).dual).dual g⁻¹ ((e (F := F)).symm w) := by
    apply (e (F := F)).injective
    rw [LinearEquiv.apply_symm_apply,e_intertwines,LinearEquiv.apply_symm_apply]
  rw [he]
  change _ = (e (F := F)).symm w (universalAction (binaryNatural (K := F)).dual (g⁻¹)⁻¹ (t f))
  rw [inv_inv]

/-- Principal cocycles are the natural dual layer, over the original projection. -/
theorem equiv_principal (v : Natural (K := F)) :
    equiv (principal (binaryNatural (K := F)) v) =
      (binaryProjection (K := F)).toLinearMap.dualMap (binarySelfDual v) := by
  apply LinearMap.ext
  intro w
  have ht : t (principal (binaryNatural (K := F)) v) =
      principal (binaryNatural (K := F)).dual (binarySelfDual v) :=
    cocyclesCongr_principal _ _ _ _ _ _
  change (e (F := F)).symm w (t (principal (binaryNatural (K := F)) v)) =
    binarySelfDual v (binaryProjection w)
  rw [ht]
  have hp : binaryProjection w = universalCoverProjection (binaryNatural (K := F))
      ((e (F := F)).symm w) := by
    simpa only [LinearEquiv.apply_symm_apply] using e_projection ((e (F := F)).symm w)
  rw [hp]
  change _ = binarySelfDual v ((Module.evalEquiv (ZMod 2) (Natural (K := F))).symm
    (universalDualProjection (binaryNatural (K := F)).dual ((e (F := F)).symm w)))
  rw [Module.apply_evalEquiv_symm_apply]
  rfl

/-- Annihilating the original central radical is exactly membership in the natural layer. -/
theorem equiv_annihilates_radical_iff (f : cocycles (binaryNatural (K := F))) :
    (∀ a : F, equiv f (0,a) = 0) ↔ f ∈ (principal (binaryNatural (K := F))).range := by
  constructor
  · intro hf
    have ha : equiv f ∈ (binaryProjection (K := F)).toLinearMap.ker.dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro w hw
      have hw0 : w.1 = 0 := hw
      have hw : w = (0,w.2) := Prod.ext hw0 rfl
      rw [hw]
      exact hf w.2
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at ha
    obtain ⟨φ,hφ⟩ := ha
    obtain ⟨v,rfl⟩ := (binarySelfDual (K := F)).surjective φ
    exact ⟨v,(equiv (F := F)).injective ((equiv_principal v).trans hφ)⟩
  · rintro ⟨v,rfl⟩ a
    rw [equiv_principal]
    change binarySelfDual v (0 : Natural (K := F)) = 0
    exact map_zero _

/-- Root-fixed cocycles lie in the natural principal layer of the actual dual model. -/
theorem conjugate_root_fixed_principal (hF : 2 < Nat.card F)
    (g : Representation.SymplecticFourOrthogonalCover.L (K := F))
    (f : cocycles (binaryNatural (K := F)))
    (hf : ∀ r ∈ Roots.conjugateGroup g,
      universalAction (binaryNatural (K := F)) r f = f) :
    f ∈ (principal (binaryNatural (K := F))).range := by
  apply (equiv_annihilates_radical_iff f).mp
  apply dual_conjugate_root_fixed_annihilates_radical hF g
  intro r hr
  rw [← equiv_intertwines, hf r hr]

end DualModel
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology
