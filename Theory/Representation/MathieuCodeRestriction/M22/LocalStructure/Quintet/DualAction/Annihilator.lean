module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.Spaces
public import Theory.Representation.BinaryPermutationNaturalDuality

/-!
# Reversal of the quintet chief flag

The coordinate pairing gives an order reversing equivalence between the
invariant subspaces of the actual outer M22 cocode and code modules. It
therefore preserves chief factors, reversing their order. The natural
five-point quotient is self-dual, giving an equivariant natural-module
identification of the code annihilator, rather than just its dimension.

Source: Aschbacher--Smith, H.15.4(1) and H.16.3(1--2), printed pp.400,403,
combined manuscript of 1 March 2004. The cocode assertions are explicit inputs.
-/

@[expose] public section
noncomputable section
namespace MathieuCode.M22Quintet
namespace DualAction

abbrev cocodeAction := m22OuterCocodeRepresentation.comp Q.subtype
abbrev codeAction := m22OuterCodeRepresentation.comp Q.subtype

/-- The reverse annihilator, still using the coordinate pairing. -/
def coannihilator (W : Submodule (ZMod 2) M22Code) :
    Submodule (ZMod 2) M22Cocode :=
  (W.map m22CodeCocodeDuality.toLinearMap).dualCoannihilator

theorem mem_coannihilator (W : Submodule (ZMod 2) M22Code) (u : M22Cocode) :
    u ∈ coannihilator W ↔ ∀ v ∈ W, m22CodeCocodeDuality v u = 0 := by
  rw [coannihilator, Submodule.mem_dualCoannihilator]
  constructor
  · intro h v hv
    exact h _ ⟨v, hv, rfl⟩
  · rintro h _ ⟨v, hv, rfl⟩
    exact h v hv

theorem coannihilator_annihilator (U : Submodule (ZMod 2) M22Cocode) :
    coannihilator (annihilator U) = U := by
  unfold coannihilator annihilator
  rw [Submodule.map_comap_eq_of_surjective m22CodeCocodeDuality.surjective,
    Subspace.dualAnnihilator_dualCoannihilator_eq]

theorem annihilator_coannihilator (W : Submodule (ZMod 2) M22Code) :
    annihilator (coannihilator W) = W := by
  unfold coannihilator annihilator
  rw [Subspace.dualCoannihilator_dualAnnihilator_eq,
    Submodule.comap_map_eq_of_injective m22CodeCocodeDuality.injective]

def coannihilatorSubrepresentation (W : Subrepresentation codeAction) :
    Subrepresentation cocodeAction where
  toSubmodule := coannihilator W.toSubmodule
  apply_mem_toSubmodule g u hu := by
    rw [mem_coannihilator] at hu ⊢
    intro v hv
    have h := hu _ (W.apply_mem_toSubmodule g⁻¹ hv)
    have he := LinearMap.congr_fun
      (m22CodeCocodeDuality_equivariant g.val⁻¹ v) u
    change m22CodeCocodeDuality (m22OuterCodeRepresentation g.val⁻¹ v) u =
      m22CodeCocodeDuality v (m22OuterCocodeRepresentation (g.val⁻¹)⁻¹ u) at he
    rw [inv_inv] at he
    exact he.symm.trans h

/-- The order reversal includes invariance, not just vector-space annihilation. -/
def annihilatorOrderIso :
    Subrepresentation cocodeAction ≃o (Subrepresentation codeAction)ᵒᵈ where
  toFun := annihilatorSubrepresentation
  invFun := coannihilatorSubrepresentation
  left_inv U := Subrepresentation.toSubmodule_injective
    (coannihilator_annihilator U.toSubmodule)
  right_inv W := Subrepresentation.toSubmodule_injective
    (annihilator_coannihilator W.toSubmodule)
  map_rel_iff' := by
    intro U W
    change annihilator W.toSubmodule ≤ annihilator U.toSubmodule ↔ U ≤ W
    constructor
    · intro h u hu
      have hu' : u ∈ coannihilator (annihilator U.toSubmodule) := by
        rwa [coannihilator_annihilator]
      have hw' : u ∈ coannihilator (annihilator W.toSubmodule) := by
        rw [mem_coannihilator] at hu' ⊢
        exact fun v hv => hu' v (h hv)
      rwa [coannihilator_annihilator] at hw'
    · exact annihilator_antitone

/-- Every cocode chief factor becomes a code chief factor in reverse order. -/
theorem annihilator_covBy {U W : Subrepresentation cocodeAction} (h : U ⋖ W) :
    annihilatorSubrepresentation W ⋖ annihilatorSubrepresentation U := by
  exact ((apply_covBy_apply_iff annihilatorOrderIso).mpr h).ofDual

/-- A genuine natural-module marking of the annihilator of the cocode middle term. -/
def naturalEquiv
    (e : (M22Cocode ⧸ V6) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5)) :
    V4 ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5) :=
  ((annihilatorQuotientDuality V6).trans e.symm.dualMap).trans
    ((BinaryPermutation.naturalDualEquiv (Fin 5)).symm)

private theorem dual_equivariant {G H X Y : Type*} [Group G] [Group H]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    (ρ : Representation (ZMod 2) G X) (σ : Representation (ZMod 2) H Y)
    (q : G →* H) (e : X ≃ₗ[ZMod 2] Y)
    (he : ∀ g v, e (ρ g v) = σ (q g) (e v)) (g : G)
    (f : Module.Dual (ZMod 2) X) :
    e.symm.dualMap (ρ.dual g f) = σ.dual (q g) (e.symm.dualMap f) := by
  ext w
  change f (ρ g⁻¹ (e.symm w)) = f (e.symm (σ (q g)⁻¹ w))
  congr 1
  apply e.injective
  simpa only [LinearEquiv.apply_symm_apply, map_inv] using he g⁻¹ (e.symm w)

/-- The marking intertwines the actual code action and the five-point action. -/
theorem naturalEquiv_equivariant
    (q : Q →* Equiv.Perm (Fin 5))
    (e : (M22Cocode ⧸ V6) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5))
    (he : ∀ (g : Q) v, e (V6Subrepresentation.quotientRepresentation g v) =
      BinaryPermutation.naturalRepresentation (Fin 5) (q g) (e v))
    (g : Q) (v : V4) :
    naturalEquiv e (V4Subrepresentation.toRepresentation g v) =
      BinaryPermutation.naturalRepresentation (Fin 5) (q g) (naturalEquiv e v) := by
  have hmark (w : V4) :
      BinaryPermutation.naturalDualEquiv (Fin 5) (naturalEquiv e w) =
        e.symm.dualMap (annihilatorQuotientDuality V6 w) :=
    (BinaryPermutation.naturalDualEquiv (Fin 5)).apply_symm_apply _
  apply (BinaryPermutation.naturalDualEquiv (Fin 5)).injective
  calc
    BinaryPermutation.naturalDualEquiv (Fin 5)
        (naturalEquiv e (V4Subrepresentation.toRepresentation g v)) =
        e.symm.dualMap
          (annihilatorQuotientDuality V6 (V4Subrepresentation.toRepresentation g v)) := hmark _
    _ = e.symm.dualMap (V6Subrepresentation.quotientRepresentation.dual g
          (annihilatorQuotientDuality V6 v)) :=
      congrArg e.symm.dualMap
        (annihilatorQuotientDuality_equivariant V6Subrepresentation g v)
    _ = (BinaryPermutation.naturalRepresentation (Fin 5)).dual (q g)
          (e.symm.dualMap (annihilatorQuotientDuality V6 v)) :=
      dual_equivariant V6Subrepresentation.quotientRepresentation
        (BinaryPermutation.naturalRepresentation (Fin 5)) q e he g _
    _ = (BinaryPermutation.naturalRepresentation (Fin 5)).dual (q g)
          (BinaryPermutation.naturalDualEquiv (Fin 5) (naturalEquiv e v)) :=
      congrArg ((BinaryPermutation.naturalRepresentation (Fin 5)).dual (q g)) (hmark v).symm
    _ = BinaryPermutation.naturalDualEquiv (Fin 5)
          (BinaryPermutation.naturalRepresentation (Fin 5) (q g) (naturalEquiv e v)) :=
      (BinaryPermutation.naturalDualEquiv_equivariant (Fin 5) (q g) (naturalEquiv e v)).symm

end DualAction
end MathieuCode.M22Quintet
