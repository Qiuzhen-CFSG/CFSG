module

public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.Embedding
public import Theory.Mathieu.M12.A5Fixer
public import Theory.Mathieu.M12.A5Fixer.InnerCentralizer
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# Transporting the intrinsic M₁₂–A₅ centralizer bounds

The ambient marking identifies residual commutation with fixation of the
corresponding element of native M₁₂. For an actual residual A₅, any subgroup
centralizing it therefore injects into the full automorphism fixer. Its
residual intersection injects into the native inner centralizer. The proved
intrinsic bounds give orders at most four and two, with no module-action or
involution-table premises.

This is the transport step for Aschbacher–Smith H.11.1(5), printed pp.392–393,
combined manuscript of 1 March 2004.
-/

public section
open Subgroup Sporadic.Mathieu
namespace CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.DisplacementFixers

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : M12ModuleInput ρ) (d : AmbientExtension ρ h)

omit [Finite G] in
/-- Ambient commutation becomes pointwise fixation in the marked native model. -/
theorem embedding_fixes_of_commute (g : G) (x : solvableResidual G)
    (hc : g * x = x * g) : d.embedding g (h.residualEquiv x) = h.residualEquiv x := by
  apply MulAut.conj_injective_of_center_eq_bot m12_center_eq_bot
  have he : g * x * g⁻¹ = x := by rw [hc, mul_inv_cancel_right]
  calc
    MulAut.conj (d.embedding g (h.residualEquiv x)) =
        d.embedding g * MulAut.conj (h.residualEquiv x) * (d.embedding g)⁻¹ := by
      ext y
      simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply,
        map_mul, map_inv, MulEquiv.apply_symm_apply]
    _ = MulAut.conj (h.residualEquiv x) := by
      rw [← d.embedding_residual x, ← map_inv, ← map_mul, ← map_mul, he,
        d.embedding_residual]

omit [Finite G] in
/-- The ambient marking identifies native fixed elements with residual commutation. -/
theorem embedding_fixes_iff_commute (g : G) (x : solvableResidual G) :
    d.embedding g (h.residualEquiv x) = h.residualEquiv x ↔ g * x = x * g := by
  constructor
  · intro hx
    apply d.embedding_injective
    simp only [map_mul, d.embedding_residual]
    apply MulEquiv.ext
    intro y
    change d.embedding g (h.residualEquiv x * y * (h.residualEquiv x)⁻¹) =
      h.residualEquiv x * d.embedding g y * (h.residualEquiv x)⁻¹
    rw [map_mul, map_mul, map_inv, hx]
  · exact embedding_fixes_of_commute ρ h d g x

include d in
omit [Finite G] in
/-- The full centralizer of a residual A₅ has order at most four, and its residual part at most two. -/
theorem centralizing_a5_bounds (E K : Subgroup G)
    (e : E ≃* alternatingGroup (Fin 5)) (hEL : E ≤ solvableResidual G)
    (hKC : K ≤ centralizer (E : Set G)) :
    Nat.card K ≤ 4 ∧ Nat.card (K ⊓ solvableResidual G : Subgroup G) ≤ 2 := by
  let EL := E.subgroupOf (solvableResidual G)
  let P := EL.map h.residualEquiv.toMonoidHom
  let eP : P ≃* alternatingGroup (Fin 5) :=
    (EL.equivMapOfInjective h.residualEquiv.toMonoidHom h.residualEquiv.injective).symm.trans
      ((subgroupOfEquivOfLe hEL).trans e)
  have hf (g : K) : d.embedding g ∈ fixingSubgroup (MulAut M12) (P : Set M12) := by
    rw [mem_fixingSubgroup_iff]
    rintro y ⟨x, hx, rfl⟩
    exact embedding_fixes_of_commute ρ h d g x
      ((mem_centralizer_iff.mp (hKC g.property) x hx).symm)
  let f : K → fixingSubgroup (MulAut M12) (P : Set M12) := fun g => ⟨d.embedding g, hf g⟩
  have hfi : Function.Injective f := by
    intro a b he
    exact Subtype.ext (d.embedding_injective (congrArg Subtype.val he))
  have hi (g : (K ⊓ solvableResidual G : Subgroup G)) :
      h.residualEquiv ⟨g, g.property.2⟩ ∈ centralizer (P : Set M12) := by
    rw [mem_centralizer_iff]
    rintro y ⟨x, hx, rfl⟩
    change h.residualEquiv x * h.residualEquiv ⟨g, g.property.2⟩ =
      h.residualEquiv ⟨g, g.property.2⟩ * h.residualEquiv x
    rw [← map_mul, ← map_mul]
    apply congrArg h.residualEquiv
    apply Subtype.ext
    exact mem_centralizer_iff.mp (hKC g.property.1) x hx
  let i : (K ⊓ solvableResidual G : Subgroup G) → centralizer (P : Set M12) :=
    fun g => ⟨h.residualEquiv ⟨g, g.property.2⟩, hi g⟩
  have hii : Function.Injective i := by
    intro a b he
    have hh := h.residualEquiv.injective (congrArg Subtype.val he)
    exact Subtype.ext (congrArg (fun z : solvableResidual G => (z : G)) hh)
  exact ⟨(Nat.card_le_card_of_injective f hfi).trans
    (M12A5Fixer.card_le_four_of_bounds M12A5Fixer.innerCentralizerBound
      M12A5Fixer.Automorphisms.outerIndexBound P eP),
    (Nat.card_le_card_of_injective i hii).trans (M12A5Fixer.innerCentralizerBound P ⟨eP⟩)⟩

end CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.DisplacementFixers
