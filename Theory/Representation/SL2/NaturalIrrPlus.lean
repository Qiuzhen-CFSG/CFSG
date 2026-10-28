module
public import Theory.Representation.SL2.AutomorphismNatural
public import Theory.SpecificGroups.SL2.Affine.Action
public import Theory.Representation.BinaryOffender.IrreducibleMovedTransport

/-!
# Natural SL₂ modules are actual Irr⁺ members

A surjection onto SL₂ preserves transitivity on nonzero natural vectors.
Every invariant binary subspace is therefore zero or the whole plane.
A transvection gives nontrivial movement; its invariant commutator span
is consequently the whole plane. The minimality criterion supplies the
literal irreducible quotient by fixed vectors required by Irr⁺.

Source: the natural-module case of Aschbacher--Smith B.4.2, printed p.86,
as used for the two-natural-copy branch of D.3.21, printed p.206.
-/

public noncomputable section
namespace Representation.SL2AutomorphismNatural
open Matrix BinaryOffender Subgroup
open scoped MatrixGroups
variable {F H : Type*} [Field F] [Finite F] [CharP F 2] [Group H]
local instance : Algebra (ZMod 2) F := ZMod.algebra _ 2

/-- A surjective marking on natural SL₂ gives Irr⁺ without an irreducibility premise. -/
theorem natural_irrPlus_of_surjective
    (q : H →* SL(2,F)) (hq : Function.Surjective q) :
    IsIrrPlus (action.comp (MulAut.conj.comp q)) ⊤ ⊤ := by
  let ρ := action.comp (MulAut.conj.comp q)
  have hr (h : H) (v : Fin 2 → F) : ρ h v = (q h).val.mulVec v := action_conj _ _
  have hm (J : Submodule (ZMod 2) (Fin 2 → F))
      (hJ : (⊤ : Subgroup H) ≤ subspaceStabilizer ρ J) : J = ⊥ ∨ J = ⊤ := by
    by_cases hbot : J = ⊥
    · exact Or.inl hbot
    right
    obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    apply top_unique
    intro w _
    by_cases hw : w = 0
    · exact hw ▸ J.zero_mem
    obtain ⟨g,hg⟩ := Matrix.SL2.exists_mulVec_eq F v w hv0 hw
    obtain ⟨g,rfl⟩ := hq g
    have hh := (hJ (mem_top g) v).mpr hv
    rwa [hr,hg] at hh
  have hn : ¬ (⊤ : Submodule (ZMod 2) (Fin 2 → F)) ≤ fixedSpace ρ ⊤ := by
    intro hh
    let g := SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one (1 : F)
    obtain ⟨h,he⟩ := hq g
    have hx := hh (show (![0,1] : Fin 2 → F) ∈ (⊤ : Submodule (ZMod 2) _) from Submodule.mem_top) ⟨h,mem_top h⟩
    change ρ h (![0,1] : Fin 2 → F) = ![0,1] at hx
    rw [hr,he] at hx
    have hx0 := congrFun hx 0
    simp [g,SpecialLinearGroup.transvection_coe,Matrix.mulVec,dotProduct,Fin.sum_univ_two] at hx0
  have ht : (⊤ : Subgroup H) ≤ subspaceStabilizer ρ ⊤ :=
    le_subspaceStabilizer ρ ⊤ (by simp)
  have hc : subspaceCommutator ρ ⊤ ⊤ = ⊤ := by
    rcases hm _ (subspaceCommutator_invariant_normalizer ρ ht (show (⊤ : Subgroup H) ≤ normalizer (⊤ : Subgroup H) from (⊤ : Subgroup H).le_normalizer)) with hz | he
    · exact (hn ((subspaceCommutator_eq_bot_iff ρ ⊤ ⊤).mp hz)).elim
    · exact he
  apply isIrrPlus_of_minimal ρ ht hc hn
  intro J hJ _
  rcases hm J hJ with rfl | he
  · exact Or.inr bot_le
  · exact Or.inl he
end Representation.SL2AutomorphismNatural
