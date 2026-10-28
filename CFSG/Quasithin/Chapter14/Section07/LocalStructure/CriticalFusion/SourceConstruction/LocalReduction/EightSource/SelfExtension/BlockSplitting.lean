module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension.Sections
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension.Certificate
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension.GeneratorRelations
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension.ParityRank
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Splitting a natural self-extension with small transposition displacement

The kernel-checked cochain calculation leaves a coboundary and the parity
class. The parity class moves at least six dimensions on the actual module,
so a transposition moving at most two forces the coboundary class. Correcting
the chosen section preserves its specified natural submodule.
-/

public noncomputable section
open Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

private theorem adjacent_rank_le_of_swap [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) (Equiv.Perm (Fin 8)) W)
    (t : Equiv.Perm (Fin 8)) (ht : t.IsSwap)
    (hr : Module.finrank (ZMod 2) (ρ t-LinearMap.id).range ≤ 2) :
    Module.finrank (ZMod 2) (ρ (adjacent 0)-LinearMap.id).range ≤ 2 := by
  obtain ⟨a,b,hab,rfl⟩ := ht
  obtain ⟨g,hg⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap hab
    (by decide : (0 : Fin 8) ≠ 1))
  have he := BinaryOffender.fixedCodim_zpowers_conj ρ (Equiv.swap a b) g
  rw [hg,BinaryOffender.fixedCodim_zpowers_eq_displacement_rank,
    BinaryOffender.fixedCodim_zpowers_eq_displacement_rank] at he
  exact he.trans_le hr

/-- A natural-by-natural section with a rank-at-most-two transposition has
an invariant complement to its specified kernel. -/
theorem SectionData.natural_complement
    {ρ : Representation (ZMod 2) (Equiv.Perm (Fin 8)) W} {X : Subrepresentation ρ}
    (s : SectionData ρ X naturalSix naturalSix)
    (t : Equiv.Perm (Fin 8)) (ht : t.IsSwap)
    (hr : Module.finrank (ZMod 2) (ρ t-LinearMap.id).range ≤ 2) :
    ∃ K : Subrepresentation ρ, IsCompl X.toSubmodule K.toSubmodule ∧
      ∃ eK : K.toSubmodule ≃ₗ[ZMod 2] V,
        ∀ g v, eK (K.toRepresentation g v) = naturalSix g (eK v) := by
  let : FiniteDimensional (ZMod 2) W := Module.Finite.equiv s.totalEquiv
  let B (i : Fin 7) : Mat := LinearMap.toMatrix' (s.cochain (adjacent i))
  obtain ⟨D,c,hD⟩ := normal_form B (relations_of_cocycle naturalSix naturalSix
    s.cochain s.cochain_mul naturalSix_adjacent naturalSix_adjacent)
  have hB (i : Fin 7) (v : V) : s.cochain (adjacent i) v =
      (A i*D+D*A i+c • A i).mulVec v := by
    calc
      _ = (B i).mulVec v := (LinearMap.toMatrix'_mulVec _ _).symm
      _ = _ := congrArg (fun M : Mat => M.mulVec v) (hD i)
  have hc : c = 0 := by
    have hcases : c=0 ∨ c=1 := by
      have hb : ∀ a : ZMod 2, a=0 ∨ a=1 := by decide
      exact hb c
    rcases hcases with hc | hc
    · exact hc
    · exfalso
      let T : Module.End (ZMod 2) (V × V) :=
        s.totalEquiv.symm.toLinearMap.comp ((ρ (adjacent 0)).comp s.totalEquiv.toLinearMap)
      have hT (x y : V) : T (x,y) = ((A 0).mulVec x+
          (A 0*D+D*A 0+A 0).mulVec y,(A 0).mulVec y) := by
        apply s.totalEquiv.injective
        change s.totalEquiv (s.totalEquiv.symm (ρ (adjacent 0) (s.totalEquiv (x,y)))) = _
        rw [s.totalEquiv.apply_symm_apply,s.totalEquiv_apply,s.totalEquiv_apply,
          map_add,s.inclusion_equivariant,s.block,naturalSix_adjacent,hB,hc,one_smul,
          map_add]
        exact (add_assoc _ _ _).symm
      have hlarge := parity_twist_matrix_rank_gt_two D T hT
      have hle := displacement_rank_le_of_injective_intertwining s.totalEquiv.toLinearMap
        s.totalEquiv.injective T (ρ (adjacent 0)) (fun z => by
          change _ = s.totalEquiv (s.totalEquiv.symm (ρ (adjacent 0) (s.totalEquiv z)))
          rw [s.totalEquiv.apply_symm_apply]
          rfl)
      have hsmall := adjacent_rank_le_of_swap ρ t ht hr
      exact (not_lt_of_ge (hle.trans hsmall)) hlarge
  apply s.complement_of_generator_correction (Set.range adjacent)
    (Equiv.Perm.mclosure_swap_castSucc_succ 7) D.mulVecLin
  rintro g ⟨i,rfl⟩
  apply LinearMap.ext
  intro v
  rw [hB,hc,zero_smul,add_zero,naturalSix_adjacent]
  simp only [LinearMap.sub_apply,LinearMap.comp_apply,Matrix.mulVecLin_apply,
    Matrix.add_mulVec,Matrix.mulVec_mulVec]
  ext r
  exact (CharTwo.sub_eq_add _ _).symm

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension
