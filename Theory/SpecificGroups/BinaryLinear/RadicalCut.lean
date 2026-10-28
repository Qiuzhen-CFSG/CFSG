module
public import Theory.SpecificGroups.BinaryLinear.NestedRadicals
public import Theory.Representation.BinaryRadicalFlag.Normalizer
public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.FieldTheory.Finiteness

/-!
# A nontrivial binary linear radical contains a full block radical

The canonical fixed filtration identifies the radical normalizer as a partial
flag stabilizer. Every cut of that flag has its full block-unipotent radical
normal in the flag stabilizer. Radical saturation therefore puts that entire
block radical in the original subgroup. No basis or parabolic premise is used.
Source: Aschbacher--Smith C.2.7 and C.4.8, pp.145--147,154.
-/

public noncomputable section
open Subgroup
namespace BinaryLinear
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] [Nontrivial V]

private def cutNatural : Representation (ZMod 2) (BinaryLinear.GL V) V where
  toFun g := g.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

/-- A nontrivial two-radical contains a full radical at a nonzero proper subspace. -/
theorem exists_radical_cut (P : Subgroup (BinaryLinear.GL V)) (hP : P.IsPRadical 2) :
    ∃ W : Submodule (ZMod 2) V, W ≠ ⊥ ∧ W ≠ ⊤ ∧ radical W ≤ P := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (BinaryLinear.GL V) := Finite.of_injective (fun g : BinaryLinear.GL V => (g : V → V))
    DFunLike.coe_injective
  have hinj : Function.Injective (cutNatural (V := V)) := by
    intro g h he
    exact LinearEquiv.ext (LinearMap.congr_fun he)
  obtain ⟨k,W,hk,_,hs,hproper,hN⟩ :=
    Representation.BinaryRadical.exists_partialFlag_normalizer cutNatural hinj P hP
  let i : Fin k := ⟨0,hk⟩
  have hN' : normalizer (P : Set (BinaryLinear.GL V)) = ⨅ j, parabolic (W j) := hN
  refine ⟨W i,(hproper i).1,(hproper i).2,?_⟩
  have hle : radical (W i) ≤ (normalizer (P : Set (BinaryLinear.GL V))).pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes (radical_two _) ?_ ?_
    · rw [hN']
      intro g hg
      simp only [mem_iInf]
      intro j
      rcases le_total i j with hij | hji
      · exact radical_le_nested_parabolic (hs.monotone hij) hg
      · exact radical_le_smaller_parabolic (hs.monotone hji) hg
    · apply le_trans _ (parabolic_le_normalizer (W i))
      rw [hN']
      exact iInf_le _ i
  exact hle.trans_eq hP.2

end BinaryLinear
