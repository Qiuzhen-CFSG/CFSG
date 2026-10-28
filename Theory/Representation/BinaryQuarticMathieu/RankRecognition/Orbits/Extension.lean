module

public import Theory.Representation.BinaryQuarticMathieu.RankRecognition.Orbits.Evaluation
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Tactic.FinCases
/-!
# Extending checks on increasing basis quadruples

Every increasing quadruple occurs in the published enumeration. Sorting the
indices of an arbitrary injective basis tuple and using alternation therefore
reduces equality of forms to those 210 values. This yields the preservation
criterion used for the two literal generators.
-/

public section
namespace BinaryQuarticMathieu.RankRecognition.Orbits

private def quadrupleIndex (v : Fin 4 → Fin 10) : Fin 210 :=
  ⟨((210 - (10 - (v 0).val).choose 4) +
    ((9 - (v 0).val).choose 3 - (10 - (v 1).val).choose 3) +
    ((9 - (v 1).val).choose 2 - (10 - (v 2).val).choose 2) +
    ((v 3).val - (v 2).val - 1)) % 210, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 4096 in
private theorem quadruple_index_check : ∀ v : Fin 4 → Fin 10,
    StrictMono v → fastQuad (quadrupleIndex v) = v := by
  decide +kernel

private theorem quadruple_complete (v : Fin 4 → Fin 10) (hv : StrictMono v) :
    ∃ i : Fin 210, quadruple i = v :=
  ⟨quadrupleIndex v, (fastQuad_eq _).symm.trans (quadruple_index_check v hv)⟩

theorem form_ext_quadruple (f g : Form)
    (h : ∀ i : Fin 210, f (fun j => basisVector (quadruple i j)) =
      g (fun j => basisVector (quadruple i j))) : f = g := by
  apply (Pi.basisFun F (Fin 10)).ext_alternating
  intro v hv
  simp only [Pi.basisFun_apply]
  change f (basisVector ∘ v) = g (basisVector ∘ v)
  let p := Tuple.sort v
  obtain ⟨i, hi⟩ := quadruple_complete (v ∘ p)
    ((Tuple.monotone_sort v).strictMono_of_injective (hv.comp p.injective))
  apply smul_left_cancel (Equiv.Perm.sign p)
  rw [← f.map_perm, ← g.map_perm]
  have hh := h i
  rw [hi] at hh
  exact hh

attribute [local irreducible] quartic

theorem preserves_of_quadruple (g : U ≃ₗ[F] U)
    (h : ∀ i : Fin 210, quartic (fun j => g (basisVector (quadruple i j))) =
      quartic (fun j => basisVector (quadruple i j))) : Preserves quartic g := by
  have he : quartic.compLinearMap g.toLinearMap = quartic :=
    form_ext_quadruple _ _ h
  intro v w x y
  have hx := AlternatingMap.congr_fun he ![v,w,x,y]
  have ht : (fun i => g (![v,w,x,y] i)) = ![g v,g w,g x,g y] := by
    funext i
    fin_cases i <;> rfl
  simpa only [AlternatingMap.compLinearMap_apply, LinearEquiv.coe_coe,
    Function.comp_def, ht] using hx

end BinaryQuarticMathieu.RankRecognition.Orbits
