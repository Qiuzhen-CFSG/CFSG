/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Codes/TernaryGolaySigned.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.TernaryGolayDiagonal
public import Theory.AtlasPort.OtherSporadic.Codes.TernaryGolayFullWeight

/-!
# TernaryGolaySigned

Signed coordinate maps preserving the code have unique lifts up to global sign.
Finite injectivity gives surjectivity, and comparing two lifts reduces to scalar diagonals.

Source: Gerald Höhn, ATLAS, `Atlas/Codes/TernaryGolaySigned.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed computational definitions.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
namespace Atlas.Codes

/-- Signed coordinate substitution, with permutation written in pullback convention. -/
def ternarySignedMap (d : TernaryWord) (σ : Equiv.Perm (Fin 12))
    (w : TernaryWord) : TernaryWord := fun i => d i * w (σ i)

def TernarySignedPreserves (d : TernaryWord) (σ : Equiv.Perm (Fin 12)) : Prop :=
  (∀ i, d i ≠ 0) ∧ ∀ w ∈ ternaryGolay, ternarySignedMap d σ w ∈ ternaryGolay

theorem ternarySignedMap_injective (d : TernaryWord) (σ : Equiv.Perm (Fin 12))
    (hd : ∀ i, d i ≠ 0) : Function.Injective (ternarySignedMap d σ) := by
  intro u v h
  funext i
  have he := congrFun h (σ.symm i)
  simpa [ternarySignedMap] using (mul_left_cancel₀ (hd (σ.symm i)) he)

theorem ternarySignedMap_surjective_code (d : TernaryWord)
    (σ : Equiv.Perm (Fin 12)) (h : TernarySignedPreserves d σ)
    (w : TernaryWord) (hw : w ∈ ternaryGolay) :
    ∃ v ∈ ternaryGolay, ternarySignedMap d σ v = w := by
  let f : ternaryGolay → ternaryGolay := fun v => ⟨ternarySignedMap d σ v.val, h.2 _ v.prop⟩
  have hf : Function.Injective f := by
    intro u v he
    exact Subtype.ext (ternarySignedMap_injective d σ h.1 (congrArg Subtype.val he))
  obtain ⟨v,hv⟩ := Finite.surjective_of_injective hf ⟨w,hw⟩
  exact ⟨v.val,v.prop,congrArg Subtype.val hv⟩

/-- Two signed lifts of one coordinate permutation differ by a global sign. -/
theorem ternarySigned_lift_unique (d e : TernaryWord) (σ : Equiv.Perm (Fin 12))
    (hd : TernarySignedPreserves d σ) (he : TernarySignedPreserves e σ) :
    d = e ∨ d = -e := by
  have hn : ∀ i, d i * e i ≠ 0 := fun i => mul_ne_zero (hd.1 i) (he.1 i)
  have hp : ∀ w ∈ ternaryGolay, ternaryDiagonal (fun i => d i * e i) w ∈ ternaryGolay := by
    intro w hw
    obtain ⟨v,hv,rfl⟩ := ternarySignedMap_surjective_code e σ he w hw
    have heq : ternaryDiagonal (fun i => d i * e i) (ternarySignedMap e σ v) =
        ternarySignedMap d σ v := by
      funext i
      have hs : e i * e i = 1 := by
        have hh : ∀ a : ZMod 3, a ≠ 0 → a*a = 1 := by decide
        exact hh _ (he.1 i)
      change (d i * e i) * (e i * v (σ i)) = d i * v (σ i)
      calc
        _ = d i * (e i * e i) * v (σ i) := by ring
        _ = _ := by rw [hs]; simp
    rw [heq]
    exact hd.2 v hv
  rcases ternaryDiagonal_automorphism_scalars (fun i => d i * e i) hn hp with h | h
  · left
    funext i
    have hi := congrFun h i
    have hh : ∀ a b : ZMod 3, a*b = 1 → a=b := by decide
    exact hh _ _ hi
  · right
    funext i
    have hi := congrFun h i
    have hh : ∀ a b : ZMod 3, a*b = -1 → a = -b := by decide
    exact hh _ _ hi

end Atlas.Codes
