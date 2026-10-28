module

public import Theory.Mathieu.M12.Properties.SylowAutomorphismGroup.Coordinates
public import Theory.Mathieu.M12.SmallParabolicPair.SylowGeometry

/-!
# Exhaustive inner involution fusion in M₁₂

Every involution lies in a Sylow two-subgroup. The existing 64-element
coordinates for the marked Sylow subgroup reduce fusion to 27 involutions.
For each one a short word in the standard generators conjugates either the
marked central involution z or the fixed-point-free marked involution third
to that element. The support sizes then identify third with the Atlas 2A
class. All word equalities are checked by Lean's kernel; the word
search is not trusted. Sylow conjugacy gives exhaustive coverage in M₁₂.

This is the inner-class coverage needed for Aschbacher–Smith 16.1.5(4),
combined manuscript of 1 March 2004, printed p.1171. The marked permutations
and their attribution come from SmallParabolicPair.Seeds and
Properties.InvolutionClasses. The reproducible certificate search is in
InvolutionFusion/source/generate.py. Centralizer identification and outer
automorphism coverage are separate results.
-/

public section
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M12SmallPair
namespace Sporadic.Mathieu.M12InvolutionFusion
open M12SmallPair.SylowAutomorphismGroup
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
private noncomputable def word : List Bool → M12
  | [] => 1
  | b :: bs => (if b then (⟨m12GeneratorB, m12GeneratorB_mem⟩ : M12)
      else ⟨m12GeneratorA, m12GeneratorA_mem⟩) * word bs
private def conjugatorWords : Array (List Bool) := #[
  [],
  [],
  [],
  [],
  [],
  [false,true,true,false,true,false,true,false,true,false,true,true,false,true,false,true,false,true,true],
  [],
  [false,true,true,false,true,false],
  [],
  [true,false,true,false,true,false,true,false,true,true,false,true,true,false,true,false,true,false,true,true,false,true,false,true],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [true,false],
  [],
  [],
  [],
  [],
  [false,true,true,false,true,true,false,true,true,false,true,false,true,false,true,true,false,true,false,true,false],
  [],
  [],
  [false,true,false,true,false,true,false,true,true,false,true,true,false,true,true,false,true,false],
  [],
  [false,true,false,true,true,false,true,false,true,false,true,false,true,false,true,true,false,true],
  [],
  [true,true,false,true,true,false,true,false,true,false,true,false,true,true,false,true,true,false],
  [],
  [true,true,false,true,false,true,true,false,true,false,true],
  [],
  [false,true,false,true,false,true,false,true,true,false,true,true,false,true,false,true,true,false,true,true],
  [false,true,false,true,false,true,true,false,true,true,false,true,true,false,true,false,true],
  [false,true,false,true,true,false,true,false,true,true,false,true,false,true,false,true,true,false,true,false],
  [true,true,false,true,true,false,true,false,true,false,true,false,true,true,false,true,false,true,false],
  [],
  [],
  [false,true,true,false,true,false,true,false,true,false,true,true,false,true,true,false,true,true,false],
  [true,true,false,true,true,false,true,true,false,true,false,true,true],
  [true,true,false,true,true,false,true,false,true,false,true,false,true,true,false,true,false,true,false],
  [true,false,true,false,true,false,true,true,false,true,false,true,false,true,false,true,true,false,true],
  [],
  [],
  [],
  [],
  [true,true,false,true,false,true,false,true,true,false,true,false],
  [],
  [],
  [false,true,false,true,false,true,false,true,true,false,true,true,false,true,true,false,true,false,true,false],
  [],
  [false,true,false,true,true,false,true,true,false,true,false,true,true],
  [true,false,true,true,false,true,true,false,true,true,false,true,false,true,false,true,true,false,true,false,true,false],
  [false,true,true,false,true,false,true,false,true,true,false,true,true,false,true,true,false,true,false,true,false,true,false],
  [],
  [],
  [true,false,true,false,true,false,true,true,false,true,false,true,false,true,true,false,true,true,false,true,false],
  [],
  [true,false,true,true,false,true,true,false,true,true],
  [true,false,true,false,true,false,true,false],
  [],
  [],
  []]

private noncomputable def conjugator (i : Fin 64) : M12 := word conjugatorWords[i.val]!

private theorem fusion_check : ∀ i : Fin 64,
    let x : M12 := element i
    x ^ 2 = 1 → x ≠ 1 →
      conjugator i * z * (conjugator i)⁻¹ = x ∨
      conjugator i * third * (conjugator i)⁻¹ = x := by
  decide +kernel

/-- Every involution of the marked Sylow subgroup lies in one of the two classes. -/
theorem sylow_fusion (x : sylowCandidate) (hx : orderOf (x : M12) = 2) :
    IsConj z (x : M12) ∨ IsConj third (x : M12) := by
  obtain ⟨i, rfl⟩ := element_surjective x
  have hp : (element i : M12) ^ 2 = 1 := by
    simpa only [hx] using pow_orderOf_eq_one (element i : M12)
  have hn : (element i : M12) ≠ 1 := by
    intro h
    simp [h] at hx
  rcases fusion_check i hp hn with h | h
  · exact Or.inl (isConj_iff.mpr ⟨conjugator i, h⟩)
  · exact Or.inr (isConj_iff.mpr ⟨conjugator i, h⟩)

/-- Every involution of the actual Witt-design M₁₂ is conjugate to z or third. -/
theorem marked_fusion (x : M12) (hx : orderOf x = 2) :
    IsConj z x ∨ IsConj third x := by
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M12 P commonSylow
  have hmem : MulAut.conj g x ∈ sylowCandidate := by
    have he := (P.equivSMul g ⟨x, hP (mem_zpowers x)⟩).property
    change MulAut.conj g x ∈ (g • P : Sylow 2 M12) at he
    rw [hg] at he
    exact he
  have ho : orderOf (MulAut.conj g x) = 2 := (MulAut.conj g).orderOf_eq x |>.trans hx
  have hc : IsConj (MulAut.conj g x) x := (isConj_iff.mpr ⟨g, rfl⟩).symm
  rcases sylow_fusion ⟨_, hmem⟩ ho with h | h
  · exact Or.inl (h.trans hc)
  · exact Or.inr (h.trans hc)
/-- The marked representatives cannot fuse: their support sizes differ. -/
theorem representatives_not_isConj : ¬ IsConj z m12Involution2A := by
  rintro h
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  have he := congrArg (fun x : M12 => (x : Equiv.Perm (Fin 12)).support.card) hg
  have hz : (z : Equiv.Perm (Fin 12)).support.card = 8 := by decide +kernel
  change ((g : Equiv.Perm (Fin 12)) * (z : Equiv.Perm (Fin 12)) *
    (g : Equiv.Perm (Fin 12))⁻¹).support.card = _ at he
  rw [Equiv.Perm.card_support_conj, hz, m12Involution2A_support_card] at he
  omega
/-- The fixed-point-free marked involution is in the Atlas 2A class. -/
theorem third_isConj_atlas_twoA : IsConj third m12Involution2A :=
  (marked_fusion m12Involution2A m12Involution2A_order).resolve_left representatives_not_isConj

/-- Exhaustive coverage by the marked central class and the Atlas 2A class. -/
theorem involution_fusion (x : M12) (hx : orderOf x = 2) :
    IsConj z x ∨ IsConj m12Involution2A x := by
  rcases marked_fusion x hx with h | h
  · exact Or.inl h
  · exact Or.inr (third_isConj_atlas_twoA.symm.trans h)
end Sporadic.Mathieu.M12InvolutionFusion
