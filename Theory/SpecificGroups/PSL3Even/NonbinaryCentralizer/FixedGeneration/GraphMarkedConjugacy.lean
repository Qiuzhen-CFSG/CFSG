module

public import Theory.SpecificGroups.PSL3Even.NonbinaryCentralizer.Models
public import Theory.SpecificGroups.PSL3Even.NonbinaryCentralizer.StandardGeneration
public import Theory.SpecificGroups.PSL3Even.NonbinaryCentralizer.FixedGeneration.Transport
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage
public import Theory.SpecificGroups.PSL3.OuterSolvable.StandardQuotient
public import Theory.SpecificGroups.PSL3.CartanActions.NormalizerForm
public import Theory.SpecificGroups.PSL3.ExtensionBorel.Linear
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.Graph

/-!
# Graph conjugacy preserving the marked PSL₃ unipotent subgroup

A graph conjugate preserving the specified projective upper-unitriangular
subgroup has a conjugator to `oppositionGraph` that preserves that same
subgroup. Standard automorphism factorization removes the field factor of
an arbitrary conjugator. The resulting linear–graph involution has a
symmetric matrix g, and preservation of U forces g times coordinate reversal
to be upper triangular.

Thus g has rows (a,b,c), (b,e,0), (c,0,0), with c and e nonzero. In the finite
characteristic-two field choose s² = a and u² = e. The upper triangular
matrix P with rows (1,s,0), (0,u,b+su), (0,0,c) satisfies g = PJPᵀ, where J
is reversal. Conjugation by the actual projective actor `linearConj(P⁻¹)`
gives the Borel-preserving graph representative and retains the literal U.
The generation transport theorem then yields ⟨C_PSL₃(a), U⟩ = PSL₃.

This supplies the graph branch of `hgenerate` in the nonbinary centralizer
geometry assembly. The field branch and final source assembly remain separate.
Sources: Aschbacher–Smith E.1.1–6 and E.1.14(1), printed pp.209–214;
GLS3, Theorem 2.5.12 and §2.7 (`refs/KGroup/GLS3/chapter2.tex`).
-/

public section

open scoped MatrixGroups
open Subgroup Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage
open Matrix.PSL3.CartanActions Matrix.PSL3.ExtensionBorel
namespace Matrix.PSL3Even.NonbinaryCentralizer.GraphMarkedConjugacy
variable {F : Type*} [Field F]

private theorem linear_graph_of_conjugate (hcover : standard F = ⊤)
    (a : MulAut PSL(3,F)) (ha : IsConj a (graph F)) :
    ∃ g : GL (Fin 3) F, a = linearConj F g * graph F := by
  obtain ⟨b, hb⟩ := isConj_iff.mp ha.symm
  obtain ⟨m, σ, hm | hm⟩ := NormalizerForm.standard_factorization F
    field_linearConj graph_linearConj_exists field_commute_graph b (hcover ▸ mem_top b)
  all_goals
    refine ⟨m * inverseTransposeGL F m⁻¹, ?_⟩
    have hc := (field_commute_graph (F := F) σ).eq
    rw [← hb, hm]
    calc
      _ = linearConj F m * (fieldAction F σ * graph F) *
          (fieldAction F σ)⁻¹ * (linearConj F m)⁻¹ := by group
      _ = linearConj F m * graph F * (linearConj F m)⁻¹ := by rw [hc]; group
      _ = _ := by rw [← map_inv, mul_assoc, graph_linearConj, ← mul_assoc, ← map_mul]

variable [Finite F] [CharP F 2]

private theorem triangular_gram (g : GL (Fin 3) F) (hs : g.val.transpose = g.val)
    (hz : g.val 1 2 = 0 ∧ g.val 2 2 = 0 ∧ g.val 2 1 = 0) :
    ∃ p : GL (Fin 3) F, p ∈ glBorel F ∧
      g.val = p.val * (reversalGL F).val * p.val.transpose := by
  have h10 : g.val 1 0 = g.val 0 1 := congrArg (fun M => M 0 1) hs
  have h20 : g.val 2 0 = g.val 0 2 := congrArg (fun M => M 0 2) hs
  have hshape : g.val = !![g.val 0 0, g.val 0 1, g.val 0 2;
      g.val 0 1, g.val 1 1, 0; g.val 0 2, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h10, h20, hz.1, hz.2.1, hz.2.2]
  have hn := GeneralLinearGroup.det_ne_zero g
  rw [hshape, Matrix.det_fin_three] at hn
  have hc : g.val 0 2 ≠ 0 := by
    intro h
    simp [h] at hn
  have he : g.val 1 1 ≠ 0 := by
    intro h
    simp [h] at hn
  let s := (frobeniusEquiv F 2).symm (g.val 0 0)
  let u := (frobeniusEquiv F 2).symm (g.val 1 1)
  have hs2 : s ^ 2 = g.val 0 0 := frobeniusEquiv_symm_pow_p F 2 _
  have hu2 : u ^ 2 = g.val 1 1 := frobeniusEquiv_symm_pow_p F 2 _
  have hu : u ≠ 0 := by
    intro h
    exact he (by simpa [h] using hu2.symm)
  let P : Matrix (Fin 3) (Fin 3) F :=
    !![1, s, 0; 0, u, g.val 0 1 + s * u; 0, 0, g.val 0 2]
  have hP : IsUnit P.det := by simp [P, Matrix.det_fin_three, hu, hc]
  refine ⟨GeneralLinearGroup.mk'' P hP, ?_, ?_⟩
  · change P 1 0 = 0 ∧ P 2 0 = 0 ∧ P 2 1 = 0
    simp [P]
  · change g.val = P * (reversalGL F).val * P.transpose
    rw [hshape]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, reversalGL, Matrix.mul_apply, Fin.sum_univ_three,
        ← pow_two, hs2, hu2, CharTwo.add_self_eq_zero, mul_comm,
        add_left_comm, add_comm]

private theorem marked_linear_graph (g : GL (Fin 3) F)
    (hg : (linearConj F g * graph F) ^ 2 = 1)
    (hU : (unipotent F).map (linearConj F g * graph F).toMonoidHom = unipotent F) :
    ∃ c : MulAut PSL(3,F),
      MulAut.congr c (linearConj F g * graph F) = oppositionGraph F ∧
      (unipotent F).map c.toMonoidHom = unipotent F := by
  have hJJ : reversalGL F * reversalGL F = 1 :=
    Units.ext (reversalGL F).val_inv
  have hactor : linearConj F (g * reversalGL F) * oppositionGraph F =
      linearConj F g * graph F := by
    rw [oppositionGraph, map_mul, ← mul_assoc, ← map_mul, ← map_mul,
      mul_assoc g, hJJ, mul_one]
  have hstable : (unipotent F).map (linearConj F (g * reversalGL F)).toMonoidHom =
      unipotent F := by
    rw [← hactor] at hU
    change (unipotent F).map ((linearConj F (g * reversalGL F)).toMonoidHom.comp
      (oppositionGraph F).toMonoidHom) = _ at hU
    rwa [← Subgroup.map_map, oppositionGraph_unipotent] at hU
  have hz := NormalizerForm.linearConj_upperTriangular F (g * reversalGL F) hstable
  change (g.val * (reversalGL F).val) 1 0 = 0 ∧
    (g.val * (reversalGL F).val) 2 0 = 0 ∧
    (g.val * (reversalGL F).val) 2 1 = 0 at hz
  simp [reversalGL, Matrix.mul_apply, Fin.sum_univ_three] at hz
  obtain ⟨p, hp, hgram⟩ := triangular_gram g
    (Matrix.PSL3.OddInvolutionFixed.graph_involution_symmetric g hg) hz
  have hfactor : g = p * reversalGL F * inverseTransposeGL F p⁻¹ := Units.ext hgram
  have hnorm : p⁻¹ * g * inverseTransposeGL F p = reversalGL F := by
    rw [hfactor, map_inv]
    group
  refine ⟨linearConj F p⁻¹, ?_, linearConj_preserves F p⁻¹ ((glBorel F).inv_mem hp)⟩
  change linearConj F p⁻¹ * (linearConj F g * graph F) *
    (linearConj F p⁻¹)⁻¹ = linearConj F (reversalGL F) * graph F
  rw [← map_inv, inv_inv, mul_assoc, mul_assoc, graph_linearConj, ← mul_assoc,
    ← map_mul, ← mul_assoc, ← map_mul, hnorm]

end Matrix.PSL3Even.NonbinaryCentralizer.GraphMarkedConjugacy

namespace Matrix.PSL3Even.NonbinaryCentralizer
variable {F : Type*} [Field F] [Finite F]

/-- An actual graph conjugate preserving U has an actual conjugator to the
opposition graph representative preserving the same U. -/
theorem exists_graph_marked_conjugator {f : ℕ}
    (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (a : MulAut PSL(3,F)) (ha : IsConj a (graph F))
    (hU : (unipotent F).map a.toMonoidHom = unipotent F) :
    ∃ c : MulAut PSL(3,F), MulAut.congr c a = oppositionGraph F ∧
      (unipotent F).map c.toMonoidHom = unipotent F := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hpow : a ^ 2 = 1 := by
    have h := IsConj.pow 2 ha
    rw [graph_sq, isConj_one_left] at h
    exact h
  obtain ⟨g, rfl⟩ := GraphMarkedConjugacy.linear_graph_of_conjugate
    (standard_eq_top_of_two_power_card F (by omega) hF) a ha
  exact GraphMarkedConjugacy.marked_linear_graph g hpow hU

/-- The graph branch of nonbinary fixed-group generation, with the original
upper-unitriangular subgroup and no compatible-conjugacy premise. -/
theorem graph_fixed_sup_unipotent_of_isConj {f : ℕ}
    (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (a : MulAut PSL(3,F)) (ha : IsConj a (graph F))
    (hU : (unipotent F).map a.toMonoidHom = unipotent F) :
    a.fixedSubgroup ⊔ unipotent F = ⊤ := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  obtain ⟨c, hc, hcU⟩ := exists_graph_marked_conjugator hf hF a ha hU
  exact graph_fixed_sup_unipotent_of_marked_congr a c hc hcU

end Matrix.PSL3Even.NonbinaryCentralizer
