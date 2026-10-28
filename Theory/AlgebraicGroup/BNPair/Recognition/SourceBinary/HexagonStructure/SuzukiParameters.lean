module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiWeightProfile
public import Theory.Representation.FiniteSimpleGenerators

/-!
# Equality of the two regular Suzuki parameters

The five canonical root Frattini quotients are irreducible H-modules with
binary dimensions a,b,a,b,a. Their literal inclusion maps span the radical
Frattini quotient. Since H has odd order, every H-invariant section is an
equivariant quotient of that span, and its dimension is a subset sum of these
five dimensions; images are allowed to overlap or vanish.

For a≤b the retained Clifford argument constructs an HR_j-invariant natural
Suzuki section of dimension 4b. If a<b, the actual Frattini lower bound gives
2b≤3a, and oddness makes this strict. None of the five-weight subset sums can
then equal 4b. Interchanging the endpoints proves equality in either orientation.

This proves the parameter synchronization on p.40 of Fong--Seitz I (6C),
without assuming dim(V_j)=3a+2b or irreducibility of V_j. The equal-parameter
Cartan/kernel and commutator contradiction, the small Suzuki cases, and the
remaining unitary and solvable rows are not conclusions of this module.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

theorem suzuki_radical_root_profile (i j : Fin 2)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup n)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup n) (t : Fin 5) :
    (rootAtCartanFrattiniRepresentation Q split
      (radicalRootKind i j t) (radicalRootWord Q i j t)).IsIrreducible ∧
    Module.finrank (ZMod 2) (Additive
      (rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t) ⧸
        frattini (rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t)))) =
      if t = 1 ∨ t = 3 then 2*n+1 else 2*m+1 := by
  fin_cases t <;> dsimp only [radicalRootKind,radicalRootWord]
  · exact suzuki_rootAt_cartan_frattini_irreducible Q split i hKi hm μi νi 1
  · exact suzuki_rootAt_cartan_frattini_irreducible Q split j hKj hn μj νj (Q.simple i)
  · exact suzuki_rootAt_cartan_frattini_irreducible Q split i hKi hm μi νi (Q.simple j*Q.simple i)
  · exact suzuki_rootAt_cartan_frattini_irreducible Q split j hKj hn μj νj (Q.simple i*Q.simple j)
  · exact suzuki_rootAt_cartan_frattini_irreducible Q split i hKi hm μi νi (Q.simple j)

/-- Every literal H-invariant section of the radical has a dimension drawn
from a subfamily of the five actual root constituents. -/
theorem suzuki_radical_section_dimension (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup n)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup n)
    (U : Subrepresentation (radicalHRepresentation Q split j hKj))
    (N : Subrepresentation U.toRepresentation) :
    ∃ s : Finset (Fin 5), Module.finrank (ZMod 2) (U ⧸ N.toSubmodule) =
      ∑ t ∈ s, if t = 1 ∨ t = 3 then 2*n+1 else 2*m+1 := by
  classical
  let ρ := radicalHRepresentation Q split j hKj
  let σ := N.quotientRepresentation
  have hc : Representation.IsCompletelyReducible ρ :=
    Representation.isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime ρ (Or.inr (by
      rw [ringChar.eq (ZMod 2) 2]; exact ⟨Nat.prime_two,split.odd⟩))
  obtain ⟨p,hp⟩ := Representation.section_surjection_of_completelyReducible ρ U N hc
  let f (t : Fin 5) := radicalRootIntertwiner Q split hhex i j hij hKj t
  let g (t : Fin 5) := p.comp (f t)
  let J : Subrepresentation σ := ⨆ t, (g t).range
  let A : Subrepresentation ρ := {
    toSubmodule := J.toSubmodule.comap p.toLinearMap
    apply_mem_toSubmodule h v hv := by
      change p (ρ h v) ∈ J.toSubmodule
      rw [p.isIntertwining]
      exact J.apply_mem_toSubmodule h hv }
  have hA : A = ⊤ := by
    apply top_unique
    rw [← radical_root_intertwiners_span Q split hhex i j hij hKj]
    apply iSup_le
    intro t v hv
    obtain ⟨x,rfl⟩ := hv
    change p (f t x) ∈ J
    have hle : (g t).range ≤ J := by
      dsimp only [J]; exact le_iSup (fun u => (g u).range) t
    exact hle ⟨x,rfl⟩
  have hJ : J = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨v,rfl⟩ := hp y
    exact (show v ∈ A from hA ▸ Submodule.mem_top)
  let V (t : Fin 5) := Additive
    (rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t) ⧸
      frattini (rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t)))
  let τ (t : Fin 5) := rootAtCartanFrattiniRepresentation Q split
    (radicalRootKind i j t) (radicalRootWord Q i j t)
  obtain ⟨s,_,hd⟩ := Representation.finrank_simple_generators V τ σ
    (fun t => (suzuki_radical_root_profile Q split i j hKi hKj hm hn μi μj νi νj t).1)
    g Finset.univ
  have hspan : (⨆ t ∈ (Finset.univ : Finset (Fin 5)), (g t).range) = ⊤ := by
    simpa only [Finset.mem_univ,iSup_pos] using hJ
  rw [hspan] at hd
  change Module.finrank (ZMod 2) ↥(⊤ : Submodule (ZMod 2) (U ⧸ N.toSubmodule)) = _ at hd
  rw [finrank_top] at hd
  refine ⟨s,hd.trans ?_⟩
  exact Finset.sum_congr rfl fun t _ =>
    (suzuki_radical_root_profile Q split i j hKi hKj hm hn μi μj νi νj t).2

private theorem no_unequal_weight_sum {m n : ℕ} (hlt : m < n)
    (hlo : 4*(2*n+1) ≤ 3*(2*m+1)+2*(2*n+1)) (s : Finset (Fin 5))
    (hs : 4*(2*n+1) = ∑ t ∈ s, if t = 1 ∨ t = 3 then 2*n+1 else 2*m+1) : False := by
  classical
  have he : (∑ t ∈ s, if t = 1 ∨ t = 3 then 2*n+1 else 2*m+1) =
      ∑ t : Fin 5, if t ∈ s then (if t = 1 ∨ t = 3 then 2*n+1 else 2*m+1) else 0 := by
    simp
  rw [he,Fin.sum_univ_five] at hs
  simp only [Fin.reduceEq,or_false,false_or,or_self,ite_false,ite_true] at hs
  split_ifs at hs <;> omega

/-- Source (6C)'s parameter synchronization, retaining the actual Cartan
and the literal radical section throughout. This is not yet the exclusion. -/
theorem suzuki_suzuki_parameters_eq_of_le (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≤ n)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup n)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup n) : m = n := by
  by_contra he
  have hlt : m < n := lt_of_le_of_ne hmn he
  obtain ⟨U,N,_,_,_,hd⟩ := suzuki_suzuki_cartan_natural_section Q split hhex i j hij hKj
    hm hn hmn μj νi νj
  let inc := inclusion (show Q.tits.B ⊓ Q.tits.N ≤ radicalCartanActor Q split j from le_sup_left)
  let UH : Subrepresentation (radicalHRepresentation Q split j hKj) := {
    toSubmodule := U.toSubmodule
    apply_mem_toSubmodule h _ hv := U.apply_mem_toSubmodule (inc h) hv }
  let NH : Subrepresentation UH.toRepresentation := {
    toSubmodule := N.toSubmodule
    apply_mem_toSubmodule h _ hv := N.apply_mem_toSubmodule (inc h) hv }
  obtain ⟨s,hs⟩ := suzuki_radical_section_dimension Q split hhex i j hij hKi hKj hm hn
    μi μj νi νj UH NH
  have hd' : Module.finrank (ZMod 2) (UH ⧸ NH.toSubmodule) = 4*(2*n+1) := hd
  rw [hd'] at hs
  have hb := suzuki_suzuki_radical_finrank_bounds Q split hhex i j hij hKj hm hn μj νi νj
  exact no_unequal_weight_sum hlt (hb.1.trans hb.2) s hs

theorem suzuki_suzuki_parameters_eq (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup n)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup n) : m = n := by
  rcases le_total m n with h | h
  · exact suzuki_suzuki_parameters_eq_of_le Q split hhex i j hij hKi hKj hm hn h μi μj νi νj
  · exact (suzuki_suzuki_parameters_eq_of_le Q split hhex j i hij.symm hKj hKi hn hm h μj μi νj νi).symm
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
