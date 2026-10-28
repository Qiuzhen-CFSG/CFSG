module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.MiddleRoots
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.LocalActions
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# The radical commutator lies in the actual three middle roots

An abelian simple root U_i complements the normal radical V_i in U, so
U' lies in V_i. The reflection s_j preserves V_j and its derived subgroup.
Consequently V_j' lies in V_j intersect V_i intersect V_i^{s_j}, which is
exactly the three-middle-root product. This is the initial commutator bound
used in the unequal-parameter proof of Fong--Seitz I (6E), printed p.44;
it is also the type-I side of the bound used in (6D), printed p.43.

The earlier source inclusion V_i <= K_i remains explicit. Abelianness of
the canonical U_i is a local-type premise, not an assumption about V_j'.
There is no claim here that the derived subgroup equals the middle root.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem simple_square (i : Fin 2) : Q.simple i*Q.simple i = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2

private theorem rightConjugate_commutator (A B : Subgroup (X ⧸ Q.D)) (n : X ⧸ Q.D) :
    rightConjugate ⁅A,B⁆ n = ⁅rightConjugate A n,rightConjugate B n⁆ := by
  simp only [rightConjugate, comap_equiv_eq_map_symm', map_commutator]

/-- An abelian simple root makes the corresponding radical contain U'. -/
theorem unipotent_commutator_le_remainder (i : Fin 2)
    (hK : simpleRemainder Q split i ≤ localKernel Q i)
    (hA : ⁅simpleRoot Q split i,simpleRoot Q split i⁆ = ⊥) :
    ⁅split.U,split.U⁆ ≤ simpleRemainder Q split i := by
  have hN : split.U ≤ normalizer (simpleRemainder Q split i : Set (X ⧸ Q.D)) :=
    split.U_le.trans ((Q.tits.B_le_standardParabolic {Q.simple i}).trans
      (remainder_parabolic_normalizes Q split i hK))
  have hU : simpleRoot Q split i ⊔ simpleRemainder Q split i = split.U := by
    apply le_antisymm (sup_le (simpleRoot_le Q split i) inf_le_left)
    intro x hx
    have hx' : x ∈ (simpleRoot Q split i : Set (X ⧸ Q.D)) *
        (simpleRemainder Q split i : Set (X ⧸ Q.D)) := (simpleRoot_mul_remainder Q split i).symm ▸ hx
    obtain ⟨a,ha,v,hv,rfl⟩ := hx'
    exact mul_mem_sup ha hv
  have hAU : ⁅simpleRoot Q split i,split.U⁆ ≤ simpleRemainder Q split i := by
    rw [commutator_comm, ← hU]
    exact commutator_sup_le_of_relative_normal split.U _ _ _ _ hN
      (simpleRoot_le Q split i) inf_le_left (hA ▸ bot_le)
      (le_normalizer_iff_commutator_le_left.mp ((simpleRoot_le Q split i).trans hN))
  nth_rw 1 [← hU]
  exact commutator_sup_le_of_relative_normal split.U _ _ _ _ hN
    (simpleRoot_le Q split i) inf_le_left hAU
    (le_normalizer_iff_commutator_le_left.mp hN)

/-- The initial containment in the proof of 6E(b), on the actual three middle roots.
Only the earlier kernel inclusion and abelianness of this canonical simple root
are used; no field sizes, perfectness or mixed commutator relations are assumed. -/
theorem radical_commutator_le_middle (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hK : simpleRemainder Q split i ≤ localKernel Q i)
    (hA : ⁅simpleRoot Q split i,simpleRoot Q split i⁆ = ⊥) :
    ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ ≤ middleRoots Q split i j := by
  let n := representative (Q.simple j)
  have hC : ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ ≤
      simpleRemainder Q split i :=
    (commutator_mono inf_le_left inf_le_left).trans
      (unipotent_commutator_le_remainder Q split i hK hA)
  have hV : rightConjugate (simpleRemainder Q split j) (n : X ⧸ Q.D) =
      simpleRemainder Q split j := by
    rw [simpleRemainder, rightConjugate_inf,
      ← unipotentConjugate_eq split _ n (representative_spec _),
      unipotentConjugate_right split _ _ n (representative_spec _), simple_square,
      unipotentConjugate_one, inf_comm]
  have hc := comap_mono (f := (MulAut.conj (n : X ⧸ Q.D)).toMonoidHom) hC
  change rightConjugate ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ (n : X ⧸ Q.D) ≤
    rightConjugate (simpleRemainder Q split i) (n : X ⧸ Q.D) at hc
  rw [rightConjugate_commutator, hV] at hc
  rw [middleRoots_eq_intersection Q split hm i j hij n (representative_spec _)]
  exact le_inf (le_inf (commutator_le_self _) hC) hc

/-- Thus every commutator has the source's literal three-factor coordinates. -/
theorem radical_commutator_three_coordinates (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hK : simpleRemainder Q split i ≤ localKernel Q i)
    (hA : ⁅simpleRoot Q split i,simpleRoot Q split i⁆ = ⊥)
    (x : X ⧸ Q.D) (hx : x ∈ ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆) :
    ∃ b ∈ rootAt Q split j (Q.simple i),
      ∃ c ∈ rootAt Q split i (Q.simple j*Q.simple i),
        ∃ d ∈ rootAt Q split j (Q.simple i*Q.simple j), x = b*c*d := by
  have hmem : x ∈ (middleRoots Q split i j : Set (X ⧸ Q.D)) :=
    radical_commutator_le_middle Q split hm i j hij hK hA hx
  rw [middleRoots_product Q split hm i j hij] at hmem
  obtain ⟨bc,⟨b,hb,c,hc,rfl⟩,d,hd,rfl⟩ := hmem
  exact ⟨b,hb,c,hc,d,hd,rfl⟩

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
