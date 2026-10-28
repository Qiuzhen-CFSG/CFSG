module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.C2RankThree.Suborbits

/-!
# The original kernel root and its parabolic action

For m=4 the root U₂^{s₁} is U^{s₁} ∩ U^{s₁s₂}. The second
simple lift swaps these two factors, so it normalizes the root. An
ascent places the root inside U. The full Cartan also normalizes it.
Consequently normalization by U extends to the whole second parabolic,
and the actual root fixes the base coset and the entire neighboring orbit.
This proves the coset-fixation step of Fong–Seitz II (7C) from its root
normalization premise, for every q including two, with the canonical lifts.

The source (6A)(a) commutation and (3G) must still establish that premise;
no centrality or normalization of the source root is asserted unconditionally.
Source: Fong–Seitz I (3G), pp.14–16; II (7C), p.193.
-/

public noncomputable section
open Subgroup MulAction
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.C2RankThree
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem longest_eq (hm : rotationOrder Q = 4) :
    longest Q = Q.simple 0*Q.simple 1*Q.simple 0*Q.simple 1 := by
  simpa only [hm,alternatingWord,Bool.false_eq_true,ite_false,ite_true,
    Bool.not_false,Bool.not_true,mul_one,mul_assoc] using (alternatingWord_longest Q false).symm

/-- The source kernel root is the intersection of two actual conjugates of U. -/
theorem kernelRoot_eq_intersection (hm : rotationOrder Q = 4) :
    kernelRoot Q split = unipotentConjugate split (Q.simple 0) ⊓
      unipotentConjugate split (Q.simple 0*Q.simple 1) := by
  have h0 : Q.simple 0*Q.simple 0 = 1 := by
    simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem 0)).2
  have h1 : Q.simple 1*Q.simple 1 = 1 := by
    simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem 1)).2
  rw [kernelRoot,simpleRoot,rootIntersection,rightConjugate_inf,
    ← unipotentConjugate_eq split (Q.simple 0) (representative _) (representative_spec _),
    unipotentConjugate_right split _ _ (representative _) (representative_spec _),longest_eq Q hm]
  simp only [mul_assoc,h0,h1,mul_one]

/-- The actual kernel root lies in the specified U, by the length-two ascent. -/
theorem kernelRoot_le_unipotent (hm : rotationOrder Q = 4) : kernelRoot Q split ≤ split.U := by
  apply (ascent_root_conjugate_le_remainder Q split (Q.simple 1) 0 ?_
    (representative _) (representative_spec _)).trans inf_le_left
  have h := wordLength_alternatingWord Q true (n := 2) (by omega)
  simpa only [alternatingWord,Bool.false_eq_true,ite_true,ite_false,Bool.not_true,Bool.not_false,
    mul_one,Q.tits.wordLength_mem_S (Q.simple_mem 1)] using h

/-- The second simple reflection swaps the two factors of the intersection. -/
theorem kernelRoot_conjugate_second (hm : rotationOrder Q = 4) :
    rightConjugate (kernelRoot Q split) (representative (Q.simple 1) : X ⧸ Q.D) =
      kernelRoot Q split := by
  have h1 : Q.simple 1*Q.simple 1 = 1 := by
    simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem 1)).2
  rw [kernelRoot_eq_intersection Q split hm,rightConjugate_inf,
    unipotentConjugate_right split _ _ (representative _) (representative_spec _),
    unipotentConjugate_right split _ _ (representative _) (representative_spec _)]
  simp only [mul_assoc,h1,mul_one,inf_comm]

/-- The chosen second lift normalizes the actual kernel root. -/
theorem second_normalizes_kernelRoot (hm : rotationOrder Q = 4) :
    (representative (Q.simple 1) : X ⧸ Q.D) ∈ normalizer (kernelRoot Q split : Set (X ⧸ Q.D)) := by
  apply mem_normalizer_iff.mpr
  intro x
  have h := congrArg (fun A : Subgroup (X ⧸ Q.D) => x ∈ A)
    (kernelRoot_conjugate_second Q split hm)
  exact (Iff.of_eq h).symm

/-- Normalization by U extends to the full second parabolic. The Cartan
and second Weyl lift are handled by the literal split geometry. -/
theorem parabolic_normalizes_kernelRoot (hm : rotationOrder Q = 4)
    (hU : split.U ≤ normalizer (kernelRoot Q split : Set (X ⧸ Q.D))) :
    Q.tits.standardParabolic {Q.simple 1} ≤ normalizer (kernelRoot Q split : Set (X ⧸ Q.D)) := by
  have hT : Q.tits.B ⊓ Q.tits.N ≤ normalizer (kernelRoot Q split : Set (X ⧸ Q.D)) :=
    torus_normalizes_rightConjugate _ (torus_normalizes_simpleRoot Q split 1) (representative _)
  have hB : Q.tits.B ≤ normalizer (kernelRoot Q split : Set (X ⧸ Q.D)) := by
    rw [← split.factorization]
    exact sup_le hU hT
  intro x hx
  have hx' : x ∈ (Q.tits.B : Set (X ⧸ Q.D)) ∪ Q.tits.bruhatCell (Q.simple 1) :=
    singleton_parabolic_cells (Q.simple_mem 1) ▸ hx
  rcases hx' with hx | hx
  · exact hB hx
  · rw [bruhatCell,B_mul_representativeSet_mul_B Q.tits.B Q.tits.N (Q.simple 1)
      (representative _) (representative_spec _)] at hx
    obtain ⟨a,ha,b,hb,rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx
    exact mul_mem (mul_mem (hB ha) (second_normalizes_kernelRoot Q split hm)) (hB hb)

/-- The canonical kernel root fixes the neighboring representative. -/
theorem kernelRoot_fixes_neighbor (u : X ⧸ Q.D) (hu : u ∈ kernelRoot Q split) :
    u • neighborPoint Q = neighborPoint Q := by
  change u • rightCosetPoint Q 1 (representative (Q.simple 0)) = _
  rw [← inv_inv u, ← rightCosetPoint_mul]
  apply (rightCosetPoint_eq_iff Q 1 _ _).mpr
  apply split.U_le.trans (Q.tits.B_le_standardParabolic _)
  apply simpleRoot_le Q split 1
  have hu' : (representative (Q.simple 0) : X ⧸ Q.D)*u*
      (representative (Q.simple 0) : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split 1 := hu
  simpa only [mul_inv_rev,inv_inv,mul_assoc] using (simpleRoot Q split 1).inv_mem hu'

/-- The literal source fixation follows from normalization by U; the
second lift, full Borel and all neighboring cosets are proved here. -/
theorem kernelRoot_fixes_closed_orbit (hm : rotationOrder Q = 4)
    (hU : split.U ≤ normalizer (kernelRoot Q split : Set (X ⧸ Q.D))) :
    ∀ u ∈ kernelRoot Q split, ∀ c ∈ insert (rightCosetPoint Q 1 1)
      (orbit (stabilizer (X ⧸ Q.D) (rightCosetPoint Q 1 1)) (neighborPoint Q)), u • c = c := by
  intro u hu c hc
  rcases hc with rfl | hc
  · apply (mem_stabilizer_iff).mp
    rw [base_stabilizer]
    exact Q.tits.B_le_standardParabolic _ (split.U_le (kernelRoot_le_unipotent Q split hm hu))
  · obtain ⟨g,rfl⟩ := mem_orbit_iff.mp hc
    have hg : (g : X ⧸ Q.D) ∈ Q.tits.standardParabolic {Q.simple 1} := by
      exact Eq.mp (congrArg (fun H : Subgroup (X ⧸ Q.D) => (g : X ⧸ Q.D) ∈ H)
        (base_stabilizer Q)) g.property
    have hn := parabolic_normalizes_kernelRoot Q split hm hU
      ((Q.tits.standardParabolic {Q.simple 1}).inv_mem hg)
    have hv : (g : X ⧸ Q.D)⁻¹*u*g ∈ kernelRoot Q split := by
      simpa only [inv_inv] using (mem_normalizer_iff.mp hn u).mp hu
    have he := kernelRoot_fixes_neighbor Q split _ hv
    have he' := congrArg (fun x : Points Q 1 => (g : X ⧸ Q.D) • x) he
    change u • ((g : X ⧸ Q.D) • neighborPoint Q) = (g : X ⧸ Q.D) • neighborPoint Q
    simpa only [← mul_smul,mul_inv_cancel_left,mul_assoc] using he'

/-- In particular the centrality proved in source (7C) suffices, with no
additional permutation-kernel or coset-fixation premise. -/
theorem kernelRoot_fixes_of_central (hm : rotationOrder Q = 4)
    (hc : split.U ≤ centralizer (kernelRoot Q split : Set (X ⧸ Q.D))) :
    ∀ u ∈ kernelRoot Q split, ∀ c ∈ insert (rightCosetPoint Q 1 1)
      (orbit (stabilizer (X ⧸ Q.D) (rightCosetPoint Q 1 1)) (neighborPoint Q)), u • c = c :=
  kernelRoot_fixes_closed_orbit Q split hm (hc.trans (centralizer_le_normalizer _))

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.C2RankThree
