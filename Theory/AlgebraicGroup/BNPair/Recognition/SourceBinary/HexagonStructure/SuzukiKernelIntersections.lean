module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiCartanKernels

/-!
# Same-type Cartan-kernel intersections in a Suzuki hexagon

An N-normal Cartan subgroup lying in K_i centralizes every conjugate of U_i.
If nontrivial, joint panel faithfulness and the actual Suzuki fixed-point
dichotomy make it fixed-point-free on every conjugate of U_j. Its centralizer
in U_si is then the literal product of two type-i roots. The induced R_i
action and the contradictory Frattini bounds prove that subgroup trivial.

Apply this to (H ∩ K_i) ∩ (H ∩ K_i)^{s_j}. The i-reflection centralizes it,
the j-reflection interchanges its factors, and H normalizes it. These lifts
generate N modulo H, proving the required relative normality. This proves
both same-type intersections by interchanging i and j. Parameters need not
be equal, and original-factor perfectness is not assumed.

Source: Fong--Seitz I (6C), printed p.40, the first three kernel-intersection
cases. The separated opposite-type case, the rank-one Cartan intersection,
and the final commutator contradiction on p.41 remain further steps.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

include split in
private theorem cartan_kernel_pair (hcore : Q.tits.B.normalCore = ⊥)
    (i j : Fin 2) (hij : i ≠ j) :
    (Q.tits.B ⊓ Q.tits.N) ⊓ localKernel Q i ⊓ localKernel Q j = ⊥ := by
  have hh := joint_cartan_kernel_eq_bot Q split (UnitarySource.actorReflection Q split) hcore
  change (Q.tits.B ⊓ Q.tits.N) ⊓ localKernel Q 0 ⊓ localKernel Q 1 = ⊥ at hh
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · exact hh
  · simpa only [inf_assoc,inf_left_comm,inf_comm] using hh
  · exact (hij rfl).elim

private theorem root_fixedFree_conjugates (i : Fin 2)
    (T : Subgroup (X ⧸ Q.D)) (hTN : Q.tits.N ≤ normalizer (T : Set (X ⧸ Q.D)))
    (hf : simpleRoot Q split i ⊓ centralizer (T : Set (X ⧸ Q.D)) = ⊥) (w : Weyl Q) :
    rootAt Q split i w ⊓ centralizer (T : Set (X ⧸ Q.D)) = ⊥ := by
  let n := representative w
  have hh := congrArg (fun A => rightConjugate A (n : X ⧸ Q.D)) hf
  rw [rightConjugate_inf,rightConjugate_eq_self _
    (normalizer_le_normalizer_centralizer T (hTN n.property))] at hh
  have hb : rightConjugate (⊥ : Subgroup (X ⧸ Q.D)) (n : X ⧸ Q.D) = ⊥ := by
    ext x
    change (n : X ⧸ Q.D)*x*(n : X ⧸ Q.D)⁻¹ = 1 ↔ x = 1
    exact (MulAut.conj (n : X ⧸ Q.D)).map_eq_one_iff
  exact hh.trans hb

private theorem root_fixed_conjugates (i : Fin 2)
    (T : Subgroup (X ⧸ Q.D)) (hTN : Q.tits.N ≤ normalizer (T : Set (X ⧸ Q.D)))
    (hf : simpleRoot Q split i ≤ centralizer (T : Set (X ⧸ Q.D))) (w : Weyl Q) :
    rootAt Q split i w ≤ centralizer (T : Set (X ⧸ Q.D)) := by
  let n := representative w
  have hh := comap_mono (f := (MulAut.conj (n : X ⧸ Q.D)).toMonoidHom) hf
  change rootAt Q split i w ≤ rightConjugate (centralizer (T : Set (X ⧸ Q.D))) (n : X ⧸ Q.D) at hh
  rwa [rightConjugate_eq_self _ (normalizer_le_normalizer_centralizer T (hTN n.property))] at hh

/-- No nontrivial N-normal Cartan subgroup can lie in either actual Suzuki
panel kernel. The contradiction is on its literal two-root centralizer section. -/
theorem suzuki_normal_cartan_kernel_eq_bot (hhex : rotationOrder Q = 6)
    (hcore : Q.tits.B.normalCore = ⊥) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup n)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup n)
    (T : Subgroup (X ⧸ Q.D)) (hTH : T ≤ Q.tits.B ⊓ Q.tits.N)
    (hTN : Q.tits.N ≤ normalizer (T : Set (X ⧸ Q.D))) (hTK : T ≤ localKernel Q i) : T = ⊥ := by
  by_contra hT
  have hTKj : ¬ T ≤ localKernel Q j := by
    intro hh
    exact hT (eq_bot_iff.mpr (by
      rw [←cartan_kernel_pair Q split hcore i j hij]
      exact le_inf (le_inf hTH hTK) hh))
  have hfree := suzuki_cartan_subgroup_fixedFree Q split j hKj hn μj νj T hTH hTKj
  have hfix : simpleRoot Q split i ≤ centralizer (T : Set (X ⧸ Q.D)) :=
    le_centralizer_iff.mp ((le_inf hTH hTK).trans (cartanKernel_centralizes_simpleRoot Q split i))
  exact no_suzuki_centralizer_section Q split hhex j i hij.symm
    (UnitarySource.actorReflection Q split i) hKi hm μi
    (suzuki_root_frattini_bound Q split i hm νi) T hTH
    (root_fixedFree_conjugates Q split j T hTN hfree)
    (root_fixed_conjugates Q split i T hTN hfix)

private theorem normalizer_le_of_simple_lifts
    (i j : Fin 2) (hij : i ≠ j) (a b : Q.tits.N)
    (ha : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) a = Q.simple i)
    (hb : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) b = Q.simple j)
    (A : Subgroup (X ⧸ Q.D)) (hH : Q.tits.B ⊓ Q.tits.N ≤ A)
    (haA : (a : X ⧸ Q.D) ∈ A) (hbA : (b : X ⧸ Q.D) ∈ A) : Q.tits.N ≤ A := by
  classical
  let n (k : Fin 2) := if k = i then a else b
  have hn (k : Fin 2) : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) (n k) = Q.simple k := by
    by_cases hk : k = i
    · simpa [n,hk] using ha
    · have hkj : k = j := by omega
      simpa [n,hkj,hij.symm] using hb
  have hnA (k : Fin 2) : (n k : X ⧸ Q.D) ∈ A := by
    dsimp only [n]
    split_ifs <;> assumption
  intro g hg
  let q := QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N)
  let gN : Q.tits.N := ⟨g,hg⟩
  obtain ⟨k,hk,hqk⟩ := UnitarySource.exists_weyl_lift_in Q n hn A hnA (q gN)
  have hdiff : gN*k⁻¹ ∈ (Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (gN*k⁻¹) = 1
    rw [map_mul,map_inv,hqk,mul_inv_cancel]
  have hz := A.mul_mem (hH hdiff) hk
  change (g*(k : X ⧸ Q.D)⁻¹)*(k : X ⧸ Q.D) ∈ A at hz
  simpa only [inv_mul_cancel_right] using hz

/-- The two same-type kernels separated by the opposite simple reflection
have trivial intersection, in the original source H and with right conjugation. -/
theorem suzuki_same_type_cartan_kernels_disjoint (hhex : rotationOrder Q = 6)
    (hcore : Q.tits.B.normalCore = ⊥) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup n)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup n) :
    let K := (Q.tits.B ⊓ Q.tits.N) ⊓ localKernel Q i
    K ⊓ rightConjugate K (representative (Q.simple j) : X ⧸ Q.D) = ⊥ := by
  let H := Q.tits.B ⊓ Q.tits.N
  let K := H ⊓ localKernel Q i
  let b := representative (Q.simple j)
  let T := K ⊓ rightConjugate K (b : X ⧸ Q.D)
  have hTH : T ≤ H := inf_le_left.trans inf_le_left
  let := split.abelian
  have hHK : H ≤ centralizer (K : Set (X ⧸ Q.D)) :=
    (Subgroup.le_centralizer H).trans (centralizer_le (show (K : Set (X ⧸ Q.D)) ⊆ (H : Set (X ⧸ Q.D)) from fun _ hx => hx.1))
  have hHT : H ≤ normalizer (T : Set (X ⧸ Q.D)) :=
    ((Subgroup.le_centralizer H).trans (centralizer_le hTH)).trans (centralizer_le_normalizer T)
  let a := UnitarySource.actorReflection Q split i
  have haT : (a.val : X ⧸ Q.D) ∈ normalizer (T : Set (X ⧸ Q.D)) := by
    apply centralizer_le_normalizer T
    have hKR : K ≤ centralizer (rankOne Q split i : Set (X ⧸ Q.D)) := by
      change (H ⊓ embeddedPanelKernel Q i) ≤ centralizer (rankOneRootGroup Q split i : Set (X ⧸ Q.D))
      rw [←cartan_centralizer_rankOneRootGroup Q split i]
      exact inf_le_right
    exact (le_centralizer_iff.mp (inf_le_left.trans hKR)) a.mem_rankOne
  have hb2 : (b : X ⧸ Q.D)*(b : X ⧸ Q.D) ∈ H := by
    change b*b ∈ (Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) (b*b) = 1
    rw [map_mul,representative_spec]
    exact (show Q.simple j*Q.simple j = 1 by simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem j)).2)
  have he : rightConjugate T (b : X ⧸ Q.D) = T := by
    change rightConjugate (K ⊓ rightConjugate K (b : X ⧸ Q.D)) (b : X ⧸ Q.D) = T
    rw [rightConjugate_inf,←rightConjugate_mul,
      rightConjugate_eq_self K ((hHK.trans (centralizer_le_normalizer K)) hb2),inf_comm]
  have hbT : (b : X ⧸ Q.D) ∈ normalizer (T : Set (X ⧸ Q.D)) := by
    apply mem_normalizer_iff.mpr
    intro x
    exact (show (b : X ⧸ Q.D)*x*(b : X ⧸ Q.D)⁻¹ ∈ T ↔ x ∈ T from
      SetLike.ext_iff.mp he x).symm
  exact suzuki_normal_cartan_kernel_eq_bot Q split hhex hcore i j hij hKi hKj hm hn μi μj νi νj
    T hTH (normalizer_le_of_simple_lifts Q i j hij a.val b a.class_eq (representative_spec _)
      _ hHT haT hbT) (inf_le_left.trans inf_le_right)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
