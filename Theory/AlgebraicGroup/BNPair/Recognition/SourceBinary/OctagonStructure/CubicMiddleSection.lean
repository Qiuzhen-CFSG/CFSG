module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicMiddleCentralizer
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.LinearLocalRoots
public import Theory.GroupAction.SubgroupCentralizerCongruence

/-!
# The degree-one octagon's middle-root quotients

Commutators and squares of the seven-root radical lie in the five middle
roots: each of the two end-root projections has elementary image, and the
middle subgroup is the intersection of the two kernels. The corresponding
quotient is therefore elementary abelian, of order sixteen when the root
orders are two and four.

The centralizer of the middle odd root contains this subgroup. It is
normal in the radical, and the perpendicular rank-one commutator makes it
invariant under the entire marked parabolic. Its quotient is elementary
abelian. The separating cubic has eight fixed points in both the radical
and this centralizer; the orbit congruence excludes quotient orders two
and eight, leaving one, four or sixteen.

Source: Fong--Seitz I (1973), (6G), printed p.50, first paragraph. These
are the actual normal quotient inputs to its irreducibility step. The
exclusion of the two nontrivial orders, whole-radical centrality and the
subsequent normalizer contradiction remain to be proved. Original-factor
and Chapter 12 applications are in LinearPairCubicSectionSource and
SourceSelection/LinearPairCubicSectionChapter12.
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem reflection_remainder (i : Fin 2) :
    rightConjugate (simpleRemainder Q split i)
      (representative (Q.simple i) : X ⧸ Q.D) = simpleRemainder Q split i := by
  have hs : Q.simple i*Q.simple i = 1 := by
    simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2
  rw [simpleRemainder, rightConjugate_inf,
    ← unipotentConjugate_eq split _ _ (representative_spec _),
    unipotentConjugate_right split _ _ _ (representative_spec _), hs,
    unipotentConjugate_one, inf_comm]

/-- Commutators of the seven-root radical belong to its middle five roots. -/
theorem radical_commutator_le_middleFive (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hA : ⁅simpleRoot Q split j,simpleRoot Q split j⁆ = ⊥) :
    ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ ≤ middleFive Q split i j := by
  have hV : ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ ≤
      simpleRemainder Q split j :=
    (commutator_mono inf_le_left inf_le_left).trans
      (unipotent_commutator_le_remainder Q split j hKj hA)
  have hh := comap_mono (f := (MulAut.conj
    (representative (Q.simple i) : X ⧸ Q.D)).toMonoidHom) hV
  change rightConjugate ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ _ ≤
    rightConjugate (simpleRemainder Q split j) _ at hh
  have he (A : Subgroup (X ⧸ Q.D)) (n : X ⧸ Q.D) :
      rightConjugate ⁅A,A⁆ n = ⁅rightConjugate A n,rightConjugate A n⁆ := by
    simp only [rightConjugate,comap_equiv_eq_map_symm',map_commutator]
  rw [he,reflection_remainder] at hh
  rw [middleFive_eq_radical_intersection Q split hm i j hij]
  exact le_inf (le_inf (commutator_le_self _) hV) hh

private theorem unipotent_square_mem_remainder (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hE : IsElementaryAbelian 2 (simpleRoot Q split j))
    (x : X ⧸ Q.D) (hx : x ∈ split.U) : x^2 ∈ simpleRemainder Q split j := by
  let := hE
  have hp : x ∈ (simpleRoot Q split j : Set (X ⧸ Q.D)) *
      (simpleRemainder Q split j : Set (X ⧸ Q.D)) :=
    (simpleRoot_mul_remainder Q split j).symm ▸ hx
  obtain ⟨a,ha,v,hv,rfl⟩ := hp
  have hnorm := (remainder_parabolic_normalizes Q split j hKj)
    ((simpleRoot_le Q split j).trans
      (split.U_le.trans (Q.tits.B_le_standardParabolic _)) ha)
  have hav := (mem_normalizer_iff.mp hnorm v).mp hv
  have ha2 : a*a = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha2
  simpa only [pow_two,hai,mul_assoc] using mul_mem hav hv

/-- Squares also lie in the five-root subgroup when the opposite root is elementary. -/
theorem radical_square_mem_middleFive (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hE : IsElementaryAbelian 2 (simpleRoot Q split j))
    (x : X ⧸ Q.D) (hx : x ∈ simpleRemainder Q split i) :
    x^2 ∈ middleFive Q split i j := by
  rw [middleFive_eq_radical_intersection Q split hm i j hij]
  refine ⟨⟨pow_mem hx 2,unipotent_square_mem_remainder Q split j hKj hE x hx.1⟩,?_⟩
  let n : X ⧸ Q.D := representative (Q.simple i)
  have hnx : n*x*n⁻¹ ∈ simpleRemainder Q split i := by
    change x ∈ rightConjugate (simpleRemainder Q split i)
      (representative (Q.simple i) : X ⧸ Q.D)
    rwa [reflection_remainder]
  have hh := unipotent_square_mem_remainder Q split j hKj hE _ hnx.1
  change n*x^2*n⁻¹ ∈ simpleRemainder Q split j
  simpa only [pow_two,mul_assoc,inv_mul_cancel_left] using hh

/-- Every normal quotient whose kernel contains the five middle roots is elementary abelian. -/
theorem middleFive_overgroup_quotient_elementary (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hE : IsElementaryAbelian 2 (simpleRoot Q split j))
    (C : Subgroup (X ⧸ Q.D)) (hJC : middleFive Q split i j ≤ C)
    [(C.subgroupOf (simpleRemainder Q split i)).Normal] :
    IsElementaryAbelian 2 ((simpleRemainder Q split i) ⧸
      C.subgroupOf (simpleRemainder Q split i)) := by
  let := hE
  refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
  · apply Normal.quotient_commutative_iff_commutator_le.mpr
    intro x hx
    apply hJC
    apply radical_commutator_le_middleFive Q split hm i j hij hKj
      (commutator_self_eq_bot_iff.mpr inferInstance)
    rw [←map_subtype_commutator]
    exact mem_map_of_mem _ hx
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    induction x using QuotientGroup.induction_on with
    | H x =>
      rw [←QuotientGroup.mk_pow]
      exact (QuotientGroup.eq_one_iff _).mpr
        (hJC (radical_square_mem_middleFive Q split hm i j hij hKj hE x x.property))

/-- In the degree-one branch the literal five-root quotient has order sixteen. -/
theorem binary_middleFive_quotient_card (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hi : Nat.card (simpleRoot Q split i) = 2)
    (hj : Nat.card (simpleRoot Q split j) = 4) :
    Nat.card ((simpleRemainder Q split i) ⧸
      (middleFive Q split i j).subgroupOf (simpleRemainder Q split i)) = 16 := by
  have hu := unipotent_card_even Q split 4 hm
  have he : Nat.card (simpleRoot Q split 0)*Nat.card (simpleRoot Q split 1) = 8 := by
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;>
      rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · exact (hij rfl).elim
    · rw [hi,hj]
    · rw [hi,hj]
    · exact (hij rfl).elim
  rw [he,unipotent_card_simple Q split i,hi] at hu
  have hv : Nat.card (simpleRemainder Q split i) = 2048 := by omega
  have hJ : Nat.card (middleFive Q split i j) = 128 := by
    rw [middleFive_card Q split hm i j hij,hi,hj]
    norm_num
  have hh := relIndex_mul_relIndex (⊥ : Subgroup (X ⧸ Q.D)) (middleFive Q split i j)
    (simpleRemainder Q split i) bot_le (middleFive_le_remainder Q split hm i j hij)
  rw [relIndex_bot_left,relIndex_bot_left,hv,hJ] at hh
  change (middleFive Q split i j).relIndex (simpleRemainder Q split i) = 16
  omega

/-- Any subgroup between the five roots and the full radical is normal in the radical. -/
theorem middleFive_overgroup_normalized (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hA : ⁅simpleRoot Q split j,simpleRoot Q split j⁆ = ⊥)
    (C : Subgroup (X ⧸ Q.D)) (hJC : middleFive Q split i j ≤ C)
    (hCV : C ≤ simpleRemainder Q split i) :
    simpleRemainder Q split i ≤ normalizer (C : Set (X ⧸ Q.D)) := by
  apply le_normalizer_iff_commutator_le_right.mpr
  exact (commutator_mono le_rfl hCV).trans
    ((radical_commutator_le_middleFive Q split hm i j hij hKj hA).trans hJC)

/-- The centralizer of the middle odd root inside the actual radical. -/
@[expose] def middleRootCentralizer (i j : Fin 2) : Subgroup (X ⧸ Q.D) :=
  simpleRemainder Q split i ⊓
    centralizer (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) : Set (X ⧸ Q.D))

/-- The middle-root centralizer is normal in the entire marked parabolic.
The proof uses the derived-subgroup bound for radical normality, the actual
perpendicular rank-one commutator, and full Cartan normalization. -/
theorem middleRootCentralizer_parabolic_normalizes (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hA : ⁅simpleRoot Q split j,simpleRoot Q split j⁆ = ⊥)
    (s : HexagonStructure.RootReflection Q split i)
    (hJC : middleFive Q split i j ≤ middleRootCentralizer Q split i j)
    (hperp : ⁅rankOne Q split i,
      rightConjugate (rankOne Q split i)
        (representative (Q.simple j*Q.simple i*Q.simple j) : X ⧸ Q.D)⁆ = ⊥) :
    Q.tits.standardParabolic {Q.simple i} ≤
      normalizer (middleRootCentralizer Q split i j : Set (X ⧸ Q.D)) := by
  let A := rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)
  let C := middleRootCentralizer Q split i j
  have hRC : rankOne Q split i ≤ centralizer (A : Set (X ⧸ Q.D)) :=
    (commutator_eq_bot_iff_le_centralizer.mp hperp).trans
      (centralizer_le (comap_mono (show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left)))
  have hRN : rankOne Q split i ≤ normalizer (C : Set (X ⧸ Q.D)) :=
    (le_inf ((rankOne_le_parabolic Q split i).trans
      (remainder_parabolic_normalizes Q split i hKi))
      (hRC.trans (centralizer (A : Set (X ⧸ Q.D))).le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
  have hVN := middleFive_overgroup_normalized Q split hm i j hij hKj hA C hJC inf_le_left
  have hUN : split.U ≤ normalizer (C : Set (X ⧸ Q.D)) := by
    intro x hx
    have hp : x ∈ (simpleRoot Q split i : Set (X ⧸ Q.D)) *
        (simpleRemainder Q split i : Set (X ⧸ Q.D)) :=
      (simpleRoot_mul_remainder Q split i).symm ▸ hx
    obtain ⟨a,ha,v,hv,rfl⟩ := hp
    exact mul_mem (hRN (mem_sup_left ha)) (hVN hv)
  have hHN : Q.tits.B ⊓ Q.tits.N ≤ normalizer (C : Set (X ⧸ Q.D)) :=
    (le_inf (inf_le_left.trans ((Q.tits.B_le_standardParabolic _).trans
      (remainder_parabolic_normalizes Q split i hKi)))
      ((rootAt_torus_normalizes Q split i _).trans
        (normalizer_le_normalizer_centralizer A))).trans inf_normalizer_le_normalizer_inf
  have hBN : Q.tits.B ≤ normalizer (C : Set (X ⧸ Q.D)) := by
    rw [←split.factorization]
    exact sup_le hUN hHN
  apply Q.tits.standardParabolic_le _ hBN
  intro w hw
  have hw' : w = Q.simple i := Set.mem_singleton_iff.mp hw
  subst w
  exact Q.tits.bruhatCell_subset_of_mem _ hBN
    (Q.tits.representative_mem_bruhatCell _ s.val s.class_eq)
    (hRN s.mem_rankOne)

/-- The centralizer quotient has order dividing sixteen in the degree-one branch. -/
theorem binary_middleRootCentralizer_quotient_card_dvd (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hi : Nat.card (simpleRoot Q split i) = 2)
    (hj : Nat.card (simpleRoot Q split j) = 4)
    (hJC : middleFive Q split i j ≤ middleRootCentralizer Q split i j) :
    Nat.card ((simpleRemainder Q split i) ⧸
      (middleRootCentralizer Q split i j).subgroupOf (simpleRemainder Q split i)) ∣ 16 := by
  rw [←binary_middleFive_quotient_card Q split hm i j hij hi hj]
  exact index_dvd_of_le (subgroupOf_mono _ hJC)

/-- The separating cubic actor eliminates the index-two and index-eight
possibilities. The middle-root centralizer quotient has order 1, 4 or 16. -/
theorem separated_binary_middleRootCentralizer_index (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hi : Nat.card (simpleRoot Q split i) = 2)
    (hj : Nat.card (simpleRoot Q split j) = 4)
    (c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) (horder : orderOf c = 3)
    (hc : ∀ w : Weyl Q,
      (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) ∧
      rootAt Q split j w ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥)
    (hJC : middleFive Q split i j ≤ middleRootCentralizer Q split i j)
    (hnc : (c : X ⧸ Q.D) ∈ normalizer (middleRootCentralizer Q split i j : Set (X ⧸ Q.D))) :
    (middleRootCentralizer Q split i j).relIndex (simpleRemainder Q split i) = 1 ∨
    (middleRootCentralizer Q split i j).relIndex (simpleRemainder Q split i) = 4 ∨
    (middleRootCentralizer Q split i j).relIndex (simpleRemainder Q split i) = 16 := by
  let V := simpleRemainder Q split i
  let C := middleRootCentralizer Q split i j
  have hfixV := (octagon_separated_root_centralizer_orders Q split hm i j hij c hc).1
  rw [hi] at hfixV
  have hfixle : V ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) ≤ C := by
    rw [←separated_radical_centralizer_sup Q split hm i j hij c hc]
    apply le_trans _ hJC
    exact sup_le (sup_le
      (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_left)))
      (le_sup_of_le_left (le_sup_of_le_left le_sup_right))) le_sup_right
  have hfixC : C ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) =
      V ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) :=
    le_antisymm (inf_le_inf_right _ inf_le_left) (le_inf hfixle inf_le_right)
  have hp : IsPGroup 3 (zpowers (c : X ⧸ Q.D)) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,orderOf_coe,horder]; rfl)
  have hmod := card_modEq_card_inf_centralizer (zpowers (c : X ⧸ Q.D)) C hp
    (zpowers_le.mpr hnc)
  rw [zpowers_eq_closure,centralizer_closure,hfixC,hfixV] at hmod
  have hd : C.relIndex V ∣ 16 :=
    binary_middleRootCentralizer_quotient_card_dvd Q split hm i j hij hi hj hJC
  have h16 : Nat.card V = 128*16 := by
    have hJ : Nat.card (middleFive Q split i j) = 128 := by
      rw [middleFive_card Q split hm i j hij,hi,hj]; norm_num
    have hh := relIndex_mul_relIndex (⊥ : Subgroup (X ⧸ Q.D))
      (middleFive Q split i j) V bot_le (middleFive_le_remainder Q split hm i j hij)
    rw [relIndex_bot_left,relIndex_bot_left,hJ] at hh
    have hq := binary_middleFive_quotient_card Q split hm i j hij hi hj
    change (middleFive Q split i j).relIndex V = 16 at hq
    rw [hq] at hh
    exact hh.symm
  have hmC := relIndex_mul_relIndex (⊥ : Subgroup (X ⧸ Q.D)) C V bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,h16] at hmC
  change Nat.card C % 3 = 8 % 3 at hmod
  have hle : C.relIndex V ≤ 16 := Nat.le_of_dvd (by decide) hd
  change C.relIndex V = 1 ∨ C.relIndex V = 4 ∨ C.relIndex V = 16
  interval_cases C.relIndex V <;> omega

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
