module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicMiddleExclusion
/-!
# The degree-one octagon normalizer contradiction

When the middle odd root is central in the radical, reflection makes the
three fixed odd roots central in the five-root subgroup J. If the two
remaining roots do not commute, Cartan irreducibility makes their mutual
centralizers trivial. Their pairing then identifies Z(J) with exactly
the three fixed roots. Since the radical normalizes J, it normalizes
this center, and the coprime fixed-normalizer theorem makes it centralize
all three fixed roots. Rank-one reflection contradicts that conclusion.
Thus J is abelian, and the perpendicular-root argument excludes it.

Source: Fong--Seitz I (1973), (6G), printed p.50, degree-one normalizer
argument. LinearPairCubicExclusionSource combines this with the proved
whole-radical centrality result and constructs every local and cubic input
from the original factor quotients. Its Chapter 12 consumer excludes the
binary linear endpoint on the literal marked quotient. Higher-degree (6G)
and the exhaustive marked comparison remain separate obligations.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup
open scoped Pointwise MatrixGroups IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
private theorem ssq (i : Fin 2) : Q.simple i*Q.simple i = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2
private theorem right_rep (i : Fin 2) (v w : Weyl Q) :
    rightConjugate (rootAt Q split i v) (representative w : X ⧸ Q.D) =
      rootAt Q split i (v*w) := rootAt_right Q split i v w _ (representative_spec _)
private theorem right_simple (i : Fin 2) (w : Weyl Q) :
    rightConjugate (simpleRoot Q split i) (representative w : X ⧸ Q.D) =
      rootAt Q split i w := rfl
private theorem right_comm (A B : Subgroup (X ⧸ Q.D)) (w : Weyl Q) :
    rightConjugate ⁅A,B⁆ (representative w : X ⧸ Q.D) =
      ⁅rightConjugate A (representative w : X ⧸ Q.D),
        rightConjugate B (representative w : X ⧸ Q.D)⁆ := by
  simp only [rightConjugate,comap_equiv_eq_map_symm',map_commutator]
private theorem right_bot (w : Weyl Q) :
    rightConjugate (⊥ : Subgroup (X ⧸ Q.D)) (representative w : X ⧸ Q.D) = ⊥ := by
  simp only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_bot]
private theorem fourth_root (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j) :
    rootAt Q split i (Q.simple j*Q.simple i*Q.simple j*Q.simple i) =
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) := by
  rw [←right_rep]
  exact perpendicular_root_stable Q split hm i j hij _ (representative_spec _)


private theorem paired_center {Y : Type*} [Group Y] (M A B J : Subgroup Y)
    (he : M ⊔ A ⊔ B = J) (hM : M ≤ centralizer (J : Set Y))
    (hAA : A ≤ centralizer (A : Set Y))
    (hAB : ⁅B,A⁆ ≤ M)
    (hAz : A ⊓ centralizer (B : Set Y) = ⊥)
    (hBz : B ⊓ centralizer (A : Set Y) = ⊥) :
    J ⊓ centralizer (J : Set Y) = M := by
  have hMJ : M ≤ J := he ▸ le_sup_of_le_left le_sup_left
  have hAJ : A ≤ J := he ▸ le_sup_of_le_left le_sup_right
  have hBJ : B ≤ J := he ▸ le_sup_right
  let N := M ⊔ A
  have hconj (b : Y) (hb : b ∈ B) :
      N.map (MulAut.conj b).toMonoidHom ≤ N := by
    rw [Subgroup.map_sup]
    apply sup_le
    · apply map_le_iff_le_comap.mpr
      intro m hm
      change b*m*b⁻¹ ∈ N
      rw [mem_centralizer_iff.mp (hM hm) b (hBJ hb),mul_inv_cancel_right]
      exact mem_sup_left hm
    · apply map_le_iff_le_comap.mpr
      intro a ha
      have hc := mul_mem_sup (hAB (commutator_mem_commutator hb ha)) ha
      change b*a*b⁻¹ ∈ N
      simpa only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one] using hc
  have hBN : B ≤ normalizer (N : Set Y) := by
    intro b hb
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · intro hx
      exact hconj b hb (mem_map_of_mem (MulAut.conj b).toMonoidHom hx)
    · intro hx
      have hh := hconj b⁻¹ (inv_mem hb)
        (mem_map_of_mem (MulAut.conj b⁻¹).toMonoidHom hx)
      change b⁻¹*(b*x*b⁻¹)*(b⁻¹)⁻¹ ∈ N at hh
      simpa only [inv_inv,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using hh
  have hAM : A ≤ normalizer (M : Set Y) :=
    (hAJ.trans (le_centralizer_iff.mp hM)).trans (Subgroup.centralizer_le_normalizer _)
  apply le_antisymm
  · intro x hx
    have hp : x ∈ (N : Set Y)*(B : Set Y) := by
      rw [←coe_mul_of_right_le_normalizer_left N B hBN]
      exact he.symm ▸ hx.1
    obtain ⟨ma,hma,b,hb,rfl⟩ := hp
    have hp : ma ∈ (M : Set Y)*(A : Set Y) := by
      rw [←coe_mul_of_right_le_normalizer_left M A hAM]
      exact hma
    obtain ⟨m,hm,a,ha,rfl⟩ := hp
    have hab : a*b ∈ centralizer (J : Set Y) := by
      have hh := mul_mem (inv_mem (hM hm)) hx.2
      simpa only [mul_assoc,inv_mul_cancel_left] using hh
    have hbA : b ∈ centralizer (A : Set Y) := by
      have hh := mul_mem (inv_mem (hAA ha)) (centralizer_le hAJ hab)
      simpa only [inv_mul_cancel_left] using hh
    have hb1 : b = 1 := mem_bot.mp (hBz ▸ (show b ∈ B ⊓ centralizer (A : Set Y) from ⟨hb,hbA⟩))
    have haB : a ∈ centralizer (B : Set Y) := by
      simpa only [hb1,mul_one] using centralizer_le hBJ hab
    have ha1 : a = 1 := mem_bot.mp (hAz ▸ (show a ∈ A ⊓ centralizer (B : Set Y) from ⟨ha,haB⟩))
    simp only [ha1,hb1,mul_one]
    exact hm
  · exact le_inf hMJ hM

/-- Whole-radical centrality of the middle odd root forces the three fixed
odd roots to centralize the five-root subgroup. -/
theorem fixedOddRoots_central_of_middle_central
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hmid : rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) ≤
      centralizer (simpleRemainder Q split i : Set (X ⧸ Q.D)))
    (hab : IsMulCommutative (fixedOddRoots Q split i j)) :
    fixedOddRoots Q split i j ≤ centralizer (middleFive Q split i j : Set (X ⧸ Q.D)) := by
  let V := simpleRemainder Q split i
  let J := middleFive Q split i j
  let A := rootAt Q split i (Q.simple j)
  let B := rootAt Q split j (Q.simple i*Q.simple j)
  let C := rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)
  let D := rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)
  let E := rootAt Q split i (Q.simple j*Q.simple i)
  let M := fixedOddRoots Q split i j
  let := hab
  have hJV : J ≤ V := middleFive_le_remainder Q split hm i j hij
  have hAM : A ≤ M := le_sup_of_le_left le_sup_left
  have hCM : C ≤ M := le_sup_of_le_left le_sup_right
  have hEM : E ≤ M := le_sup_right
  have hC : J ≤ centralizer (C : Set (X ⧸ Q.D)) :=
    hJV.trans (le_centralizer_iff.mp hmid)
  have hEnd : rootAt Q split j (Q.simple i) ≤ V := by
    intro b hb
    have hp : b ∈ (simpleRoot Q split j : Set (X ⧸ Q.D))*
        ((J : Set (X ⧸ Q.D))*(rootAt Q split j (Q.simple i) : Set (X ⧸ Q.D))) :=
      ⟨1,one_mem _,b,⟨1,one_mem _,b,hb,one_mul _⟩,one_mul _⟩
    rwa [←radical_end_product Q split hm i j hij] at hp
  have hEC (R : Subgroup (X ⧸ Q.D)) (hRV : R ≤ V) :
      rightConjugate R (representative (Q.simple j) : X ⧸ Q.D) ≤
        centralizer (E : Set (X ⧸ Q.D)) := by
    have hz := commutator_eq_bot_iff_le_centralizer.mpr (hRV.trans (le_centralizer_iff.mp hmid))
    have hh := congrArg (fun K => rightConjugate K (representative (Q.simple j) : X ⧸ Q.D)) hz
    rw [right_comm,right_rep,right_bot] at hh
    simp only [mul_assoc,ssq,mul_one] at hh
    exact commutator_eq_bot_iff_le_centralizer.mp hh
  have hBE : B ≤ centralizer (E : Set (X ⧸ Q.D)) := by
    simpa only [right_rep,B] using hEC _ hEnd
  have hDE : D ≤ centralizer (E : Set (X ⧸ Q.D)) := by
    have hh := hEC D ((le_sup_of_le_left le_sup_right).trans hJV)
    dsimp only [D] at hh
    rw [right_rep,fourth_root Q split hm j i hij.symm] at hh
    exact hh
  have hJE : J ≤ centralizer (E : Set (X ⧸ Q.D)) := by
    have hME := M.le_centralizer.trans (centralizer_le hEM)
    exact sup_le (sup_le (sup_le (sup_le (hAM.trans hME) hBE)
      (hCM.trans hME)) hDE) (hEM.trans hME)
  have hJA : J ≤ centralizer (A : Set (X ⧸ Q.D)) := by
    have hz := commutator_eq_bot_iff_le_centralizer.mpr hJE
    have hh := congrArg (fun K => rightConjugate K (representative (Q.simple i) : X ⧸ Q.D)) hz
    rw [right_comm,middleFive_reflection Q split hm i j hij,right_rep,right_bot] at hh
    simp only [mul_assoc,ssq,mul_one] at hh
    exact commutator_eq_bot_iff_le_centralizer.mp hh
  exact sup_le (sup_le (le_centralizer_iff.mp hJA) (le_centralizer_iff.mp hC))
    (le_centralizer_iff.mp hJE)


private theorem fixed_not_central
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (s : HexagonStructure.RootReflection Q split j)
    (hperp : ⁅simpleRoot Q split i,
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ = ⊥)
    (hlong : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ ≠ ⊥) :
    ¬ simpleRemainder Q split i ≤ centralizer (fixedOddRoots Q split i j : Set (X ⧸ Q.D)) := by
  intro hVM
  let C := rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)
  let E := rootAt Q split i (Q.simple j*Q.simple i)
  have hU : simpleRoot Q split j ≤ simpleRemainder Q split i := by
    intro x hx
    have hp : x ∈ (simpleRoot Q split j : Set (X ⧸ Q.D))*
        ((middleFive Q split i j : Set (X ⧸ Q.D))*(rootAt Q split j (Q.simple i) : Set (X ⧸ Q.D))) :=
      ⟨x,hx,1,⟨1,one_mem _,1,one_mem _,one_mul _⟩,mul_one _⟩
    rwa [←radical_end_product Q split hm i j hij] at hp
  have hUC : simpleRoot Q split j ≤ centralizer (C : Set (X ⧸ Q.D)) :=
    (hU.trans hVM).trans (centralizer_le (show C ≤ fixedOddRoots Q split i j from le_sup_of_le_left le_sup_right))
  have hUE : simpleRoot Q split j ≤ centralizer (E : Set (X ⧸ Q.D)) :=
    (hU.trans hVM).trans (centralizer_le (show E ≤ fixedOddRoots Q split i j from le_sup_right))
  have hOC : rootAt Q split j (Q.simple j) ≤ centralizer (C : Set (X ⧸ Q.D)) := by
    have hh := congrArg (fun K => rightConjugate K (representative (Q.simple j) : X ⧸ Q.D))
      (commutator_eq_bot_iff_le_centralizer.mpr hUE)
    rw [right_comm,right_simple,right_rep,right_bot] at hh
    exact commutator_eq_bot_iff_le_centralizer.mp hh
  have hRC : rankOne Q split j ≤ centralizer (C : Set (X ⧸ Q.D)) := sup_le hUC hOC
  have hEC : E = C := by
    have hh := rightConjugate_eq_self C (Subgroup.centralizer_le_normalizer _ (hRC s.mem_rankOne))
    dsimp only [C] at hh
    rw [rootAt_right Q split i _ _ s.val s.class_eq] at hh
    simpa only [E,C,mul_assoc,ssq,mul_one] using hh
  have hAC : rootAt Q split i (Q.simple j) = C := by
    have hh := congrArg (fun K => rightConjugate K (representative (Q.simple i) : X ⧸ Q.D)) hEC
    dsimp only [E,C] at hh
    rw [right_rep,right_rep,fourth_root Q split hm i j hij] at hh
    simpa only [E,C,mul_assoc,ssq,mul_one] using hh
  apply hlong
  rw [hAC]
  exact hperp

private theorem middle_abelian_of_fixed_normalizer
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μj : localGroup Q split j ≃* PSL(2,F))
    (hM : fixedOddRoots Q split i j ≤ centralizer (middleFive Q split i j : Set (X ⧸ Q.D)))
    (hNC : simpleRemainder Q split i ⊓ normalizer (fixedOddRoots Q split i j : Set (X ⧸ Q.D)) =
      simpleRemainder Q split i ⊓ centralizer (fixedOddRoots Q split i j : Set (X ⧸ Q.D)))
    (hnot : ¬ simpleRemainder Q split i ≤ centralizer (fixedOddRoots Q split i j : Set (X ⧸ Q.D))) :
    IsMulCommutative (middleFive Q split i j) := by
  let V := simpleRemainder Q split i
  let J := middleFive Q split i j
  let M := fixedOddRoots Q split i j
  let B := rootAt Q split j (Q.simple i*Q.simple j)
  let D := rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)
  let H := Q.tits.B ⊓ Q.tits.N
  have hgen : M ⊔ B ⊔ D = J := by
    dsimp only [M,B,D,J,fixedOddRoots,middleFive]
    ac_rfl
  have hBJ : B ≤ J := hgen ▸ le_sup_of_le_left le_sup_right
  have hDJ : D ≤ J := hgen ▸ le_sup_right
  have hMJ : M ≤ J := hgen ▸ le_sup_of_le_left le_sup_left
  have hcomm (w : Weyl Q) : rootAt Q split j w ≤ centralizer (rootAt Q split j w : Set (X ⧸ Q.D)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    have hh := congrArg (fun K => rightConjugate K (representative w : X ⧸ Q.D))
      (simpleRoot_commutator_eq_bot_of_linear Q split j μj)
    rw [right_comm,right_simple,right_bot] at hh
    exact hh
  by_cases hBD : ⁅B,D⁆ = ⊥
  · have hJB : J ≤ centralizer (B : Set (X ⧸ Q.D)) := by
      rw [←hgen]
      exact sup_le (sup_le (hM.trans (centralizer_le hBJ)) (hcomm _))
        (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hBD))
    have hJD : J ≤ centralizer (D : Set (X ⧸ Q.D)) := by
      rw [←hgen]
      exact sup_le (sup_le (hM.trans (centralizer_le hDJ))
        (commutator_eq_bot_iff_le_centralizer.mp hBD)) (hcomm _)
    apply le_centralizer_iff_isMulCommutative.mp
    change J ≤ centralizer (J : Set (X ⧸ Q.D))
    nth_rw 1 [←hgen]
    exact sup_le (sup_le hM (le_centralizer_iff.mp hJB)) (le_centralizer_iff.mp hJD)
  · have hBDM : ⁅B,D⁆ ≤ M := by
      have hh := comap_mono (f := (MulAut.conj
        (representative (Q.simple i*Q.simple j) : X ⧸ Q.D)).toMonoidHom)
        (distance_two_commutator_le Q split hm j i hij.symm hKj)
      change rightConjugate _ _ ≤ rightConjugate _ _ at hh
      rw [right_comm,right_simple,right_rep,right_rep] at hh
      simp only [←mul_assoc,fourth_root Q split hm j i hij.symm] at hh
      exact hh.trans (le_sup_of_le_left le_sup_right)
    have hkernel (v w : Weyl Q)
        (hne : ⁅rootAt Q split j v,rootAt Q split j w⁆ ≠ ⊥) :
        rootAt Q split j v ⊓ centralizer (rootAt Q split j w : Set (X ⧸ Q.D)) = ⊥ := by
      by_contra hh
      have he := QuadrangleStructure.rootAt_eq_of_torus_invariant Q split j μj hKj v
        _ inf_le_left hh ((le_inf (rootAt_torus_normalizes Q split j v)
          ((rootAt_torus_normalizes Q split j w).trans (normalizer_le_normalizer_centralizer _))).trans
            inf_normalizer_le_normalizer_inf)
      exact hne (commutator_eq_bot_iff_le_centralizer.mpr (he ▸ inf_le_right))
    have hZ : J ⊓ centralizer (J : Set (X ⧸ Q.D)) = M :=
      paired_center M B D J hgen hM (hcomm _) (by rwa [commutator_comm])
        (hkernel _ _ hBD) (hkernel _ _ (by rwa [commutator_comm]))
    have hVJ := middleFive_normalized_by_remainder Q split hm i j hij hKj
    have hVM : V ≤ normalizer (M : Set (X ⧸ Q.D)) := by
      rw [←hZ]
      exact (le_inf hVJ (hVJ.trans (normalizer_le_normalizer_centralizer _))).trans
        inf_normalizer_le_normalizer_inf
    have hVC : V ≤ centralizer (M : Set (X ⧸ Q.D)) := by
      have hh : V ≤ V ⊓ normalizer (M : Set (X ⧸ Q.D)) := le_inf le_rfl hVM
      rw [hNC] at hh
      exact hh.trans inf_le_right
    exact (hnot hVC).elim

/-- The whole-radical centrality branch also contradicts the binary
perpendicular-root relation, through the fixed-subgroup normalizer. -/
theorem separated_binary_normalizer_exclusion
    {F E : Type*} [Field F] [Finite F] [CharP F 2]
    [Field E] [Finite E] [CharP E 2]
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,F))
    (μj : localGroup Q split j ≃* PSL(2,E))
    (si : HexagonStructure.RootReflection Q split i)
    (sj : HexagonStructure.RootReflection Q split j)
    (hF : Nat.card F = 2)
    (hi : Nat.card (simpleRoot Q split i) = 2)
    (c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) (hc3 : orderOf c = 3)
    (hc : ∀ w : Weyl Q,
      (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) ∧
      rootAt Q split j w ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥)
    (hne : ⁅simpleRoot Q split j,
      rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)⁆ ≠ ⊥)
    (hmid : rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) ≤
      centralizer (simpleRemainder Q split i : Set (X ⧸ Q.D))) : False := by
  obtain ⟨hab,hperp⟩ := separated_linear_radical_abelian Q split hm i j hij hKi μi si
    (a := 1) (by decide) hF hi c hc
  have hMab : IsMulCommutative (fixedOddRoots Q split i j) := by
    have he := separated_radical_centralizer_sup Q split hm i j hij c hc
    exact (congrArg (fun D : Subgroup (X ⧸ Q.D) => IsMulCommutative D) he).mpr hab
  have hM := fixedOddRoots_central_of_middle_central Q split hm i j hij hmid hMab
  have hN := separated_fixedOddRoots_normalizer Q split hm i j hij hKi μi si
    (a := 1) (by decide) hF hi c hc3 hc
  have hnot := fixed_not_central Q split hm i j hij sj hperp
    (separated_long_commutator_ne_bot Q split hm i j hij si
      (separated_distance_two_commutator Q split hm i j hij hKi c hc))
  have hJ := middle_abelian_of_fixed_normalizer Q split hm i j hij hKj μj hM hN hnot
  exact separated_binary_middleFive_not_abelian Q split hm i j hij hKi hKj μj si hi c hc3 hc hperp hne hJ
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
