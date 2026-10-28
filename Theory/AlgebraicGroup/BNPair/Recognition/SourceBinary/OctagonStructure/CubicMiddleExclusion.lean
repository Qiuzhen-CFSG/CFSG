module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicMiddleAbelian
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicCentralizerDichotomy
/-!
# Excluding an abelian five-root subgroup in the binary octagon

If the five middle roots commute, reflection makes the opposite middle
root central in the other seven-root radical. Its perpendicular commutator
is therefore central and supported on three roots. Coprime decomposition
separates its moving even coordinate from its fixed odd coordinates.
The nonzero long odd-root commutator eliminates one fixed coordinate,
and reflection eliminates the other. Cartan irreducibility would then
make the perpendicular commutator the whole remaining even root, which
contradicts centrality after reflection.

Source: Fong--Seitz I (1973), (6G), printed p.50, the final root argument
of the degree-one branch. Applied to the previously proved abelianness
in the proper-centralizer branch, this excludes index sixteen. The
original-factor and Chapter 12 applications are in LinearPairCubicCentralitySource
and SourceSelection/LinearPairCubicCentralityChapter12. The whole-radical
centrality case is handled in CubicNormalizerExclusion; the higher-degree
argument still requires its subsequent root calculations.
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

/-- Abelianness of the five middle roots makes the opposite middle root
central in its entire seven-root radical. -/
theorem middle_opposite_central_of_abelian
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hab : IsMulCommutative (middleFive Q split i j)) :
    rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) ≤
      centralizer (simpleRemainder Q split j : Set (X ⧸ Q.D)) := by
  let J := middleFive Q split i j
  let D := rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)
  let n : X ⧸ Q.D := representative (Q.simple j)
  let := hab
  have hDJ : D ≤ J := le_sup_of_le_left le_sup_right
  have hJD : ⁅J,D⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (J.le_centralizer.trans (centralizer_le hDJ))
  have hDn : rightConjugate D n = D :=
    perpendicular_root_stable Q split hm j i hij.symm _ (representative_spec _)
  have hJnD : rightConjugate J n ≤ centralizer (D : Set (X ⧸ Q.D)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    have hh := congrArg (fun A => rightConjugate A n) hJD
    change rightConjugate ⁅J,D⁆ (representative (Q.simple j) : X ⧸ Q.D) = _ at hh
    rw [right_comm,right_bot] at hh
    rwa [hDn] at hh
  have hAJ : rootAt Q split i (Q.simple j) ≤ J :=
    le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_left))
  have hBJ : rootAt Q split j (Q.simple i*Q.simple j) ≤ J :=
    le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_right))
  have hAn : simpleRoot Q split i ≤ rightConjugate J n := by
    have hh := comap_mono (f := (MulAut.conj n).toMonoidHom) hAJ
    change rightConjugate (rootAt Q split i (Q.simple j)) n ≤ rightConjugate J n at hh
    simpa only [n,right_rep,ssq,rootAt_one] using hh
  have hBn : rootAt Q split j (Q.simple i) ≤ rightConjugate J n := by
    have hh := comap_mono (f := (MulAut.conj n).toMonoidHom) hBJ
    change rightConjugate (rootAt Q split j (Q.simple i*Q.simple j)) n ≤ rightConjugate J n at hh
    simpa only [n,right_rep,mul_assoc,ssq,mul_one] using hh
  have hMJ : middleFive Q split j i ≤ J ⊔ rightConjugate J n :=
    sup_le (sup_le (sup_le (sup_le (hBn.trans le_sup_right)
      (le_sup_right.trans le_sup_left)) (hDJ.trans le_sup_left))
      ((le_sup_of_le_left (le_sup_of_le_left le_sup_right)).trans le_sup_left))
      (hBJ.trans le_sup_left)
  have hW : simpleRemainder Q split j ≤ J ⊔ rightConjugate J n := by
    intro x hx
    have hp : x ∈ (simpleRemainder Q split j : Set (X ⧸ Q.D)) := hx
    rw [radical_end_product Q split hm j i hij.symm] at hp
    obtain ⟨a,ha,_,⟨m,hm,b,hb,rfl⟩,rfl⟩ := hp
    exact mul_mem (mem_sup_right (hAn ha))
      (mul_mem (hMJ hm) (mem_sup_left (hAJ hb)))
  exact le_centralizer_iff.mp (hW.trans
    (sup_le (commutator_eq_bot_iff_le_centralizer.mp hJD) hJnD))

private theorem binary_centralizer_eq_bot {Y : Type*} [Group Y]
    (A B : Subgroup Y) (hA : Nat.card A = 2) (hne : ⁅B,A⁆ ≠ ⊥) :
    A ⊓ centralizer (B : Set Y) = ⊥ := by
  apply eq_bot_iff.mpr
  intro a ha
  by_contra hane
  have hane' : a ≠ 1 := fun h => hane (mem_bot.mpr h)
  obtain ⟨u,hu,huni⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
  have hau : (⟨a,ha.1⟩ : A) = u := huni _ (fun h => hane' (congrArg Subtype.val h))
  apply hne
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mp
  intro z hz
  by_cases hz1 : z = 1
  · rw [hz1]; exact one_mem _
  · have hzu : (⟨z,hz⟩ : A) = u := huni _ (fun h => hz1 (congrArg Subtype.val h))
    have hza : z = a := congrArg Subtype.val (hzu.trans hau.symm)
    exact hza ▸ ha.2

private theorem sinv (i : Fin 2) : (Q.simple i)⁻¹ = Q.simple i :=
  inv_eq_of_mul_eq_one_right (ssq Q i)
private theorem scancel (i : Fin 2) (w : Weyl Q) : Q.simple i*(Q.simple i*w) = w := by
  rw [←mul_assoc,ssq,one_mul]
private theorem near_far_disjoint (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) :
    Disjoint (rootAt Q split i (Q.simple j))
      (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)) := by
  apply rootAt_disjoint Q split i _ _
  simp only [mul_inv_rev,sinv,mul_assoc,scancel,ssq,mul_one]
  have hh (b : Bool) := And.intro
    (wordLength_alternatingWord Q b (n := 1) (by omega))
    (wordLength_alternatingWord Q b (n := 2) (by omega))
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;>
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
  · exact (hij rfl).elim
  · have hl := hh true
    simp only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_true,mul_one] at hl
    exact hl.2.trans (congrArg (·+1) hl.1).symm
  · have hl := hh false
    simp only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,mul_one] at hl
    exact hl.2.trans (congrArg (·+1) hl.1).symm
  · exact (hij rfl).elim

/-- The abelian five-root alternative contradicts the actual nonzero
perpendicular even-root commutator. Coprime decomposition and reflection
remove its two fixed coordinates; Cartan irreducibility removes the third. -/
theorem separated_binary_middleFive_not_abelian
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μj : localGroup Q split j ≃* PSL(2,F))
    (s : HexagonStructure.RootReflection Q split i)
    (hi : Nat.card (simpleRoot Q split i) = 2)
    (c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) (hc3 : orderOf c = 3)
    (hc : ∀ w : Weyl Q,
      (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) ∧
      rootAt Q split j w ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥)
    (hperp : ⁅simpleRoot Q split i,
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ = ⊥)
    (hne : ⁅simpleRoot Q split j,
      rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)⁆ ≠ ⊥) :
    ¬ IsMulCommutative (middleFive Q split i j) := by
  intro hab
  let J := middleFive Q split i j
  let W := simpleRemainder Q split j
  let A := rootAt Q split i (Q.simple j)
  let B := rootAt Q split j (Q.simple i*Q.simple j)
  let C := rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)
  let D := rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)
  let K := ⁅simpleRoot Q split j,D⁆
  let H := Q.tits.B ⊓ Q.tits.N
  let T := zpowers (c : X ⧸ Q.D)
  let w := Q.simple i*Q.simple j*Q.simple i
  let n : X ⧸ Q.D := representative w
  let := hab
  have hAJ : A ≤ J := le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_left))
  have hBJ : B ≤ J := le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_right))
  have hCJ : C ≤ J := le_sup_of_le_left (le_sup_of_le_left le_sup_right)
  have hDJ : D ≤ J := le_sup_of_le_left le_sup_right
  have hJW : J ≤ W := by
    dsimp only [J,W]
    rw [middleFive_eq_radical_intersection Q split hm i j hij]
    exact inf_le_left.trans inf_le_right
  have hsupport (x : X ⧸ Q.D) (hx : x ∈ K) :
      x ∈ (A : Set (X ⧸ Q.D))*(B : Set (X ⧸ Q.D))*(C : Set (X ⧸ Q.D)) :=
    distance_four_commutator_support Q split hm j i hij.symm hKj x hx
  have hKABC : K ≤ A ⊔ B ⊔ C := by
    intro x hx
    obtain ⟨ab,⟨a,ha,b,hb,rfl⟩,z,hz,rfl⟩ := hsupport x hx
    exact mul_mem_sup (mul_mem_sup ha hb) hz
  have hKJ : K ≤ J := hKABC.trans (sup_le (sup_le hAJ hBJ) hCJ)
  have hDC : D ≤ centralizer (W : Set (X ⧸ Q.D)) :=
    middle_opposite_central_of_abelian Q split hm i j hij hab
  have hUC : simpleRoot Q split j ≤ normalizer (centralizer (W : Set (X ⧸ Q.D)) : Set _) :=
    ((simpleRoot_le Q split j).trans (split.U_le.trans ((Q.tits.B_le_standardParabolic _).trans
      (remainder_parabolic_normalizes Q split j hKj)))).trans
        (normalizer_le_normalizer_centralizer _)
  have hKC : K ≤ centralizer (W : Set (X ⧸ Q.D)) :=
    (commutator_mono le_rfl hDC).trans (le_normalizer_iff_commutator_le_right.mp hUC)
  have hHK : H ≤ normalizer (K : Set (X ⧸ Q.D)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq]
    change (⁅simpleRoot Q split j,D⁆).map (MulAut.conj g : (X ⧸ Q.D) →* (X ⧸ Q.D)) = K
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (torus_normalizes_simpleRoot Q split j hg),
      mem_normalizer_iff_map_conj_eq.mp (rootAt_torus_normalizes Q split j w hg)]
  have hTK : T ≤ normalizer (K : Set (X ⧸ Q.D)) := zpowers_le.mpr (hHK c.property)
  have hTC : centralizer (T : Set (X ⧸ Q.D)) =
      centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) := by
    dsimp only [T]
    rw [zpowers_eq_closure,centralizer_closure]
  have hAC : A ≤ centralizer (T : Set (X ⧸ Q.D)) := by
    rw [hTC]
    exact fun a ha => mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp (hc (Q.simple j)).1 a ha)
  have hCC : C ≤ centralizer (T : Set (X ⧸ Q.D)) := by
    rw [hTC]
    exact fun a ha => mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp (hc (Q.simple j*Q.simple i*Q.simple j)).1 a ha)
  have hAUi : A ⊓ centralizer (simpleRoot Q split i : Set (X ⧸ Q.D)) = ⊥ :=
    binary_centralizer_eq_bot A (simpleRoot Q split i)
      (by simpa only [A,rootAt,card_rightConjugate] using hi)
      (separated_long_commutator_ne_bot Q split hm i j hij s
        (separated_distance_two_commutator Q split hm i j hij hKi c hc))
  have hUiW : simpleRoot Q split i ≤ W := by
    have hh := comap_mono (f := (MulAut.conj (representative (Q.simple j) : X ⧸ Q.D)).toMonoidHom)
      (hAJ.trans hJW)
    change rightConjugate A (representative (Q.simple j) : X ⧸ Q.D) ≤
      rightConjugate W (representative (Q.simple j) : X ⧸ Q.D) at hh
    have he : rightConjugate W (representative (Q.simple j) : X ⧸ Q.D) = W := by
      dsimp only [W,simpleRemainder]
      rw [rightConjugate_inf,←unipotentConjugate_eq split _ _ (representative_spec _),
        unipotentConjugate_right split _ _ _ (representative_spec _),ssq,unipotentConjugate_one,inf_comm]
    simpa only [A,right_rep,ssq,rootAt_one,he] using hh
  have hfixC : K ⊓ centralizer (T : Set (X ⧸ Q.D)) ≤ C := by
    intro x hx
    obtain ⟨ab,⟨a,ha,b,hb,rfl⟩,z,hz,rfl⟩ := hsupport x hx.1
    have hbfix : b ∈ centralizer (T : Set (X ⧸ Q.D)) := by
      have hh := mul_mem (inv_mem (hAC ha)) (mul_mem hx.2 (inv_mem (hCC hz)))
      simpa only [mul_assoc,mul_inv_cancel_right,inv_mul_cancel_left,mul_inv_cancel,mul_one] using hh
    have hb1 : b = 1 := mem_bot.mp ((hc (Q.simple i*Q.simple j)).2 ▸
      (show b ∈ B ⊓ centralizer ({(c : X ⧸ Q.D)} : Set _) from ⟨hb,hTC ▸ hbfix⟩))
    have hxUi := (hKC hx.1)
    have haz : a*z ∈ centralizer (simpleRoot Q split i : Set (X ⧸ Q.D)) := by
      simpa only [hb1,mul_one] using (centralizer_le hUiW hxUi)
    have hzUi : z ∈ centralizer (simpleRoot Q split i : Set (X ⧸ Q.D)) :=
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hperp)) hz
    have haUi : a ∈ centralizer (simpleRoot Q split i : Set (X ⧸ Q.D)) := by
      simpa only [mul_inv_cancel_right] using mul_mem haz (inv_mem hzUi)
    have ha1 : a = 1 := mem_bot.mp (hAUi ▸ (show a ∈ A ⊓ centralizer (simpleRoot Q split i : Set _) from ⟨ha,haUi⟩))
    simp only [ha1,hb1,one_mul]
    exact hz
  have hKn : rightConjugate K n = K := by
    dsimp only [K,D,n,w]
    rw [right_comm,right_simple,right_rep]
    simp only [mul_assoc,scancel,ssq,rootAt_one,commutator_comm]
  have hCn : rightConjugate C n = A := by
    dsimp only [C,n,w,A]
    rw [right_rep]
    rw [show (Q.simple j*Q.simple i*Q.simple j)*(Q.simple i*Q.simple j*Q.simple i) =
      (Q.simple j*Q.simple i*Q.simple j*Q.simple i)*(Q.simple j*Q.simple i) by simp only [mul_assoc]]
    rw [←right_rep,fourth_root Q split hm i j hij,right_rep]
    simp only [mul_assoc,scancel,ssq,mul_one]
  have hfix : K ⊓ centralizer (T : Set (X ⧸ Q.D)) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hxC := hfixC hx
    have hnK : n ∈ normalizer (K : Set (X ⧸ Q.D)) := by
      rw [mem_normalizer_iff]
      intro y
      change y ∈ K ↔ y ∈ rightConjugate K n
      rw [hKn]
    have hyK : n⁻¹*x*n ∈ K := by
      simpa only [inv_inv] using (mem_normalizer_iff.mp (inv_mem hnK) x).mp hx.1
    have hyA : n⁻¹*x*n ∈ A := by
      rw [←hCn]
      change n*(n⁻¹*x*n)*n⁻¹ ∈ C
      simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using hxC
    have hyC := hfixC ⟨hyK,hAC hyA⟩
    have hy1 := disjoint_def.mp (near_far_disjoint Q split hm i j hij) hyA hyC
    apply mem_bot.mpr
    have hh := congrArg (fun z => n*z*n⁻¹) hy1
    simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one,mul_one,one_mul] using hh
  have hJB : J ≤ normalizer (B : Set (X ⧸ Q.D)) :=
    (J.le_centralizer.trans (centralizer_le hBJ)).trans (Subgroup.centralizer_le_normalizer _)
  have hTB : T ≤ normalizer (B : Set (X ⧸ Q.D)) :=
    zpowers_le.mpr (rootAt_torus_normalizes Q split j (Q.simple i*Q.simple j) c.property)
  have hKT : ⁅K,T⁆ ≤ B := by
    apply (commutator_mono hKABC le_rfl).trans
    apply commutator_sup_le_of_relative_normal J _ _ T B hJB (sup_le hAJ hBJ) hCJ
    · apply commutator_sup_le_of_relative_normal J _ _ T B hJB hAJ hBJ
      · rw [commutator_eq_bot_iff_le_centralizer.mpr hAC]; exact bot_le
      · exact le_normalizer_iff_commutator_le_left.mp hTB
    · rw [commutator_eq_bot_iff_le_centralizer.mpr hCC]; exact bot_le
  have hKp : IsPGroup 2 K := split.sylow.isPGroup'.of_injective
    (inclusion (hKJ.trans (hJW.trans inf_le_left))) (inclusion_injective _)
  have hcop : Nat.Coprime (Nat.card T) (Nat.card K) := by
    obtain ⟨a,ha⟩ := hKp.exists_card_eq
    rw [show Nat.card T = 3 by rw [Nat.card_zpowers,orderOf_coe,hc3],ha]
    exact Nat.Coprime.pow_right a (by decide)
  have hKB : K ≤ B := by
    rw [eq_commutator_sup_centralizer_of_solvable_coprime K T hTK
      (@IsNilpotent.to_isSolvable K _ hKp.isNilpotent) hcop,hfix,sup_bot_eq]
    exact hKT
  have hKeq : K = B := QuadrangleStructure.rootAt_eq_of_torus_invariant Q split j μj hKj
    (Q.simple i*Q.simple j) K hKB hne hHK
  have hBC : B ≤ centralizer (W : Set (X ⧸ Q.D)) := hKeq ▸ hKC
  have hBW : rootAt Q split j (Q.simple i) ≤ W := by
    have hh := comap_mono (f := (MulAut.conj (representative (Q.simple j) : X ⧸ Q.D)).toMonoidHom)
      (hBJ.trans hJW)
    change rightConjugate B (representative (Q.simple j) : X ⧸ Q.D) ≤
      rightConjugate W (representative (Q.simple j) : X ⧸ Q.D) at hh
    have he : rightConjugate W (representative (Q.simple j) : X ⧸ Q.D) = W := by
      dsimp only [W,simpleRemainder]
      rw [rightConjugate_inf,←unipotentConjugate_eq split _ _ (representative_spec _),
        unipotentConjugate_right split _ _ _ (representative_spec _),ssq,unipotentConjugate_one,inf_comm]
    simpa only [B,right_rep,mul_assoc,ssq,mul_one,he] using hh
  have hz : ⁅rootAt Q split j (Q.simple i),B⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hBW.trans (le_centralizer_iff.mp hBC))
  have hh := congrArg (fun E => rightConjugate E
    (representative (Q.simple i) : X ⧸ Q.D)) hz
  rw [right_comm,right_rep,right_rep,right_bot] at hh
  simp only [ssq,rootAt_one] at hh
  exact hne hh
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
