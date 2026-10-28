module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicMiddleClosure
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The binary octagon centralizer dichotomy

The radical is the product of its two end roots and the five middle roots.
A parabolic-invariant subgroup containing the middle roots cannot have
index four: each end root would supplement it, so adjacent commutation
makes the first simple root trivial on that quotient. Intersecting with
the opposite radical puts all its commutators in the middle five roots.
Reflection and rank-one generation then force the reflection itself to
act trivially modulo those roots, contrary to its exchange of the two
independent end roots.

This proves the index-four exclusion in the first paragraph of Fong--Seitz I
(1973), (6G), printed p.50, directly with the actual root maps. Together
with the previously proved cubic congruence, it leaves exactly the whole
radical and the five-root subgroup as middle-root centralizers. The
original-factor and Chapter 12 applications are in LinearPairCubicDichotomySource
and SourceSelection/LinearPairCubicDichotomyChapter12. The remaining index-sixteen
exclusion and subsequent normalizer argument are separate obligations.
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups commutatorElement
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
private theorem seven_list (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j) :
    ∃ b, orderedRoots Q split b 7 =
      [simpleRoot Q split j, rootAt Q split i (Q.simple j),
       rootAt Q split j (Q.simple i*Q.simple j),
       rootAt Q split i (Q.simple j*Q.simple i*Q.simple j),
       rootAt Q split j (Q.simple i*Q.simple j*Q.simple i),
       rootAt Q split i (Q.simple j*Q.simple i), rootAt Q split j (Q.simple i)] ∧
      rootIntersection split (longest Q) (alternatingWord Q b 7)⁻¹ =
        simpleRemainder Q split i := by
  have h0 := perpendicular_root_stable Q split hm i j hij
    (representative (Q.simple i)) (representative_spec _)
  have h1 := perpendicular_root_stable Q split hm j i hij.symm
    (representative (Q.simple j)) (representative_spec _)
  rw [right_rep] at h0 h1
  have h5 := congrArg (fun A => rightConjugate A (representative (Q.simple j) : X ⧸ Q.D)) h0
  have h6 := congrArg (fun A => rightConjugate A
    (representative (Q.simple i*Q.simple j) : X ⧸ Q.D)) h1
  simp only [right_rep, mul_assoc, ssq, mul_one] at h5 h6
  simp only [←mul_assoc] at h5 h6
  have hint (b : Bool) : rootIntersection split (longest Q) (alternatingWord Q b 7)⁻¹ =
      simpleRemainder Q split (if b then 0 else 1) := by
    have he : longest Q = Q.simple (if b then 0 else 1)*alternatingWord Q b 7 := by
      have hh := (alternatingWord_longest Q (!b)).symm
      rw [hm] at hh
      cases b <;> exact hh
    change split.U ⊓ unipotentConjugate split
      (longest Q*(alternatingWord Q b 7)⁻¹) = _
    rw [he,mul_inv_cancel_right]
    rfl
  have hlist (b : Bool) (hi : i = if b then 0 else 1) (hj : j = if b then 1 else 0) :
      orderedRoots Q split b 7 =
      [simpleRoot Q split j, rootAt Q split i (Q.simple j),
       rootAt Q split j (Q.simple i*Q.simple j),
       rootAt Q split i (Q.simple j*Q.simple i*Q.simple j),
       rootAt Q split j (Q.simple i*Q.simple j*Q.simple i),
       rootAt Q split i (Q.simple j*Q.simple i), rootAt Q split j (Q.simple i)] := by
    cases b <;> subst i <;> subst j <;>
      simp only [Bool.false_eq_true, ↓reduceIte] at h0 h1 h5 h6 <;>
      simp only [orderedRoots, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
        Bool.not_true, List.map_cons, List.map_nil, right_simple, right_rep] <;>
      rw [h1,h5,h6] <;> simp only [mul_assoc,ssq,mul_one]
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · have hj : j = 1 := by omega
    subst j
    exact ⟨true,hlist true rfl rfl,hint true⟩
  · have hj : j = 0 := by omega
    subst j
    exact ⟨false,hlist false rfl rfl,hint false⟩



private theorem other_root_le (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) :
    simpleRoot Q split i ≤ simpleRemainder Q split j := by
  have hl : Q.tits.wordLength (Q.simple j*Q.simple i) = 2 := by
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;>
      rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · exact (hij rfl).elim
    · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.not_false, mul_one] using wordLength_alternatingWord Q true (n := 2) (by omega)
    · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.not_false, mul_one] using wordLength_alternatingWord Q false (n := 2) (by omega)
    · exact (hij rfl).elim
  have hj : Q.tits.wordLength (Q.simple j) = 1 := by
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte, mul_one] using
        wordLength_alternatingWord Q false (n := 1) (by omega)
    · simpa only [alternatingWord, ↓reduceIte, mul_one] using
        wordLength_alternatingWord Q true (n := 1) (by omega)
  exact simpleRoot_le_ascent_intersection Q split (Q.simple j) i (by rw [hl,hj])

private theorem reflection_remainder (i : Fin 2) :
    rightConjugate (simpleRemainder Q split i)
      (representative (Q.simple i) : X ⧸ Q.D) = simpleRemainder Q split i := by
  rw [simpleRemainder,rightConjugate_inf,
    ←unipotentConjugate_eq split _ _ (representative_spec _),
    unipotentConjugate_right split _ _ _ (representative_spec _),ssq,
    unipotentConjugate_one,inf_comm]

/-- The two end roots and the middle five roots are the exact radical product. -/
theorem radical_end_product (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) :
    (simpleRemainder Q split i : Set (X ⧸ Q.D)) =
      (simpleRoot Q split j : Set (X ⧸ Q.D)) *
      ((middleFive Q split i j : Set (X ⧸ Q.D)) *
        (rootAt Q split j (Q.simple i) : Set (X ⧸ Q.D))) := by
  have hB := other_root_le Q split hm j i hij.symm
  have hD : rootAt Q split j (Q.simple i) ≤ simpleRemainder Q split i := by
    have hh := comap_mono (f := (MulAut.conj
      (representative (Q.simple i) : X ⧸ Q.D)).toMonoidHom) hB
    change rootAt Q split j (Q.simple i) ≤ rightConjugate (simpleRemainder Q split i) _ at hh
    rwa [reflection_remainder] at hh
  have hJ := middleFive_le_remainder Q split hm i j hij
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨b,hb,hV⟩ := seven_list Q split hm i j hij
    have hp := (orderedRoots_product Q split b 7 (by omega)).symm
    rw [hV,hb] at hp
    change (simpleRemainder Q split i : Set (X ⧸ Q.D)) =
      (simpleRoot Q split j : Set (X ⧸ Q.D)) *
        ((rootAt Q split i (Q.simple j) : Set (X ⧸ Q.D)) *
        ((rootAt Q split j (Q.simple i*Q.simple j) : Set (X ⧸ Q.D)) *
        ((rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) : Set (X ⧸ Q.D)) *
        ((rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) *
        ((rootAt Q split i (Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) *
        ((rootAt Q split j (Q.simple i) : Set (X ⧸ Q.D)) * 1)))))) at hp
    rw [mul_one] at hp
    rw [hp] at hx
    obtain ⟨u,hu,_,⟨a,ha,_,⟨e,he,_,⟨v,hv,_,⟨d,hd,_,⟨c,hc,f,hf,rfl⟩,rfl⟩,rfl⟩,rfl⟩,rfl⟩,rfl⟩ := hx
    refine ⟨u,hu,_,⟨a*(e*(v*(d*c))),?_,f,hf,by simp only [mul_assoc]⟩,rfl⟩
    exact mul_mem (mem_sup_left (mem_sup_left (mem_sup_left (mem_sup_left ha))))
      (mul_mem (mem_sup_left (mem_sup_left (mem_sup_left (mem_sup_right he))))
        (mul_mem (mem_sup_left (mem_sup_left (mem_sup_right hv)))
          (mul_mem (mem_sup_left (mem_sup_right hd)) (mem_sup_right hc))))
  · rintro _ ⟨b,hb,_,⟨m,hm,d,hd,rfl⟩,rfl⟩
    exact mul_mem (hB hb) (mul_mem (hJ hm) (hD hd))

private theorem end_data (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) :
    rootAt Q split j (Q.simple i) ≤ simpleRemainder Q split i ⊓ simpleRemainder Q split j ∧
    Disjoint (middleFive Q split i j) (rootAt Q split j (Q.simple i)) ∧
    simpleRemainder Q split i ⊓ simpleRemainder Q split j =
      middleFive Q split i j ⊔ rootAt Q split j (Q.simple i) := by
  let V := simpleRemainder Q split i
  let W := simpleRemainder Q split j
  let J := middleFive Q split i j
  let D := rootAt Q split j (Q.simple i)
  have hJV : J ≤ V := middleFive_le_remainder Q split hm i j hij
  have hJW : J ≤ W := by
    dsimp only [J,W]
    rw [middleFive_eq_radical_intersection Q split hm i j hij]
    exact inf_le_left.trans inf_le_right
  have hDV : D ≤ V := by
    have hh := comap_mono (f := (MulAut.conj
      (representative (Q.simple i) : X ⧸ Q.D)).toMonoidHom)
      (other_root_le Q split hm j i hij.symm)
    change D ≤ rightConjugate V _ at hh
    rwa [reflection_remainder] at hh
  have hDW : D ≤ W := by
    have hd : D ≤ unipotentConjugate split (Q.simple j) := by
      apply rootAt_le_conjugate
      simp only [inv_eq_of_mul_eq_one_right (ssq Q i)]
      have hh (b : Bool) := And.intro
        (wordLength_alternatingWord Q b (n := 2) (by omega))
        (wordLength_alternatingWord Q b (n := 3) (by omega))
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;>
        rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · exact (hij rfl).elim
      · have hl := hh true
        simp only [alternatingWord, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
          Bool.not_true,mul_one] at hl
        simpa only [mul_assoc] using hl.2.trans (congrArg (·+1) hl.1).symm
      · have hl := hh false
        simp only [alternatingWord, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
          Bool.not_true,mul_one] at hl
        simpa only [mul_assoc] using hl.2.trans (congrArg (·+1) hl.1).symm
      · exact (hij rfl).elim
    exact le_inf (hDV.trans inf_le_left) hd
  have hdis : Disjoint J D := by
    apply Disjoint.mono_left (show J ≤ rightConjugate W
      (representative (Q.simple i) : X ⧸ Q.D) from by
        dsimp only [J,W]
        rw [middleFive_eq_radical_intersection Q split hm i j hij]; exact inf_le_right)
    apply disjoint_def.mpr
    intro x hx hy
    apply (MulAut.conj (representative (Q.simple i) : X ⧸ Q.D)).injective
    exact (disjoint_def.mp (simpleRoot_disjoint_remainder Q split j) hy hx).trans
      (map_one _).symm
  refine ⟨le_inf hDV hDW,hdis,le_antisymm ?_ (sup_le (le_inf hJV hJW) (le_inf hDV hDW))⟩
  intro x hx
  have hp : x ∈ (V : Set (X ⧸ Q.D)) := hx.1
  rw [radical_end_product Q split hm i j hij] at hp
  obtain ⟨b,hb,_,⟨m,hm,d,hd,rfl⟩,rfl⟩ := hp
  have hbW : b ∈ W := by
    simpa only [mul_inv_cancel_right] using
      W.mul_mem hx.2 (W.inv_mem (W.mul_mem (hJW hm) (hDW hd)))
  have hb1 := disjoint_def.mp (simpleRoot_disjoint_remainder Q split j) hb hbW
  simpa only [hb1,one_mul] using (mul_mem_sup hm hd : m*d ∈ J ⊔ D)

/-- A parabolic-invariant overgroup of the five middle roots cannot have
index four in the degree-one radical. -/
theorem binary_middle_overgroup_index_ne_four {F : Type*}
    [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μj : localGroup Q split j ≃* PSL(2,F))
    (s : HexagonStructure.RootReflection Q split i)
    (hi : Nat.card (simpleRoot Q split i) = 2)
    (hj : Nat.card (simpleRoot Q split j) = 4)
    (C : Subgroup (X ⧸ Q.D))
    (hJC : middleFive Q split i j ≤ C) (hCV : C ≤ simpleRemainder Q split i)
    (hPC : Q.tits.standardParabolic {Q.simple i} ≤ normalizer (C : Set (X ⧸ Q.D))) :
    C.relIndex (simpleRemainder Q split i) ≠ 4 := by
  intro hindex
  let V := simpleRemainder Q split i
  let W := V ⊓ simpleRemainder Q split j
  let J := middleFive Q split i j
  let A := simpleRoot Q split i
  let B := simpleRoot Q split j
  let D := rootAt Q split j (Q.simple i)
  let n : X ⧸ Q.D := representative (Q.simple i)
  have hnP : n ∈ Q.tits.standardParabolic {Q.simple i} :=
    Q.tits.bruhatCell_subset_standardParabolic_of_mem (Set.mem_singleton _)
      (Q.tits.representative_mem_bruhatCell _ (representative (Q.simple i)) (representative_spec _))
  have hCn : rightConjugate C n = C := rightConjugate_eq_self _ (hPC hnP)
  obtain ⟨hDW,hJD,hW⟩ := end_data Q split hm i j hij
  change D ≤ W at hDW
  change Disjoint J D at hJD
  change W = J ⊔ D at hW
  have hJV : J ≤ V := middleFive_le_remainder Q split hm i j hij
  have hJW : J ≤ W := hW ▸ le_sup_left
  have hBV : B ≤ V := other_root_le Q split hm j i hij.symm
  have hVP : V ≤ Q.tits.standardParabolic {Q.simple i} :=
    inf_le_left.trans (split.U_le.trans (Q.tits.B_le_standardParabolic _))
  have hVC := hVP.trans hPC
  have hVN := middleFive_normalized_by_remainder Q split hm i j hij hKj
  have hJcard : Nat.card J = 128 := by
    dsimp only [J]
    rw [middleFive_card Q split hm i j hij,hi,hj]; norm_num
  have hVcard : Nat.card V = 2048 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup (X ⧸ Q.D)) J V bot_le hJV
    rw [relIndex_bot_left,relIndex_bot_left,hJcard] at hh
    have hq := binary_middleFive_quotient_card Q split hm i j hij hi hj
    change J.relIndex V = 16 at hq
    rw [hq] at hh
    exact hh.symm
  have hCcard : Nat.card C = 512 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup (X ⧸ Q.D)) C V bot_le hCV
    rw [relIndex_bot_left,relIndex_bot_left,hVcard,hindex] at hh
    omega
  have hDcard : Nat.card D = 4 := by
    simpa only [D,rootAt,card_rightConjugate] using hj
  have hWcard : Nat.card W = 512 := by
    rw [hW,card_sup_eq_mul_of_normalizes_of_disjoint J D (hDW.trans (inf_le_left.trans hVN)) hJD,
      hJcard,hDcard]
  have hBnot : ¬ B ≤ C := by
    intro hBC
    have hDC : D ≤ C := by
      have hh := comap_mono (f := (MulAut.conj n).toMonoidHom) hBC
      change D ≤ rightConjugate C n at hh
      rwa [hCn] at hh
    have hVC' : V ≤ C := by
      intro x hx
      have hp : x ∈ (V : Set (X ⧸ Q.D)) := hx
      rw [radical_end_product Q split hm i j hij] at hp
      obtain ⟨b,hb,_,⟨m,hm,d,hd,rfl⟩,rfl⟩ := hp
      exact mul_mem (hBC hb) (mul_mem (hJC hm) (hDC hd))
    have he := le_antisymm hCV hVC'
    rw [he,relIndex_self] at hindex
    omega
  have hCB : Disjoint C B := by
    apply disjoint_iff.mpr
    by_contra hne
    have he := QuadrangleStructure.simpleRoot_eq_of_torus_invariant Q split j μj hKj
      (C ⊓ B) inf_le_right hne
      ((le_inf (inf_le_left.trans ((Q.tits.B_le_standardParabolic _).trans hPC))
        (torus_normalizes_simpleRoot Q split j)).trans inf_normalizer_le_normalizer_inf)
    change C ⊓ B = B at he
    exact hBnot (he ▸ inf_le_left)
  have hCD : Disjoint C D := by
    apply disjoint_def.mpr
    intro x hx hy
    have hx' : n*x*n⁻¹ ∈ C := (mem_normalizer_iff.mp (hPC hnP) x).mp hx
    apply (MulAut.conj n).injective
    exact (disjoint_def.mp hCB hx' hy).trans (map_one _).symm
  have hCDV : C ⊔ D = V := by
    apply eq_of_le_of_card_ge (sup_le hCV (hDW.trans inf_le_left))
    rw [card_sup_eq_mul_of_normalizes_of_disjoint C D
      ((hDW.trans inf_le_left).trans hVC) hCD,hCcard,hDcard,hVcard]
  have hCWV : C ⊔ W = V := le_antisymm (sup_le hCV inf_le_left)
    (hCDV ▸ sup_le le_sup_left (hDW.trans le_sup_right))
  have hWN : V ≤ normalizer (W : Set (X ⧸ Q.D)) :=
    (le_inf V.le_normalizer
      (inf_le_left.trans (split.U_le.trans ((Q.tits.B_le_standardParabolic _).trans
        (remainder_parabolic_normalizes Q split j hKj))))).trans
        inf_normalizer_le_normalizer_inf
  have hCW : C ⊓ W = J := by
    apply (eq_of_le_of_card_ge (le_inf hJC hJW) ?_).symm
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes W C (hCV.trans hWN)
    rw [inf_comm W C,sup_comm W C,hCWV,hWcard,hCcard,hVcard] at hh
    rw [hJcard]
    omega
  have hAP : A ≤ Q.tits.standardParabolic {Q.simple i} :=
    (simpleRoot_le Q split i).trans (split.U_le.trans (Q.tits.B_le_standardParabolic _))
  have hAV : ⁅A,V⁆ ≤ C := by
    rw [←hCDV,commutator_comm]
    apply commutator_sup_le_of_relative_normal V C D A C hVC hCV (hDW.trans inf_le_left)
    · rw [commutator_comm]
      exact le_normalizer_iff_commutator_le_right.mp (hAP.trans hPC)
    · rw [commutator_comm,ReeSource.adjacent_commutator_eq_bot Q split hm i j hij hKi hKj]
      exact bot_le
  have hAW : ⁅A,V⁆ ≤ W := by
    apply le_inf
    · exact le_normalizer_iff_commutator_le_right.mp
        (hAP.trans (remainder_parabolic_normalizes Q split i hKi))
    · exact (commutator_mono (other_root_le Q split hm i j hij) le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp
          (inf_le_left.trans (split.U_le.trans ((Q.tits.B_le_standardParabolic _).trans
        (remainder_parabolic_normalizes Q split j hKj)))))
  have hAJ : ⁅A,V⁆ ≤ J := hCW ▸ le_inf hAV hAW
  have hJn : rightConjugate J n = J := middleFive_reflection Q split hm i j hij
  have hopp : ⁅rootAt Q split i (Q.simple i),V⁆ ≤ J := by
    have hh := comap_mono (f := (MulAut.conj n).toMonoidHom) hAJ
    change rightConjugate ⁅A,V⁆ n ≤ rightConjugate J n at hh
    rw [right_comm,hJn,reflection_remainder] at hh
    exact hh
  have hAN : A ≤ normalizer (J : Set (X ⧸ Q.D)) :=
    le_normalizer_iff_commutator_le_right.mpr ((commutator_mono le_rfl hJV).trans hAJ)
  have hON : rootAt Q split i (Q.simple i) ≤ normalizer (J : Set (X ⧸ Q.D)) :=
    le_normalizer_iff_commutator_le_right.mpr ((commutator_mono le_rfl hJV).trans hopp)
  have hRJ : ⁅rankOne Q split i,V⁆ ≤ J :=
    commutator_sup_le_of_relative_normal (normalizer (J : Set (X ⧸ Q.D))) _ _ V J
      le_rfl hAN hON hAJ hopp
  have hBzero : B = ⊥ := by
    apply eq_bot_iff.mpr
    intro b hb
    have hc := hRJ (commutator_mem_commutator (inv_mem s.mem_rankOne) (hBV hb))
    have hd : (s.val : X ⧸ Q.D)⁻¹*b*(s.val : X ⧸ Q.D) ∈ D := by
      rw [show D = rightConjugate B (s.val : X ⧸ Q.D) from rootAt_eq Q split j _ s.val s.class_eq]
      change (s.val : X ⧸ Q.D)*((s.val : X ⧸ Q.D)⁻¹*b*(s.val : X ⧸ Q.D))*
        (s.val : X ⧸ Q.D)⁻¹ ∈ B
      simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using hb
    have hbW : b⁻¹ ∈ simpleRemainder Q split j := by
      have hh := (simpleRemainder Q split j).mul_mem
        ((simpleRemainder Q split j).inv_mem (hDW hd).2) (hJW hc).2
      simpa only [commutatorElement_def,coe_inv,inv_inv,mul_inv_rev,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_left] using hh
    exact mem_bot.mpr (disjoint_def.mp (simpleRoot_disjoint_remainder Q split j)
      hb (by simpa only [inv_inv] using inv_mem hbW))
  have hc : Nat.card B = 1 := hBzero ▸ card_bot
  change Nat.card B = 4 at hj
  omega

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
