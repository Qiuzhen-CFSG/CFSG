module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.NonbinaryMixedCommutator
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.NonbinaryLongCommutator
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.SixRootIntervals

/-!
# The higher-degree two-linear octagon contradiction

The middle fixed pair is central in the larger radical but cannot be
invariant under its rank-one group. Hence the next mixed commutator
escapes the second fixed root. The six-root interval and derived bound
leave three coordinates. Centrality and Cartan irreducibility kill the
last coordinate; the separating cubic actor then forces the entire
remaining moving root into that commutator. Reflection puts all five
middle roots into the derived radical, contradicting the (4B) bound.

Source: Fong--Seitz I (1973), (6G), bottom of printed p.50 and top of p.51.
LinearPairExclusion constructs every input from the original linear
factors, retaining the full Borel and both endpoint maps.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups Pointwise commutatorElement
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
private theorem right_comm (A B : Subgroup (X ⧸ Q.D)) (w : Weyl Q) :
    rightConjugate ⁅A,B⁆ (representative w : X ⧸ Q.D) =
      ⁅rightConjugate A (representative w : X ⧸ Q.D),
        rightConjugate B (representative w : X ⧸ Q.D)⁆ := by
  simp only [rightConjugate,comap_equiv_eq_map_symm',map_commutator]
private theorem right_bot (w : Weyl Q) :
    rightConjugate (⊥ : Subgroup (X ⧸ Q.D)) (representative w : X ⧸ Q.D) = ⊥ := by
  simp only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_bot]
private theorem reflection_remainder (k : Fin 2) :
    rightConjugate (simpleRemainder Q split k)
      (representative (Q.simple k) : X ⧸ Q.D) = simpleRemainder Q split k := by
  rw [simpleRemainder,rightConjugate_inf,
    ←unipotentConjugate_eq split _ _ (representative_spec _),
    unipotentConjugate_right split _ _ _ (representative_spec _),ssq,
    unipotentConjugate_one,inf_comm]

/-- The non-invariant middle pair forces the next mixed commutator to
escape its second root. -/
theorem middle_pair_commutator_not_le (i j : Fin 2)
    (hzero : ⁅simpleRoot Q split j,
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ = ⊥)
    (hN : ¬ rankOne Q split j ≤ normalizer
      ((rootAt Q split i (Q.simple j*Q.simple i) ⊔
        rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) : Subgroup (X ⧸ Q.D)) : Set _)) :
    ¬ ⁅simpleRoot Q split j,rootAt Q split i (Q.simple j*Q.simple i)⁆ ≤
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) := by
  intro hle
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let E := rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)
  let J := C ⊔ E
  have hU : simpleRoot Q split j ≤ normalizer (J : Set (X ⧸ Q.D)) := by
    apply le_normalizer_iff.mpr
    intro u hu x hx
    have hmap : J.map (MulAut.conj u).toMonoidHom ≤ J := by
      rw [Subgroup.map_sup]
      apply sup_le
      · rintro _ ⟨v,hv,rfl⟩
        have hh : ⁅u,v⁆*v ∈ J := mul_mem
          (mem_sup_right (hle (commutator_mem_commutator hu hv))) (mem_sup_left hv)
        change u*v*u⁻¹ ∈ J
        simpa only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one] using hh
      · rintro _ ⟨v,hv,rfl⟩
        change u*v*u⁻¹ ∈ J
        rw [←commutator_eq_bot_iff_le_centralizer.mp hzero hu v hv,mul_inv_cancel_right]
        exact mem_sup_right hv
    exact hmap (mem_map_of_mem (MulAut.conj u).toMonoidHom hx)
  have hswap : rightConjugate J (representative (Q.simple j) : X ⧸ Q.D) = J := by
    simp only [J,rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_sup]
    simp only [←comap_equiv_eq_map_symm']
    change rightConjugate C _ ⊔ rightConjugate E _ = J
    dsimp only [C,E]
    rw [right_rep,right_rep]
    simp only [mul_assoc,ssq,mul_one,J,C,E,sup_comm]
  apply hN
  apply sup_le hU
  have hh := (comap_mono (f := (MulAut.conj
    (representative (Q.simple j) : X ⧸ Q.D)).toMonoidHom) hU).trans
      (le_normalizer_comap _)
  change rootAt Q split j (Q.simple j) ≤ normalizer
    (rightConjugate J (representative (Q.simple j) : X ⧸ Q.D) : Set _) at hh
  rwa [hswap] at hh

private theorem longest_eight (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) :
    longest Q = Q.simple i*Q.simple j*Q.simple i*Q.simple j*
      Q.simple i*Q.simple j*Q.simple i*Q.simple j := by
  have h0 := alternatingWord_longest Q false
  have h1 := alternatingWord_longest Q true
  rw [hm] at h0 h1
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false, Bool.not_true, mul_one, mul_assoc] using h0.symm
  · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false, Bool.not_true, mul_one, mul_assoc] using h1.symm
  · exact (hij rfl).elim

private theorem mixed_reflected (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hz : ⁅simpleRoot Q split j,
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ = ⊥) :
    ⁅simpleRoot Q split i,rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)⁆ = ⊥ := by
  have hh := congrArg (fun A => rightConjugate A
    (representative (Q.simple i*Q.simple j*Q.simple i*Q.simple j) : X ⧸ Q.D)) hz
  rw [right_comm] at hh
  change ⁅rootAt Q split j (Q.simple i*Q.simple j*Q.simple i*Q.simple j),
    rightConjugate (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)) _⁆ = _ at hh
  rw [right_rep,right_bot] at hh
  have hfix := perpendicular_root_stable Q split hm j i hij.symm
    (representative (Q.simple j)) (representative_spec _)
  rw [right_rep] at hfix
  have he : (Q.simple j*Q.simple i*Q.simple j)*
      (Q.simple i*Q.simple j*Q.simple i*Q.simple j) = (longest Q*Q.simple i)*1 := by
    rw [longest_eight Q hm j i hij.symm]
    simp only [mul_assoc,ssq,mul_one]
  rw [hfix,he,rootAt_longest_simple_mul Q split hm i j hij,rootAt_one,commutator_comm] at hh
  exact hh

/-- The final higher-degree (6G) contradiction. A commutator escaping the
central fixed pair has a nonzero coordinate in the other root family;
Cartan irreducibility and reflection then fill the forbidden derived radical. -/
theorem nonbinary_linear_terminal_false
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μj : localGroup Q split j ≃* PSL(2,F))
    (c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)))
    (hc : ∀ w : Weyl Q,
      (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) ∧
      rootAt Q split j w ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥)
    (hlong : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ =
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) ⊔
        rootAt Q split i (Q.simple j*Q.simple i))
    (hzero : ⁅simpleRoot Q split j,rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ = ⊥)
    (hcentral : rootAt Q split i (Q.simple j*Q.simple i) ⊔
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) ≤
      centralizer (simpleRemainder Q split j : Set (X ⧸ Q.D)))
    (hnot : ¬ ⁅simpleRoot Q split j,rootAt Q split i (Q.simple j*Q.simple i)⁆ ≤
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j))
    (hlt : ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ < middleFive Q split j i) : False := by
  let V := simpleRemainder Q split j
  let D := ⁅V,V⁆
  let M := middleFive Q split j i
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let E := rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)
  let B := rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)
  let W := rootAt Q split j (Q.simple i*Q.simple j)
  let K := ⁅simpleRoot Q split j,C⁆
  change ¬ K ≤ E at hnot
  have hCV : C ≤ V := (show C ≤ M from le_sup_right.trans
    (le_sup_left.trans (le_sup_left.trans le_sup_left))).trans
      (middleFive_le_remainder Q split hm j i hij.symm)
  have hEV : E ≤ V := (show E ≤ M from le_sup_right.trans le_sup_left).trans
    (middleFive_le_remainder Q split hm j i hij.symm)
  have hBV : B ≤ V := (show B ≤ M from le_sup_right.trans (le_sup_left.trans le_sup_left)).trans
    (middleFive_le_remainder Q split hm j i hij.symm)
  have hWV : W ≤ V := (show W ≤ M from le_sup_right).trans
    (middleFive_le_remainder Q split hm j i hij.symm)
  have hAV : simpleRoot Q split i ≤ V := by
    intro x hx
    change x ∈ (V : Set (X ⧸ Q.D))
    rw [show V = simpleRemainder Q split j from rfl,radical_end_product Q split hm j i hij.symm]
    exact ⟨x,hx,1,⟨1,one_mem _,1,one_mem _,one_mul _⟩,mul_one _⟩
  have hAD : E ⊔ C ≤ D := by
    rw [←hlong]
    exact commutator_mono hAV (octagon_three_roots_le_remainder Q split hm j i hij.symm).1
  have hCD : C ≤ D := le_sup_right.trans hAD
  have hED : E ≤ D := le_sup_left.trans hAD
  have hUN : simpleRoot Q split j ≤ normalizer (V : Set (X ⧸ Q.D)) :=
    (simpleRoot_le Q split j).trans (split.U_le.trans
      ((Q.tits.B_le_standardParabolic _).trans (remainder_parabolic_normalizes Q split j hKj)))
  have hUND : simpleRoot Q split j ≤ normalizer (D : Set (X ⧸ Q.D)) := by
    intro u hu
    rw [mem_normalizer_iff_map_conj_eq]
    change (⁅V,V⁆).map _ = _
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (hUN hu)]
  have hKD : K ≤ D := (commutator_mono le_rfl hCD).trans
    (le_normalizer_iff_commutator_le_right.mp hUND)
  have hKC : K ≤ centralizer (V : Set (X ⧸ Q.D)) :=
    (commutator_mono le_rfl (le_sup_left.trans hcentral)).trans
      (le_normalizer_iff_commutator_le_right.mp
        (hUN.trans (normalizer_le_normalizer_centralizer _)))
  have hHK : Q.tits.B ⊓ Q.tits.N ≤ normalizer (K : Set (X ⧸ Q.D)) := by
    intro t ht
    rw [mem_normalizer_iff_map_conj_eq]
    change (⁅simpleRoot Q split j,C⁆).map _ = _
    rw [map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (torus_normalizes_simpleRoot Q split j ht),
      mem_normalizer_iff_map_conj_eq.mp (rootAt_torus_normalizes Q split i (Q.simple j*Q.simple i) ht)]
  have hdis : Disjoint (rootAt Q split i (Q.simple j)) M := by
    apply disjoint_def.mpr
    intro x hx hy
    change x ∈ middleFive Q split j i at hy
    have hy' := (middleFive_eq_radical_intersection Q split hm j i hij.symm ▸ hy).2
    apply (MulAut.conj (representative (Q.simple j) : X ⧸ Q.D)).injective
    exact (disjoint_def.mp (simpleRoot_disjoint_remainder Q split i) hx hy').trans (map_one _).symm
  have support (x : X ⧸ Q.D) (hx : x ∈ K) :
      ∃ b ∈ B, ∃ e ∈ E, ∃ w ∈ W, b*e*w = x := by
    obtain ⟨awe,⟨aw,⟨a,ha,w,hw,rfl⟩,e,he,rfl⟩,b,hb,hh⟩ :=
      distance_five_commutator_support Q split hm j i hij.symm hKj hKi x⁻¹ (K.inv_mem hx)
    change a*w*e*b = x⁻¹ at hh
    have haM : a ∈ M := by
      have hhM : a*w*e*b ∈ M := by
        rw [hh]
        exact hlt.le (hKD (K.inv_mem hx))
      have hmprod : w*e*b ∈ M := M.mul_mem
        (M.mul_mem (mem_sup_right hw) (mem_sup_left (mem_sup_right he)))
        (mem_sup_left (mem_sup_left (mem_sup_right hb)))
      simpa only [mul_assoc,mul_inv_rev,mul_inv_cancel_left,mul_inv_cancel,mul_one]
        using M.mul_mem hhM (M.inv_mem hmprod)
    have ha1 := disjoint_def.mp hdis ha haM
    refine ⟨b⁻¹,B.inv_mem hb,e⁻¹,E.inv_mem he,w⁻¹,W.inv_mem hw,?_⟩
    have hh' := congrArg Inv.inv hh
    simpa only [ha1,one_mul,mul_inv_rev,inv_inv,mul_assoc] using hh'
  have hconjK : rightConjugate K (representative (Q.simple i*Q.simple j) : X ⧸ Q.D) =
      ⁅W,simpleRoot Q split i⁆ := by
    rw [right_comm]
    change ⁅W,rightConjugate C _⁆ = _
    dsimp only [C]
    rw [right_rep]
    simp only [mul_assoc,←mul_assoc (Q.simple i) (Q.simple i),ssq,one_mul,rootAt_one]
  have hWzero : W ⊓ centralizer (simpleRoot Q split i : Set (X ⧸ Q.D)) = ⊥ := by
    by_contra hn
    have he := QuadrangleStructure.rootAt_eq_of_torus_invariant Q split j μj hKj
      (Q.simple i*Q.simple j) _ inf_le_left hn
      ((le_inf (rootAt_torus_normalizes Q split j (Q.simple i*Q.simple j))
        ((torus_normalizes_simpleRoot Q split i).trans (normalizer_le_normalizer_centralizer _))).trans
          inf_normalizer_le_normalizer_inf)
    change W ⊓ centralizer (simpleRoot Q split i : Set (X ⧸ Q.D)) = W at he
    have hz : ⁅W,simpleRoot Q split i⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr (he ▸ inf_le_right)
    rw [←hconjK,rightConjugate,comap_equiv_eq_map_symm'] at hz
    have hKbot : K = ⊥ := (map_eq_bot_iff_of_injective K (MulAut.conj _).symm.injective).mp hz
    exact hnot (hKbot ▸ bot_le)
  have hAB : simpleRoot Q split i ≤ centralizer (B : Set (X ⧸ Q.D)) :=
    commutator_eq_bot_iff_le_centralizer.mp (mixed_reflected Q split hm i j hij hzero)
  have support_two (x : X ⧸ Q.D) (hx : x ∈ K) : x ∈ (B : Set (X ⧸ Q.D))*(E : Set (X ⧸ Q.D)) := by
    obtain ⟨b,hb,e,he,w,hw,hxval⟩ := support x hx
    have hbA : b ∈ centralizer (simpleRoot Q split i : Set (X ⧸ Q.D)) := le_centralizer_iff.mp hAB hb
    have heA : e ∈ centralizer (simpleRoot Q split i : Set (X ⧸ Q.D)) :=
      fun u hu => (le_sup_right.trans hcentral) he u (hAV hu)
    have hxA : x ∈ centralizer (simpleRoot Q split i : Set (X ⧸ Q.D)) := fun u hu => hKC hx u (hAV hu)
    have hwA : w ∈ centralizer (simpleRoot Q split i : Set (X ⧸ Q.D)) := by
      rw [←hxval] at hxA
      simpa only [inv_mul_cancel_left] using
        (centralizer _).mul_mem ((centralizer _).inv_mem ((centralizer _).mul_mem hbA heA)) hxA
    have hw1 : w = 1 := hWzero.le ⟨hw,hwA⟩
    refine ⟨b,hb,e,he,?_⟩
    simpa only [hw1,mul_one] using hxval
  have hBKne : K ⊓ B ≠ ⊥ := by
    intro hz
    obtain ⟨x,hx,hxe⟩ := Set.not_subset.mp hnot
    obtain ⟨b,hb,e,he,hbe⟩ := support_two x hx
    change b*e = x at hbe
    have hbne : b ≠ 1 := by
      intro hb1
      apply hxe
      rw [←hbe,hb1,one_mul]
      exact he
    let t : X ⧸ Q.D := c
    let z := t*x*t⁻¹*x⁻¹
    have hzK : z ∈ K := K.mul_mem
      ((mem_normalizer_iff.mp (hHK c.property) x).mp hx) (K.inv_mem hx)
    have hte : t*e*t⁻¹ = e := by
      rw [←(hc (Q.simple j*Q.simple i*Q.simple j)).1 e he,mul_inv_cancel_right]
    have hzb : z = t*b*t⁻¹*b⁻¹ := by
      dsimp only [z]
      rw [←hbe]
      calc
        _ = (t*b*t⁻¹)*(t*e*t⁻¹)*(b*e)⁻¹ := by group
        _ = _ := by rw [hte]; group
    have hzB : z ∈ B := by
      rw [hzb]
      exact B.mul_mem ((mem_normalizer_iff.mp
        (rootAt_torus_normalizes Q split j (Q.simple i*Q.simple j*Q.simple i) c.property) b).mp hb)
        (B.inv_mem hb)
    have hz1 : z = 1 := hz.le ⟨hzK,hzB⟩
    rw [hzb,mul_inv_eq_one] at hz1
    have hbfix : b ∈ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) :=
      mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hz1).symm
    exact hbne ((hc (Q.simple i*Q.simple j*Q.simple i)).2.le ⟨hb,hbfix⟩)
  have heB := QuadrangleStructure.rootAt_eq_of_torus_invariant Q split j μj hKj
    (Q.simple i*Q.simple j*Q.simple i) (K ⊓ B) inf_le_right hBKne
    ((le_inf hHK (rootAt_torus_normalizes Q split j (Q.simple i*Q.simple j*Q.simple i))).trans
      inf_normalizer_le_normalizer_inf)
  change K ⊓ B = B at heB
  have hBK : B ≤ K := heB.symm ▸ inf_le_left
  have hfirst : rootAt Q split j (Q.simple i) ≤ D := by
    have hh := comap_mono (f := (MulAut.conj
      (representative (Q.simple i*Q.simple j) : X ⧸ Q.D)).toMonoidHom) hBK
    change rightConjugate B _ ≤ rightConjugate K _ at hh
    rw [hconjK] at hh
    dsimp only [B] at hh
    rw [right_rep] at hh
    simp only [mul_assoc,←mul_assoc (Q.simple i) (Q.simple i),ssq,one_mul,mul_one] at hh
    exact hh.trans (commutator_mono hWV hAV)
  have hlast : W ≤ D := by
    have hh := comap_mono (f := (MulAut.conj
      (representative (Q.simple j) : X ⧸ Q.D)).toMonoidHom) hfirst
    change rightConjugate (rootAt Q split j (Q.simple i)) _ ≤ rightConjugate ⁅V,V⁆ _ at hh
    dsimp only [V] at hh
    rw [right_rep,right_comm,reflection_remainder] at hh
    exact hh
  apply (not_le_of_gt hlt)
  exact sup_le (sup_le (sup_le (sup_le hfirst hCD) (hBK.trans hKD)) hED) hlast
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
