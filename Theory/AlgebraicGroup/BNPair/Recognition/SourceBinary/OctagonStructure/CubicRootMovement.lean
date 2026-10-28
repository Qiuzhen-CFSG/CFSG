module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicSeparation

/-!
# Root movement in the cubic fixed radical of an octagon

The simple reflection exchanges two disjoint nontrivial roots. If the
first root centralizes the nearer conjugate, it therefore cannot centralize
the farther one. For a separating cubic actor, this gives the nonzero
commutator [U_i,U_i^(s_j)]. The fixed radical has three root coordinates;
normality of the reflected radical removes the first coordinate of this
commutator, leaving the two middle fixed roots.

When |U_i| = 2, the two zero commutators already proved by the cubic
calculation make this nonzero commutator an involution subgroup. Reflection
exchanges its two coordinates and centralizes the involution, so both
coordinates are nonidentity. This constructs the actual diagonal <xy> used
in the degree-one normalizer argument, without assuming a class-two radical.

Source: Fong--Seitz I (1973), (6G), printed p.50, the paragraph beginning
“Let U_1^(s_2 s_1 s_2) = <x>”. The original-factor and Chapter 12 consumers
are in LinearPairCubicDegreeOneSource and LinearPairCubicDegreeOneChapter12.
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
private theorem simple_sq (i : Fin 2) : Q.simple i*Q.simple i = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2
private theorem simple_inv (i : Fin 2) : (Q.simple i)⁻¹ = Q.simple i :=
  inv_eq_of_mul_eq_one_right (simple_sq Q i)
private theorem right_rep (i : Fin 2) (v w : Weyl Q) :
    rightConjugate (rootAt Q split i v) (representative w : X ⧸ Q.D) =
      rootAt Q split i (v*w) := rootAt_right Q split i v w _ (representative_spec _)
private theorem octagon_lengths (i : Fin 2) (hm : rotationOrder Q = 8) (j : Fin 2) (hij : i ≠ j) :
    Q.tits.wordLength (Q.simple i) = 1 ∧
    Q.tits.wordLength (Q.simple i*Q.simple j) = 2 ∧
    Q.tits.wordLength (Q.simple i*Q.simple j*Q.simple i) = 3 ∧
    Q.tits.wordLength (Q.simple i*Q.simple j*Q.simple i*Q.simple j) = 4 ∧
    Q.tits.wordLength (Q.simple i*Q.simple j*Q.simple i*Q.simple j*Q.simple i) = 5 := by
  have hh (b : Bool) := And.intro
    (wordLength_alternatingWord Q b (n := 1) (by omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 2) (by omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 3) (by omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 4) (by omega))
    (wordLength_alternatingWord Q b (n := 5) (by omega)))))
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.not_true, mul_one, mul_assoc] using hh false
  · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.not_true, mul_one, mul_assoc] using hh true
  · exact (hij rfl).elim

private theorem octagon_exchanged_roots_disjoint (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) :
    Disjoint (rootAt Q split i (Q.simple j))
      (rootAt Q split i (Q.simple j*Q.simple i)) := by
  apply rootAt_disjoint Q split i (Q.simple j) (Q.simple j*Q.simple i)
  simp only [mul_inv_rev, simple_inv, ←mul_assoc]
  have hh := octagon_lengths Q i hm j hij
  rw [hh.2.2.2.1, hh.2.2.2.2]


/-- Reflection forces the long commutator to be nonzero once the nearer
commutator vanishes. Both roots are in the same marked octagon. -/
theorem separated_long_commutator_ne_bot
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (s : HexagonStructure.RootReflection Q split i)
    (hAC : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥) :
    ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ ≠ ⊥ := by
  intro hAE
  have hcE := commutator_eq_bot_iff_le_centralizer.mp hAE
  have hcC := commutator_eq_bot_iff_le_centralizer.mp hAC
  have hni : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) s.val⁻¹ =
      Q.simple i := by rw [map_inv,s.class_eq,simple_inv]
  have hRC : rankOne Q split i ≤ centralizer (rootAt Q split i (Q.simple j) : Set _) := by
    apply sup_le hcE
    intro x hx
    rw [rootAt_eq Q split i (Q.simple i) s.val s.class_eq] at hx
    change (s.val : X ⧸ Q.D)*x*(s.val : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split i at hx
    apply mem_centralizer_iff.mpr
    intro y hy
    have hy' : (s.val : X ⧸ Q.D)*y*(s.val : X ⧸ Q.D)⁻¹ ∈
        rootAt Q split i (Q.simple j*Q.simple i) := by
      rw [← rootAt_right Q split i (Q.simple j) (Q.simple i) s.val⁻¹ hni]
      change (s.val : X ⧸ Q.D)⁻¹*((s.val : X ⧸ Q.D)*y*(s.val : X ⧸ Q.D)⁻¹)*
        ((s.val : X ⧸ Q.D)⁻¹)⁻¹ ∈ rootAt Q split i (Q.simple j)
      simpa only [inv_inv,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using (show y ∈ rootAt Q split i (Q.simple j) from hy)
    have he := mem_centralizer_iff.mp (hcC hx) _ hy'
    apply (MulAut.conj (s.val : X ⧸ Q.D)).injective
    simpa only [map_mul,MulAut.conj_apply] using he
  have he : rootAt Q split i (Q.simple j*Q.simple i) = rootAt Q split i (Q.simple j) := by
    rw [← rootAt_right Q split i (Q.simple j) (Q.simple i) s.val s.class_eq]
    exact rightConjugate_eq_self _ (Subgroup.centralizer_le_normalizer _ (hRC s.mem_rankOne))
  have hd := octagon_exchanged_roots_disjoint Q split hm i j hij
  rw [he,disjoint_self] at hd
  exact rootAt_ne_bot Q split i (Q.simple j) hd

/-- In the fixed radical the long-root commutator has only its two
middle coordinates. The reflected radical removes the first coordinate. -/
theorem separated_long_commutator_support (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hK : simpleRemainder Q split i ≤ localKernel Q i)
    (c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)))
    (hc : ∀ w : Weyl Q,
      (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) ∧
      rootAt Q split j w ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥)
    (x : X ⧸ Q.D)
    (hx : x ∈ ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆) :
    x ∈ (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) : Set (X ⧸ Q.D)) *
      (rootAt Q split i (Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) := by
  let A := rootAt Q split i (Q.simple j)
  let B := rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let K := simpleRemainder Q split i ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D))
  let V := simpleRemainder Q split i
  let n := representative (Q.simple j)
  let R := rightConjugate V (n : X ⧸ Q.D)
  have hp : (K : Set (X ⧸ Q.D)) = (A : Set _)*(B : Set _)*(C : Set _) :=
    separated_radical_centralizer_product Q split hm i j hij c hc
  have hjoin : A ⊔ B ⊔ C = K := separated_radical_centralizer_sup Q split hm i j hij c hc
  have hAK : A ≤ K := hjoin ▸ le_sup_of_le_left le_sup_left
  have hBK : B ≤ K := hjoin ▸ le_sup_of_le_left le_sup_right
  have hCK : C ≤ K := hjoin ▸ le_sup_right
  have hAR : simpleRoot Q split i ≤ R := by
    have hh := comap_mono (f := (MulAut.conj (n : X ⧸ Q.D)).toMonoidHom)
      (hAK.trans inf_le_left)
    change rightConjugate A (n : X ⧸ Q.D) ≤ R at hh
    simpa only [A,n,right_rep,simple_sq,rootAt_one] using hh
  have hBR : B ≤ R := by
    have hh := comap_mono (f := (MulAut.conj (n : X ⧸ Q.D)).toMonoidHom)
      (hCK.trans inf_le_left)
    change rightConjugate C (n : X ⧸ Q.D) ≤ R at hh
    simpa only [B,C,n,right_rep] using hh
  have hCR : C ≤ R := by
    have hh := comap_mono (f := (MulAut.conj (n : X ⧸ Q.D)).toMonoidHom)
      (hBK.trans inf_le_left)
    change rightConjugate B (n : X ⧸ Q.D) ≤ R at hh
    simpa only [B,C,n,right_rep,mul_assoc,simple_sq,mul_one] using hh
  have hUR : simpleRoot Q split i ≤ normalizer (V : Set (X ⧸ Q.D)) :=
    (show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left).trans
      ((rankOne_le_parabolic Q split i).trans (remainder_parabolic_normalizes Q split i hK))
  have hNR : A ≤ normalizer (R : Set (X ⧸ Q.D)) :=
    (comap_mono hUR).trans (le_normalizer_comap _)
  have hxR : x ∈ R :=
    ((commutator_mono hAR le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hNR)) hx
  have hUK : simpleRoot Q split i ≤ normalizer (K : Set (X ⧸ Q.D)) :=
    (show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left).trans
      (separated_radical_centralizer_normalized Q split i hK c (fun w => (hc w).1))
  have hxK : x ∈ (K : Set (X ⧸ Q.D)) :=
    ((commutator_mono le_rfl hAK).trans
      (le_normalizer_iff_commutator_le_right.mp hUK)) hx
  rw [hp] at hxK
  obtain ⟨ab,⟨a,ha,b,hb,rfl⟩,d,hd,rfl⟩ := hxK
  have haR : a ∈ R := by
    have hh := R.mul_mem hxR (R.inv_mem (R.mul_mem (hBR hb) (hCR hd)))
    simpa only [mul_inv_rev,mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using hh
  have ha1 : a = 1 := by
    apply (MulAut.conj (n : X ⧸ Q.D)).injective
    exact (disjoint_def.mp (simpleRoot_disjoint_remainder Q split i) ha haR).trans
      (map_one _).symm
  subst a
  exact ⟨b,hb,d,hd,by simp only [one_mul]⟩

open scoped commutatorElement

private theorem two_root_commutator_card {Y : Type*} [Group Y]
    (A B : Subgroup Y) (hA : Nat.card A = 2) (hB : Nat.card B = 2)
    (hne : ⁅A,B⁆ ≠ ⊥) (hc : A ≤ centralizer ((⁅A,B⁆ : Subgroup Y) : Set Y)) :
    Nat.card (⁅A,B⁆ : Subgroup Y) = 2 := by
  obtain ⟨a,ha,hau⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
  obtain ⟨b,hb,hbu⟩ := (Nat.card_eq_two_iff' (1 : B)).mp hB
  have hcasesA (x : A) : x = 1 ∨ x = a := by
    by_cases hh : x = 1
    · exact Or.inl hh
    · exact Or.inr (hau x hh)
  have hcasesB (x : B) : x = 1 ∨ x = b := by
    by_cases hh : x = 1
    · exact Or.inl hh
    · exact Or.inr (hbu x hh)
  have heq : ⁅A,B⁆ = zpowers ⁅(a : Y),(b : Y)⁆ := by
    apply le_antisymm
    · apply commutator_le.mpr
      intro x hx y hy
      rcases hcasesA ⟨x,hx⟩ with hh | hh
      · have hx1 := congrArg Subtype.val hh
        change x = 1 at hx1
        rw [hx1,commutatorElement_one_left]
        exact one_mem _
      · have hxa := congrArg Subtype.val hh
        change x = (a : Y) at hxa
        rw [hxa]
        rcases hcasesB ⟨y,hy⟩ with hh | hh
        · have hy1 := congrArg Subtype.val hh
          change y = 1 at hy1
          rw [hy1,commutatorElement_one_right]
          exact one_mem _
        · have hyb := congrArg Subtype.val hh
          change y = (b : Y) at hyb
          rw [hyb]
          exact mem_zpowers _
    · exact zpowers_le.mpr (commutator_mem_commutator a.property b.property)
  have hne' : ⁅(a : Y),(b : Y)⁆ ≠ 1 := by
    intro he
    apply hne
    rw [heq,he,zpowers_one_eq_bot]
  have ha2 : (a : Y)*(a : Y) = 1 := by
    have hh := congrArg Subtype.val (pow_card_eq_one' (x := a))
    simpa only [hA,pow_two,coe_mul,coe_one] using hh
  have hcomm : (a : Y)*⁅(a : Y),(b : Y)⁆ = ⁅(a : Y),(b : Y)⁆*(a : Y) :=
    (mem_centralizer_iff.mp (hc a.property) _
      (commutator_mem_commutator a.property b.property)).symm
  have hpow : ⁅(a : Y),(b : Y)⁆^2 = 1 := by
    have hh := commutatorElement_mul_left_eq_conj_mul (a : Y) a b
    rw [ha2,commutatorElement_one_left,hcomm,mul_inv_cancel_right] at hh
    simpa only [pow_two] using hh.symm
  rw [heq,Nat.card_zpowers]
  exact orderOf_eq_prime hpow hne'

/-- With a binary fixed root, the nonzero long commutator is an involution
subgroup. Its centrality under the first root comes from the two fixed
middle coordinates, not from an assumed class-two radical. -/
theorem separated_binary_long_commutator_card (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hK : simpleRemainder Q split i ≤ localKernel Q i)
    (s : HexagonStructure.RootReflection Q split i)
    (hcard : Nat.card (simpleRoot Q split i) = 2)
    (c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)))
    (hc : ∀ w : Weyl Q,
      (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) ∧
      rootAt Q split j w ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥)
    (hperp : ⁅simpleRoot Q split i,
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ = ⊥) :
    Nat.card (⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ : Subgroup (X ⧸ Q.D)) = 2 := by
  have hzero := separated_distance_two_commutator Q split hm i j hij hK c hc
  apply two_root_commutator_card _ _ hcard
    (by simpa only [rootAt,card_rightConjugate] using hcard)
    (separated_long_commutator_ne_bot Q split hm i j hij s hzero)
  intro u hu
  apply mem_centralizer_iff.mpr
  intro x hx
  obtain ⟨b,hb,d,hd,rfl⟩ := separated_long_commutator_support Q split hm i j hij hK c hc x hx
  have hb' := mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hperp hu) b hb
  have hd' := mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero hu) d hd
  calc
    b*d*u = b*(d*u) := mul_assoc _ _ _
    _ = b*(u*d) := by rw [hd']
    _ = (b*u)*d := (mul_assoc _ _ _).symm
    _ = (u*b)*d := by rw [hb']
    _ = u*(b*d) := mul_assoc _ _ _

/-- The binary long commutator is the diagonal involution in the two
middle roots. Both coordinates are nonidentity, as on printed p.50. -/
theorem separated_binary_long_commutator_diagonal (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hK : simpleRemainder Q split i ≤ localKernel Q i)
    (s : HexagonStructure.RootReflection Q split i)
    (hcard : Nat.card (simpleRoot Q split i) = 2)
    (c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)))
    (hc : ∀ w : Weyl Q,
      (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) ∧
      rootAt Q split j w ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥)
    (hperp : ⁅simpleRoot Q split i,
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ = ⊥) :
    ∃ x ∈ rootAt Q split i (Q.simple j*Q.simple i*Q.simple j),
      ∃ y ∈ rootAt Q split i (Q.simple j*Q.simple i),
        x ≠ 1 ∧ y ≠ 1 ∧
        ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ = zpowers (x*y) ∧
        orderOf (x*y) = 2 := by
  let D := ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆
  let B := rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let n := representative (Q.simple j)
  have hD : Nat.card D = 2 :=
    separated_binary_long_commutator_card Q split hm i j hij hK s hcard c hc hperp
  have hDC : rightConjugate D (n : X ⧸ Q.D) = D := by
    change rightConjugate ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ _ = _
    have he (A E : Subgroup (X ⧸ Q.D)) : rightConjugate ⁅A,E⁆ (n : X ⧸ Q.D) =
        ⁅rightConjugate A (n : X ⧸ Q.D),rightConjugate E (n : X ⧸ Q.D)⁆ := by
      simp only [rightConjugate,comap_equiv_eq_map_symm',map_commutator]
    rw [he]
    change ⁅rootAt Q split i (Q.simple j),rightConjugate (rootAt Q split i (Q.simple j))
      (representative (Q.simple j) : X ⧸ Q.D)⁆ = _
    rw [right_rep,simple_sq,rootAt_one,commutator_comm]
  have hn : (n : X ⧸ Q.D) ∈ normalizer (D : Set (X ⧸ Q.D)) := by
    rw [mem_normalizer_iff]
    intro z
    change z ∈ D ↔ z ∈ rightConjugate D (n : X ⧸ Q.D)
    rw [hDC]
  have hnC := normalizer_le_centralizer_of_card_two D hD hn
  have hBC : Disjoint B C := by
    apply rootAt_disjoint Q split i _ _
    simp only [mul_inv_rev,simple_inv,←mul_assoc]
    have hh (b : Bool) := And.intro
      (wordLength_alternatingWord Q b (n := 6) (by omega))
      (wordLength_alternatingWord Q b (n := 7) (by omega))
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;>
      rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · exact (hij rfl).elim
    · have hl := hh false
      simp only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,
        Bool.not_true,mul_one,←mul_assoc] at hl
      rw [hl.1,hl.2]
    · have hl := hh true
      simp only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,
        Bool.not_true,mul_one,←mul_assoc] at hl
      rw [hl.1,hl.2]
    · exact (hij rfl).elim
  obtain ⟨d,hd,hdu⟩ := (Nat.card_eq_two_iff' (1 : D)).mp hD
  have hdne : (d : X ⧸ Q.D) ≠ 1 := by
    intro he
    exact hd (Subtype.ext he)
  obtain ⟨x,hx,y,hy,hxy⟩ := separated_long_commutator_support Q split hm i j hij hK c hc d d.property
  change x*y = (d : X ⧸ Q.D) at hxy
  have hconj : (n : X ⧸ Q.D)*(d : X ⧸ Q.D)*(n : X ⧸ Q.D)⁻¹ = d := by
    rw [←mem_centralizer_iff.mp hnC _ d.property,mul_inv_cancel_right]
  have hswapC : rightConjugate C (n : X ⧸ Q.D) = B := by
    dsimp only [C,B,n]
    rw [right_rep]
  have hswapB : rightConjugate B (n : X ⧸ Q.D) = C := by
    dsimp only [C,B,n]
    rw [right_rep]
    simp only [mul_assoc,simple_sq,mul_one]
  have hxne : x ≠ 1 := by
    intro hx1
    have hdC : (d : X ⧸ Q.D) ∈ C := by
      rw [←hxy,hx1,one_mul]
      exact hy
    have hdB : (d : X ⧸ Q.D) ∈ B := by
      rw [←hswapC]
      change (n : X ⧸ Q.D)*(d : X ⧸ Q.D)*(n : X ⧸ Q.D)⁻¹ ∈ C
      rwa [hconj]
    exact hdne (disjoint_def.mp hBC hdB hdC)
  have hyne : y ≠ 1 := by
    intro hy1
    have hdB : (d : X ⧸ Q.D) ∈ B := by
      rw [←hxy,hy1,mul_one]
      exact hx
    have hdC : (d : X ⧸ Q.D) ∈ C := by
      rw [←hswapB]
      change (n : X ⧸ Q.D)*(d : X ⧸ Q.D)*(n : X ⧸ Q.D)⁻¹ ∈ B
      rwa [hconj]
    exact hdne (disjoint_def.mp hBC hdB hdC)
  have hgen : D = zpowers (d : X ⧸ Q.D) := by
    apply le_antisymm
    · intro z hz
      by_cases hz1 : z = 1
      · rw [hz1]; exact one_mem _
      · have he : (⟨z,hz⟩ : D) = d := hdu _ (fun he => hz1 (congrArg Subtype.val he))
        rw [show z = (d : X ⧸ Q.D) from congrArg Subtype.val he]
        exact mem_zpowers _
    · exact zpowers_le.mpr d.property
  refine ⟨x,hx,y,hy,hxne,hyne,?_,?_⟩
  · rw [hxy]
    exact hgen
  · rw [hxy,←Nat.card_zpowers,←hgen]
    exact hD

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
