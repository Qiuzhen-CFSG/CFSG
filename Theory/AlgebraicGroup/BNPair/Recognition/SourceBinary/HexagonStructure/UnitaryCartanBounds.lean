module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.UnitaryWeights
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.OrderedProducts

/-!
# Cartan lower bounds through the actual root intervals

A nontrivial normal subgroup M of an ordered root interval either has
nonzero image on the leading root or lies in the shorter conjugate
interval. The leading image is represented by A intersection MB; it is
normal in A, has order at most |M|, and inherits the full Cartan action.
The complementary root interval is normal only relative to the larger
interval. No ambient normality is used.

Induction therefore transfers a common lower bound on Cartan-invariant
normal subgroups of the two simple roots to every nontrivial normal,
Cartan-invariant subgroup of the actual hexagon radical. In a regular
unitary root the Frattini dichotomy and center irreducibility give the
fixed-field lower bound. The CFSG companion applies this to [V',V],
retaining its literal source action and both endpoint scalar conventions.

Source: Fong--Seitz I (6D), printed p.42, the Cartan lower bound for the
nontrivial third lower-central term. The interval induction uses the
canonical ordered-root products, with right conjugation unchanged.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped Pointwise

private theorem leading_normal_section {G : Type*} [Group G] [Finite G]
    (H K A B M : Subgroup G) (hA : A ≤ K) (hM : M ≤ K)
    (hprod : (K : Set G) = (A : Set G)*(B : Set G))
    (hdis : Disjoint A B) (hKB : K ≤ normalizer (B : Set G))
    (hKM : K ≤ normalizer (M : Set G))
    (hHA : H ≤ normalizer (A : Set G)) (hHB : H ≤ normalizer (B : Set G))
    (hHM : H ≤ normalizer (M : Set G)) (hnot : ¬ M ≤ B) :
    ∃ W : Subgroup G, W ≤ A ∧ W ≠ ⊥ ∧ A ≤ normalizer (W : Set G) ∧
      H ≤ normalizer (W : Set G) ∧ Nat.card W ≤ Nat.card M := by
  let W := A ⊓ (M ⊔ B)
  have hmul : ((M ⊔ B : Subgroup G) : Set G) = (M : Set G)*(B : Set G) :=
    coe_mul_of_left_le_normalizer_right M B (hM.trans hKB)
  have hne : W ≠ ⊥ := by
    intro he
    apply hnot
    intro x hx
    have hxK : x ∈ (K : Set G) := hM hx
    rw [hprod] at hxK
    obtain ⟨a,ha,b,hb,hab⟩ := hxK
    change a*b=x at hab
    have haW : a ∈ W := ⟨ha,by
      have hh := (M ⊔ B).mul_mem (show x ∈ M ⊔ B from (show M ≤ M ⊔ B from le_sup_left) hx)
        (show b⁻¹ ∈ M ⊔ B from (show B ≤ M ⊔ B from le_sup_right) (B.inv_mem hb))
      rwa [←hab,mul_inv_cancel_right] at hh⟩
    have ha1 : a=1 := mem_bot.mp (he ▸ haW)
    rw [←hab,ha1,one_mul]
    exact hb
  have hAN : A ≤ normalizer (W : Set G) :=
    (le_inf A.le_normalizer ((le_inf (hA.trans hKM) (hA.trans hKB)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _))).trans
        inf_normalizer_le_normalizer_inf
  have hHN : H ≤ normalizer (W : Set G) :=
    (le_inf hHA ((le_inf hHM hHB).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _))).trans
        inf_normalizer_le_normalizer_inf
  have hex (w : W) : ∃ t : M, ∃ b : B, (t : G)*(b : G) = w := by
    have hw : (w : G) ∈ ((M ⊔ B : Subgroup G) : Set G) := w.property.2
    rw [hmul] at hw
    obtain ⟨t,ht,b,hb,he⟩ := hw
    exact ⟨⟨t,ht⟩,⟨b,hb⟩,he⟩
  choose t b ht using hex
  have hinj : Function.Injective t := by
    intro x y he
    have heq : (x : G)⁻¹*y = (b x : G)⁻¹*b y := by
      rw [←ht x,←ht y,he]
      group
    have hone : (x : G)⁻¹*y = 1 := disjoint_def.mp hdis
      (A.mul_mem (A.inv_mem x.property.1) y.property.1)
      (heq ▸ B.mul_mem (B.inv_mem (b x).property) (b y).property)
    exact Subtype.ext (inv_mul_eq_one.mp hone)
  exact ⟨W,inf_le_left,hne,hAN,hHN,Nat.card_le_card_of_injective t hinj⟩

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem interval_normal_card_bound
    (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
    (c : ℕ)
    (hroot : ∀ i (W : Subgroup (X ⧸ Q.D)), W ≤ simpleRoot Q split i → W ≠ ⊥ →
      simpleRoot Q split i ≤ normalizer (W : Set (X ⧸ Q.D)) →
      Q.tits.B ⊓ Q.tits.N ≤ normalizer (W : Set (X ⧸ Q.D)) → c ≤ Nat.card W)
    (b : Bool) (n : ℕ) (hn : n ≤ rotationOrder Q)
    (M : Subgroup (X ⧸ Q.D))
    (hM : M ≤ rootIntersection split (longest Q) (alternatingWord Q b n)⁻¹)
    (hne : M ≠ ⊥)
    (hMN : rootIntersection split (longest Q) (alternatingWord Q b n)⁻¹ ≤
      normalizer (M : Set (X ⧸ Q.D)))
    (hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer (M : Set (X ⧸ Q.D))) : c ≤ Nat.card M := by
  induction n generalizing b M with
  | zero =>
    change M ≤ rootIntersection split (longest Q) (1 : Weyl Q)⁻¹ at hM
    rw [inv_one,rootIntersection_one] at hM
    exact (hne (bot_unique hM)).elim
  | succ n ih =>
    let i : Fin 2 := if b then 1 else 0
    let s := representative (Q.simple i)
    let w := (alternatingWord Q (!b) n)⁻¹
    let A := simpleRoot Q split i
    let T := rootIntersection split (longest Q) w
    let B := rightConjugate T (s : X ⧸ Q.D)
    let K := rootIntersection split (longest Q) (w*Q.simple i)
    let N := simpleRemainder Q split i
    have hstepword : (alternatingWord Q b (n+1))⁻¹ = w*Q.simple i := by
      dsimp only [w,i]
      rw [alternatingWord,mul_inv_rev]
      congr 1
      exact inv_eq_of_mul_eq_one_right (by
        simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem _)).2)
    rw [hstepword] at hM hMN
    have hstep : Q.tits.wordLength (w*Q.simple i) = Q.tits.wordLength w+1 := by
      rw [←hstepword,wordLength_inv,wordLength_inv,wordLength_alternatingWord Q _ hn,
        wordLength_alternatingWord Q _ (by omega)]
    have hprod : (K : Set (X ⧸ Q.D)) = (A : Set _)*(B : Set _) :=
      rootIntersection_ascent_product Q split w i hstep s (representative_spec _)
    have hAK : A ≤ K := by
      intro a ha
      change a ∈ (K : Set (X ⧸ Q.D))
      rw [hprod]
      exact ⟨a,ha,1,one_mem _,mul_one _⟩
    have hBK : B ≤ K := by
      intro a ha
      change a ∈ (K : Set (X ⧸ Q.D))
      rw [hprod]
      exact ⟨1,one_mem _,a,ha,one_mul _⟩
    have hBN : B ≤ N :=
      ascent_root_conjugate_le_remainder Q split w i hstep s (representative_spec _)
    have hdis : Disjoint A N := simpleRoot_disjoint_remainder Q split i
    have hBKN : B = K ⊓ N := by
      apply le_antisymm (le_inf hBK hBN)
      rintro x ⟨hxK,hxN⟩
      change x ∈ (K : Set (X ⧸ Q.D)) at hxK
      rw [hprod] at hxK
      obtain ⟨a,ha,b,hb,hab⟩ := hxK
      change a*b=x at hab
      have haN : a ∈ N := by
        have hh := N.mul_mem hxN (N.inv_mem (hBN hb))
        rwa [←hab,mul_inv_cancel_right] at hh
      have ha1 := disjoint_def.mp hdis ha haN
      rw [←hab,ha1,one_mul]
      exact hb
    have hUN : split.U ≤ normalizer (N : Set (X ⧸ Q.D)) :=
      split.U_le.trans ((Q.tits.B_le_standardParabolic _).trans
        (remainder_parabolic_normalizes Q split i (hK i)))
    have hKB : K ≤ normalizer (B : Set (X ⧸ Q.D)) := by
      rw [hBKN]
      exact (le_inf K.le_normalizer (inf_le_left.trans hUN)).trans
        inf_normalizer_le_normalizer_inf
    by_cases hMB : M ≤ B
    · let a := MulAut.conj (s : X ⧸ Q.D)
      let M' := M.map a.toMonoidHom
      have hBT : B.map a.toMonoidHom = T := map_comap_eq_self_of_surjective a.surjective T
      have hM'T : M' ≤ T := hBT ▸ map_mono hMB
      have hne' : M' ≠ ⊥ := by
        intro he
        apply hne
        exact Subgroup.map_injective a.injective (he.trans (Subgroup.map_bot _).symm)
      have hTN : T ≤ normalizer (M' : Set (X ⧸ Q.D)) := by
        rw [←hBT,←map_equiv_normalizer_eq]
        exact map_mono (hBK.trans hMN)
      have hHN : Q.tits.B ⊓ Q.tits.N ≤ normalizer (M' : Set (X ⧸ Q.D)) := by
        rw [←map_equiv_normalizer_eq]
        have hh := map_mono (f := a.toMonoidHom) hH
        have heH : (Q.tits.B ⊓ Q.tits.N).map a.toMonoidHom = Q.tits.B ⊓ Q.tits.N :=
          mem_normalizer_iff_map_conj_eq.mp (torus_normalizes s)
        rwa [heH] at hh
      have hb := ih (!b) (by omega) M' hM'T hne' hTN hHN
      exact hb.trans_eq (Nat.card_congr (M.equivMapOfInjective a.toMonoidHom a.injective).toEquiv).symm
    · have hHB : Q.tits.B ⊓ Q.tits.N ≤ normalizer (B : Set (X ⧸ Q.D)) := by
        rw [hBKN]
        exact (le_inf (torus_normalizes_rootIntersection split _ _)
          (inf_le_left.trans ((Q.tits.B_le_standardParabolic _).trans
            (remainder_parabolic_normalizes Q split i (hK i))))).trans
          inf_normalizer_le_normalizer_inf
      obtain ⟨W,hWA,hWne,hAN,hHN,hc⟩ := leading_normal_section (Q.tits.B ⊓ Q.tits.N)
        K A B M hAK hM hprod (hdis.mono_right hBN) hKB hMN
        (torus_normalizes_simpleRoot Q split i) hHB hH hMB
      exact (hroot i W hWA hWne hAN hHN).trans hc

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem five_interval (hhex : rotationOrder Q = 6) (b : Bool) :
    rootIntersection split (longest Q) (alternatingWord Q b 5)⁻¹ =
      simpleRemainder Q split (if b then 0 else 1) := by
  have hsq (i : Fin 2) : Q.simple i*Q.simple i = 1 := by
    simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2
  have hi (i : Fin 2) : (Q.simple i)⁻¹ = Q.simple i := inv_eq_of_mul_eq_one_right (hsq i)
  have hlong := alternatingWord_longest Q b
  rw [hhex] at hlong
  have he : (alternatingWord Q b 5)⁻¹ = longest Q*Q.simple (if b then 0 else 1) := by
    rw [←hlong]
    cases b <;> simp only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,
      Bool.not_true,mul_inv_rev,hi,mul_one,mul_assoc,hsq]
  rw [he,rootIntersection_complement]
  rfl


/-- A nontrivial normal subgroup of the actual radical inherits the common
Cartan lower bound of its simple-root sections. -/
theorem radical_normal_subgroup_card_bound
    (hhex : rotationOrder Q = 6)
    (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
    (c : ℕ)
    (hroot : ∀ i (W : Subgroup (X ⧸ Q.D)), W ≤ simpleRoot Q split i → W ≠ ⊥ →
      simpleRoot Q split i ≤ normalizer (W : Set (X ⧸ Q.D)) →
      Q.tits.B ⊓ Q.tits.N ≤ normalizer (W : Set (X ⧸ Q.D)) → c ≤ Nat.card W)
    (j : Fin 2) (M : Subgroup (X ⧸ Q.D)) (hM : M ≤ simpleRemainder Q split j)
    (hne : M ≠ ⊥) (hMN : simpleRemainder Q split j ≤ normalizer (M : Set (X ⧸ Q.D)))
    (hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer (M : Set (X ⧸ Q.D))) : c ≤ Nat.card M := by
  have hb (b : Bool) (hbj : (if b then 0 else 1 : Fin 2) = j) : c ≤ Nat.card M := by
    apply interval_normal_card_bound Q split hK c hroot b 5 (by omega) M
    · rwa [five_interval Q split hhex b,hbj]
    · exact hne
    · rwa [five_interval Q split hhex b,hbj]
    · exact hH
  fin_cases j
  · exact hb true rfl
  · exact hb false rfl

open QuadrangleStructure
/-- Every nontrivial Cartan-invariant normal subgroup of a regular
unitary root contains its whole center and has at least fixed-field order. -/
theorem unitary_simpleRoot_normal_card_bound
    {E : Type*} [Field E] [Finite E] [CharP E 2] (J : HermitianForm 3 E)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2^n)^2)
    (hf : Nat.card {x : E // J.conj x=x} = 2^n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (i : Fin 2) (μ : localGroup Q split i ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hK : simpleRemainder Q split i ≤ localKernel Q i)
    (W : Subgroup (X ⧸ Q.D)) (hW : W ≤ simpleRoot Q split i) (hne : W ≠ ⊥)
    (hWN : simpleRoot Q split i ≤ normalizer (W : Set (X ⧸ Q.D)))
    (hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer (W : Set (X ⧸ Q.D))) :
    2^n ≤ Nat.card W := by
  let A := simpleRoot Q split i
  have hz := unitary_rootAt_frattini_center Q split J hn hcard hf hJ i μ hK 1
  rw [rootAt_one] at hz
  have hZW : (center A).map A.subtype ≤ W := by
    rcases unitary_simpleRoot_normalized_frattini_dichotomy Q split J hn hcard hf hJ
      i μ hK W hW hWN hH with hs | he
    · rw [hz.1] at hs
      exact (simpleRoot_center_eq_of_torus_invariant Q split
        (unitary_sylow_center_irreducible J (by omega) hcard hf hJ) i μ hK W hs hne hH).ge
    · rw [he]
      exact map_subtype_le _
  have hc : Nat.card ((center A).map A.subtype) = 2^n := by
    rw [←Nat.card_congr ((center A).equivMapOfInjective A.subtype A.subtype_injective).toEquiv]
    exact hz.1 ▸ hz.2
  rw [←hc]
  exact card_le_of_le hZW

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
