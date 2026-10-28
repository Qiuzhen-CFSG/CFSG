module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.LayerCoordinates

/-!
# Interior support of the first Suzuki cross commutator

The commutator of U₂ and U₂^s₁ lies in both Uₛ₂ and its s₁-conjugate,
by relative normality, and in Uₛ₁. Carter's unique eight-root product
then removes its three outside factors. What remains is the five literal
interior roots, with their original order and source reflection unchanged.
This supplies the reflected-displacement bound used to distinguish the
second line of V₂ also when q = 2.

Source: Fong--Seitz I (1973), (3G); II (1974), the discussion of (10.4)
and (10.5), printed p.222. The consumer is ReeSection10.V2MiddleLines.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

set_option linter.unusedSimpArgs false in
include c in
theorem positiveRoot_le_remainder (r : ReeF4.RootPresentationRecognition.PositiveTables.Root)
    (i : Fin 2) (hr : r ≠ if i = 0 then .inl 0 else .inr 0) :
    positiveRoot Q split r ≤ simpleRemainder Q split i := by
  have hs (k : Fin 2) : (Q.simple k)⁻¹ = Q.simple k :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using
      (Q.tits.involutions _ (Q.simple_mem k)).2)
  have hss (k : Fin 2) : Q.simple k*Q.simple k = 1 := by
    simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem k)).2
  have hl (b : Bool) := And.intro
    (wordLength_alternatingWord Q b (n := 1) (by rw [c.rotation_eight]; omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 2) (by rw [c.rotation_eight]; omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 3) (by rw [c.rotation_eight]; omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 4) (by rw [c.rotation_eight]; omega))
    (wordLength_alternatingWord Q b (n := 5) (by rw [c.rotation_eight]; omega)))))
  have hf := hl false
  have ht := hl true
  simp only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,
    Bool.not_true,mul_one] at hf ht
  fin_cases i <;> cases r with
  | inl j =>
    fin_cases j
    all_goals first | exact (hr rfl).elim | skip
    all_goals
      apply rootAt_le_remainder
      all_goals simp [positiveKind,positiveWord,mul_inv_rev,hs,mul_assoc,
        ←mul_assoc (Q.simple 0) (Q.simple 0),←mul_assoc (Q.simple 1) (Q.simple 1),
        hss,one_mul,Q.tits.wordLength_one,
        hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2,
        ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.1,ht.2.2.2.2]
  | inr j =>
    fin_cases j
    all_goals first | exact (hr rfl).elim | skip
    all_goals
      apply rootAt_le_remainder
      all_goals simp [positiveKind,positiveWord,mul_inv_rev,hs,mul_assoc,
        ←mul_assoc (Q.simple 0) (Q.simple 0),←mul_assoc (Q.simple 1) (Q.simple 1),
        hss,one_mul,Q.tits.wordLength_one,
        hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2,
        ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.1,ht.2.2.2.2]

/-- The five roots strictly between U₂ and U₂^s₁, in Carter order. -/
def V2InteriorFactors : List (Subgroup (X ⧸ Q.D)) :=
  [positiveRoot Q split (.inl 2),positiveRoot Q split (.inr 1),
   positiveRoot Q split (.inl 3),positiveRoot Q split (.inr 3),
   positiveRoot Q split (.inl 1)]

include c in
private theorem V2Interior_le_reflected_remainder :
    ∀ A ∈ V2InteriorFactors Q split,
      A ≤ rightConjugate (simpleRemainder Q split 1) ((c.reflections 0).val : X ⧸ Q.D) := by
  have hs (k : Fin 2) : (Q.simple k)⁻¹ = Q.simple k :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using
      (Q.tits.involutions _ (Q.simple_mem k)).2)
  have hss (k : Fin 2) : Q.simple k*Q.simple k = 1 := by
    simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem k)).2
  have hl (b : Bool) := And.intro
    (wordLength_alternatingWord Q b (n := 1) (by rw [c.rotation_eight]; omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 2) (by rw [c.rotation_eight]; omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 3) (by rw [c.rotation_eight]; omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 4) (by rw [c.rotation_eight]; omega))
    (wordLength_alternatingWord Q b (n := 5) (by rw [c.rotation_eight]; omega)))))
  have hf := hl false
  have ht := hl true
  simp only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,
    Bool.not_true,mul_one] at hf ht
  have ht6 := wordLength_alternatingWord Q true (n := 6) (by rw [c.rotation_eight]; omega)
  simp only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,
    Bool.not_true,mul_one] at ht6
  intro A hA
  simp only [V2InteriorFactors,List.mem_cons,List.not_mem_nil,or_false] at hA
  rcases hA with rfl | rfl | rfl | rfl | rfl
  all_goals
    rw [simpleRemainder,rightConjugate_inf,
      ←unipotentConjugate_eq split _ _ (c.reflections 0).class_eq,
      unipotentConjugate_right split _ _ _ (c.reflections 0).class_eq]
    apply le_inf
    all_goals
      apply rootAt_le_conjugate
      simp [positiveKind,positiveWord,mul_inv_rev,hs,mul_assoc,
        ←mul_assoc (Q.simple 0) (Q.simple 0),←mul_assoc (Q.simple 1) (Q.simple 1),
        hss,one_mul,Q.tits.wordLength_one,
        hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2,
        ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.1,ht.2.2.2.2,ht6]

include c in
theorem V2_cross_commutator_support (x : X ⧸ Q.D)
    (hx : x ∈ ⁅simpleRoot Q split 1,positiveRoot Q split (.inr 2)⁆) :
    x ∈ Set.range (rootProduct (V2InteriorFactors Q split)) := by
  let V := simpleRemainder Q split 1
  let R := rightConjugate V ((c.reflections 0).val : X ⧸ Q.D)
  have hN : split.U ≤ normalizer (V : Set (X ⧸ Q.D)) :=
    split.U_le.trans ((Q.tits.B_le_standardParabolic _).trans
      (remainder_parabolic_normalizes Q split 1 (remainder_le_kernel Q split c)))
  have hC : positiveRoot Q split (.inr 2) ≤ V :=
    positiveRoot_le_remainder Q split c _ _ (by decide)
  have hxV : x ∈ V :=
    ((commutator_mono (simpleRoot_le Q split 1) hC).trans
      (le_normalizer_iff_commutator_le_right.mp hN)) hx
  have hA : simpleRoot Q split 1 ≤ R := by
    have h := comap_mono hC (f := (MulAut.conj ((c.reflections 0).val : X ⧸ Q.D)).toMonoidHom)
    change rightConjugate (positiveRoot Q split (.inr 2))
      ((c.reflections 0).val : X ⧸ Q.D) ≤ R at h
    change rightConjugate (rootAt Q split 1 (Q.simple 0))
      ((c.reflections 0).val : X ⧸ Q.D) ≤ R at h
    rw [rootAt_right Q split 1 _ _ _ (c.reflections 0).class_eq] at h
    have hss : Q.simple 0*Q.simple 0 = 1 := by
      simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem 0)).2
    simpa only [hss,rootAt_one] using h
  have hroot : positiveRoot Q split (.inr 2) =
      rightConjugate (simpleRoot Q split 1) ((c.reflections 0).val : X ⧸ Q.D) :=
    rootAt_eq Q split 1 _ _ (c.reflections 0).class_eq
  have hCN : positiveRoot Q split (.inr 2) ≤ normalizer (R : Set (X ⧸ Q.D)) := by
    rw [hroot]
    exact (comap_mono ((simpleRoot_le Q split 1).trans hN)).trans (le_normalizer_comap _)
  have hxR : x ∈ R := by
    have h := (commutator_mono hA le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hCN)
    exact h hx
  have hU : x ∈ split.U := hxV.1
  have hp : x ∈ Set.range (rootProduct (orderedRoots Q split false (rotationOrder Q))) := by
    obtain ⟨p,hp⟩ := (unipotentOrderedCoordinates Q split false).surjective ⟨x,hU⟩
    exact ⟨p,(unipotentOrderedCoordinates_apply Q split false p).symm.trans
      (congrArg Subtype.val hp)⟩
  rw [c.rotation_eight,positiveRoot_ordered Q split c.rotation_eight] at hp
  change ∃ p : RootTuple [positiveRoot Q split (.inl 0),positiveRoot Q split (.inr 2),
      positiveRoot Q split (.inl 2),positiveRoot Q split (.inr 1),positiveRoot Q split (.inl 3),
      positiveRoot Q split (.inr 3),positiveRoot Q split (.inl 1),positiveRoot Q split (.inr 0)],
    rootProduct _ p = x at hp
  obtain ⟨⟨a,b,d,e,f,g,h,k,t⟩,hp⟩ := hp
  have hp : (a : X ⧸ Q.D)*b*d*e*f*g*h*k = x := by
    simpa only [rootProduct,mul_one,mul_assoc] using hp
  let z := rootProduct (V2InteriorFactors Q split) (d,e,f,g,h,t)
  have hz0 : z ∈ simpleRemainder Q split 0 := by
    apply rootProduct_mem
    intro A hA
    simp only [V2InteriorFactors,List.mem_cons,List.not_mem_nil,or_false] at hA
    rcases hA with rfl | rfl | rfl | rfl | rfl
    all_goals exact positiveRoot_le_remainder Q split c _ _ (by decide)
  have hzV : z ∈ V := by
    apply rootProduct_mem
    intro A hA
    simp only [V2InteriorFactors,List.mem_cons,List.not_mem_nil,or_false] at hA
    rcases hA with rfl | rfl | rfl | rfl | rfl
    all_goals exact positiveRoot_le_remainder Q split c _ _ (by decide)
  have hzR : z ∈ R := rootProduct_mem _ _
    (V2Interior_le_reflected_remainder Q split c) _
  have hp : (a : X ⧸ Q.D)*((b : X ⧸ Q.D)*z*(k : X ⧸ Q.D)) = x := by
    simpa only [z,V2InteriorFactors,rootProduct,mul_one,mul_assoc] using hp
  have hx0 : x ∈ simpleRemainder Q split 0 := by
    apply (commutator_le_self (simpleRemainder Q split 0))
    apply commutator_mono _ _ hx
    · simpa only [positiveRoot,positiveKind,positiveWord,Matrix.cons_val,
        Fin.isValue,Matrix.head_cons,rootAt_one] using
        positiveRoot_le_remainder Q split c (.inr 0) 0 (by decide)
    · exact positiveRoot_le_remainder Q split c _ _ (by decide)
  have hb0 := positiveRoot_le_remainder Q split c (.inr 2) 0 (by decide) b.property
  have hk0 := positiveRoot_le_remainder Q split c (.inr 0) 0 (by decide) k.property
  have ha0 : (a : X ⧸ Q.D) ∈ simpleRemainder Q split 0 := by
    have hh := (simpleRemainder Q split 0).mul_mem hx0
      ((simpleRemainder Q split 0).inv_mem
        ((simpleRemainder Q split 0).mul_mem
          ((simpleRemainder Q split 0).mul_mem hb0 hz0) hk0))
    rw [←hp,mul_inv_cancel_right] at hh
    exact hh
  have ha : (a : X ⧸ Q.D) = 1 := disjoint_def.mp
    (simpleRoot_disjoint_remainder Q split 0) (by simpa [positiveRoot,positiveKind,positiveWord] using a.property) ha0
  rw [ha,one_mul] at hp
  have hkV : (k : X ⧸ Q.D) ∈ V := by
    have hh := V.mul_mem (V.inv_mem (V.mul_mem (hC b.property) hzV)) hxV
    rw [←hp,inv_mul_cancel_left] at hh
    exact hh
  have hk : (k : X ⧸ Q.D) = 1 := disjoint_def.mp
    (simpleRoot_disjoint_remainder Q split 1) (by simpa [positiveRoot,positiveKind,positiveWord] using k.property) hkV
  rw [hk,mul_one] at hp
  have hbR : (b : X ⧸ Q.D) ∈ R := by
    have hh := R.mul_mem hxR (R.inv_mem hzR)
    rw [←hp,mul_inv_cancel_right] at hh
    exact hh
  have hb : (b : X ⧸ Q.D) = 1 := by
    apply (MulAut.conj ((c.reflections 0).val : X ⧸ Q.D)).injective
    exact (disjoint_def.mp (simpleRoot_disjoint_remainder Q split 1)
      (hroot.le b.property) hbR).trans (map_one _).symm
  rw [hb,one_mul] at hp
  exact ⟨(d,e,f,g,h,t),hp⟩

end Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
