module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.LinearDerived

/-!
# The linear radical's five-root interior and Frattini denominator

The seven ordered roots of U_s₁ give unique coordinates. Its five interior
roots form the intersection of U_s₁, U_s₂ and U_s₂^s₁, so the generated T₁
is the printed ordered product and is normal in U_s₁. Multiplication of the
two endpoint Suzuki roots then identifies U_s₁/T₁ with their direct product.
Taking both first-coordinate maps constructs the literal denominator
X₁ = Omega₁(U₂^s₁) T₁ Omega₁(U₂), proves its ordered-product formula and
relative normality, and gives |U_s₁/X₁| = q² for every parameter, including q=2.

This quotient bounds the actual Frattini and derived subgroups from above.
When T₁ is contained in the derived subgroup, Frattini functoriality supplies
the converse and makes X₁ characteristic. LinearCharacteristic discharges
that premise for q>2 and the binary whole-shifted-root branch. The binary
noncontainment branch still requires the separate abelianization argument;
normality and order alone do not establish characteristicity or a natural
rank-one action there.

Source: Fong--Seitz I (1973), (3G); II (1974), printed p.222, between
(10.5) and (10.6). All quotients are taken inside the same literal radical.
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

def linearFactors : List (Subgroup (X ⧸ Q.D)) :=
  [positiveRoot Q split (.inr 2),positiveRoot Q split (.inl 2),
   positiveRoot Q split (.inr 1),positiveRoot Q split (.inl 3),
   positiveRoot Q split (.inr 3),positiveRoot Q split (.inl 1),
   positiveRoot Q split (.inr 0)]

include c in
private theorem linearFactors_le : ∀ A ∈ linearFactors Q split,
    A ≤ simpleRemainder Q split 0 := by
  intro A hA
  simp only [linearFactors,List.mem_cons,List.not_mem_nil,or_false] at hA
  rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact positiveRoot_le_remainder Q split c _ 0 (by decide)

include c in
theorem linearProduct_injective : Function.Injective (rootProduct (linearFactors Q split)) := by
  have hi : Function.Injective (rootProduct (orderedRoots Q split false 8)) := by
    intro p q he
    apply (orderedCoordinates Q split false 8 (by rw [c.rotation_eight])).injective
    apply Subtype.ext
    simpa only [orderedCoordinates_apply] using he
  rw [positiveRoot_ordered Q split c.rotation_eight] at hi
  change Function.Injective (rootProduct (positiveRoot Q split (.inl 0) :: linearFactors Q split)) at hi
  intro p q he
  exact congrArg Prod.snd (hi (a₁ := (1,p)) (a₂ := (1,q)) (by
    simpa only [rootProduct,OneMemClass.coe_one,one_mul] using he))

include c in
theorem linearProduct_range : Set.range (rootProduct (linearFactors Q split)) =
    (simpleRemainder Q split 0 : Set (X ⧸ Q.D)) := by
  apply Set.Subset.antisymm
  · rintro x ⟨p,rfl⟩
    exact rootProduct_mem _ _ (linearFactors_le Q split c) _
  · intro x hx
    have hp : x ∈ Set.range (rootProduct (orderedRoots Q split false (rotationOrder Q))) := by
      obtain ⟨p,hp⟩ := (unipotentOrderedCoordinates Q split false).surjective ⟨x,hx.1⟩
      exact ⟨p,(unipotentOrderedCoordinates_apply Q split false p).symm.trans
        (congrArg Subtype.val hp)⟩
    rw [c.rotation_eight,positiveRoot_ordered Q split c.rotation_eight] at hp
    change ∃ p : RootTuple (positiveRoot Q split (.inl 0) :: linearFactors Q split),
      rootProduct _ p = x at hp
    obtain ⟨p,he⟩ := hp
    let z := rootProduct (linearFactors Q split) p.2
    have hz : z ∈ simpleRemainder Q split 0 :=
      rootProduct_mem _ _ (linearFactors_le Q split c) _
    have he : (p.1 : X ⧸ Q.D)*z = x := he
    have ha : (p.1 : X ⧸ Q.D) ∈ simpleRemainder Q split 0 := by
      have hh := (simpleRemainder Q split 0).mul_mem hx ((simpleRemainder Q split 0).inv_mem hz)
      rw [←he,mul_inv_cancel_right] at hh
      exact hh
    have ha1 : (p.1 : X ⧸ Q.D) = 1 := disjoint_def.mp
      (simpleRoot_disjoint_remainder Q split 0)
      (by simpa [positiveRoot,positiveKind,positiveWord] using p.1.property) ha
    exact ⟨p.2,by simpa only [ha1,one_mul] using he⟩

include c in
private theorem interior_le_reflected_remainder :
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


def linearInterior (c : ReeSixHData Q split n m) : Subgroup (X ⧸ Q.D) :=
  simpleRemainder Q split 0 ⊓ simpleRemainder Q split 1 ⊓
    rightConjugate (simpleRemainder Q split 1) ((c.reflections 0).val : X ⧸ Q.D)

include c in
private theorem interiorFactors_le : ∀ A ∈ V2InteriorFactors Q split,
    A ≤ linearInterior Q split c := by
  intro A hA
  refine le_inf (le_inf ?_ ?_) (interior_le_reflected_remainder Q split c A hA)
  all_goals
    simp only [V2InteriorFactors,List.mem_cons,List.not_mem_nil,or_false] at hA
    rcases hA with rfl | rfl | rfl | rfl | rfl
    all_goals exact positiveRoot_le_remainder Q split c _ _ (by decide)

include c in
theorem interiorProduct_range : Set.range (rootProduct (V2InteriorFactors Q split)) =
    (linearInterior Q split c : Set (X ⧸ Q.D)) := by
  apply Set.Subset.antisymm
  · rintro x ⟨p,rfl⟩
    exact rootProduct_mem _ _ (interiorFactors_le Q split c) _
  · intro x hx
    have hp := hx.1.1
    change x ∈ (simpleRemainder Q split 0 : Set (X ⧸ Q.D)) at hp
    rw [←linearProduct_range Q split c] at hp
    obtain ⟨⟨b,d,e,f,g,h,k,t⟩,hp⟩ := hp
    let z := rootProduct (V2InteriorFactors Q split) (d,e,f,g,h,t)
    have hz : z ∈ linearInterior Q split c :=
      rootProduct_mem _ _ (interiorFactors_le Q split c) _
    have hp : (b : X ⧸ Q.D)*z*k = x := by
      simpa only [z,linearFactors,V2InteriorFactors,rootProduct,mul_one,mul_assoc] using hp
    have hbV := positiveRoot_le_remainder Q split c (.inr 2) 1 (by decide) b.property
    have hkV : (k : X ⧸ Q.D) ∈ simpleRemainder Q split 1 := by
      have hh := (simpleRemainder Q split 1).mul_mem
        ((simpleRemainder Q split 1).inv_mem
          ((simpleRemainder Q split 1).mul_mem hbV hz.1.2)) hx.1.2
      rw [←hp,inv_mul_cancel_left] at hh
      exact hh
    have hk : (k : X ⧸ Q.D) = 1 := disjoint_def.mp
      (simpleRoot_disjoint_remainder Q split 1)
      (by simpa [positiveRoot,positiveKind,positiveWord] using k.property) hkV
    rw [hk,mul_one] at hp
    let R := rightConjugate (simpleRemainder Q split 1) ((c.reflections 0).val : X ⧸ Q.D)
    have hbR : (b : X ⧸ Q.D) ∈ R := by
      have hh := R.mul_mem hx.2 (R.inv_mem hz.2)
      rw [←hp,mul_inv_cancel_right] at hh
      exact hh
    have hb : (b : X ⧸ Q.D) = 1 := by
      apply (MulAut.conj ((c.reflections 0).val : X ⧸ Q.D)).injective
      have hroot : positiveRoot Q split (.inr 2) =
          rightConjugate (simpleRoot Q split 1) ((c.reflections 0).val : X ⧸ Q.D) :=
        rootAt_eq Q split 1 _ _ (c.reflections 0).class_eq
      exact (disjoint_def.mp (simpleRoot_disjoint_remainder Q split 1)
        (hroot.le b.property) hbR).trans (map_one _).symm
    exact ⟨(d,e,f,g,h,t),by simpa only [hb,one_mul] using hp⟩

include c in
theorem T1_eq_linearInterior : T1 Q split = linearInterior Q split c := by
  apply le_antisymm
  · apply sup_le (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) ?_
    all_goals apply interiorFactors_le Q split c
    all_goals simp [V2InteriorFactors]
  · intro x hx
    change x ∈ (linearInterior Q split c : Set (X ⧸ Q.D)) at hx
    rw [←interiorProduct_range Q split c] at hx
    obtain ⟨p,rfl⟩ := hx
    apply rootProduct_mem
    intro A hA
    simp only [V2InteriorFactors,List.mem_cons,List.not_mem_nil,or_false] at hA
    rcases hA with rfl | rfl | rfl | rfl | rfl
    · exact le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))
    · exact le_sup_right.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))
    · exact le_sup_right.trans (le_sup_left.trans le_sup_left)
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right

include c in
theorem T1_product : (T1 Q split : Set (X ⧸ Q.D)) =
    (positiveRoot Q split (.inl 2) : Set (X ⧸ Q.D)) *
    (positiveRoot Q split (.inr 1) : Set (X ⧸ Q.D)) *
    (positiveRoot Q split (.inl 3) : Set (X ⧸ Q.D)) *
    (positiveRoot Q split (.inr 3) : Set (X ⧸ Q.D)) *
    (positiveRoot Q split (.inl 1) : Set (X ⧸ Q.D)) := by
  rw [T1_eq_linearInterior Q split c,←interiorProduct_range Q split c,rootProduct_range]
  change (positiveRoot Q split (.inl 2) : Set (X ⧸ Q.D)) *
    ((positiveRoot Q split (.inr 1) : Set (X ⧸ Q.D)) *
    ((positiveRoot Q split (.inl 3) : Set (X ⧸ Q.D)) *
    ((positiveRoot Q split (.inr 3) : Set (X ⧸ Q.D)) *
    ((positiveRoot Q split (.inl 1) : Set (X ⧸ Q.D)) * 1)))) = _
  simp only [mul_one,mul_assoc]

include c in
theorem T1_le_linearRemainder : T1 Q split ≤ simpleRemainder Q split 0 := by
  rw [T1_eq_linearInterior Q split c]
  exact inf_le_left.trans inf_le_left

include c in
theorem linearRemainder_normalizes_T1 :
    simpleRemainder Q split 0 ≤ normalizer (T1 Q split : Set (X ⧸ Q.D)) := by
  have hN : split.U ≤ normalizer (simpleRemainder Q split 1 : Set (X ⧸ Q.D)) :=
    split.U_le.trans ((Q.tits.B_le_standardParabolic _).trans
      (remainder_parabolic_normalizes Q split 1 (remainder_le_kernel Q split c)))
  have hR : simpleRemainder Q split 0 ≤ normalizer
      (rightConjugate (simpleRemainder Q split 1) ((c.reflections 0).val : X ⧸ Q.D) : Set (X ⧸ Q.D)) := by
    have hc := (comap_mono hN (f :=
      (MulAut.conj ((c.reflections 0).val : X ⧸ Q.D)).toMonoidHom)).trans
        (le_normalizer_comap _)
    apply le_trans _ hc
    change simpleRemainder Q split 0 ≤ rightConjugate split.U ((c.reflections 0).val : X ⧸ Q.D)
    rw [←unipotentConjugate_eq split _ _ (c.reflections 0).class_eq]
    exact inf_le_right
  rw [T1_eq_linearInterior Q split c]
  exact (le_inf ((le_inf (simpleRemainder Q split 0).le_normalizer
    (inf_le_left.trans hN)).trans inf_normalizer_le_normalizer_inf) hR).trans
      inf_normalizer_le_normalizer_inf

include c in
theorem linearInteriorNormal :
    ((T1 Q split).subgroupOf (simpleRemainder Q split 0)).Normal :=
  normal_subgroupOf_of_le_normalizer (linearRemainder_normalizes_T1 Q split c)

instance linearInterior_normal :
    ((linearInterior Q split c).subgroupOf (simpleRemainder Q split 0)).Normal := by
  rw [←T1_eq_linearInterior Q split c]
  exact linearInteriorNormal Q split c

/-- The actual quotient by the five-root interior. -/
abbrev LinearEdgeQuotient :=
  simpleRemainder Q split 0 ⧸ (linearInterior Q split c).subgroupOf (simpleRemainder Q split 0)

private def edgeLeft : positiveRoot Q split (.inr 2) →* LinearEdgeQuotient Q split c :=
  (QuotientGroup.mk' _).comp (inclusion
    (positiveRoot_le_remainder Q split c (.inr 2) 0 (by decide)))

private def edgeRight : positiveRoot Q split (.inr 0) →* LinearEdgeQuotient Q split c :=
  (QuotientGroup.mk' _).comp (inclusion
    (positiveRoot_le_remainder Q split c (.inr 0) 0 (by decide)))

open scoped commutatorElement
private theorem edge_commute (a : positiveRoot Q split (.inr 2))
    (b : positiveRoot Q split (.inr 0)) :
    Commute (edgeLeft Q split c a) (edgeRight Q split c b) := by
  apply commutatorElement_eq_one_iff_commute.mp
  change ⁅QuotientGroup.mk' _ _,QuotientGroup.mk' _ _⁆ = 1
  rw [←map_commutatorElement]
  apply (QuotientGroup.eq_one_iff _).mpr
  have hb : (b : X ⧸ Q.D) ∈ simpleRoot Q split 1 := by
    simpa [positiveRoot,positiveKind,positiveWord] using b.property
  have hx : ⁅(a : X ⧸ Q.D),(b : X ⧸ Q.D)⁆ ∈
      ⁅simpleRoot Q split 1,positiveRoot Q split (.inr 2)⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator a.property hb
  have hi := V2_cross_commutator_support Q split c _ hx
  rw [interiorProduct_range Q split c] at hi
  exact hi

/-- Multiplication of the two endpoint roots, modulo the actual interior. -/
def linearEdgeMap :
    (positiveRoot Q split (.inr 2) × positiveRoot Q split (.inr 0)) →*
      LinearEdgeQuotient Q split c where
  toFun p := QuotientGroup.mk' _
    (inclusion (positiveRoot_le_remainder Q split c (.inr 2) 0 (by decide)) p.1) *
      QuotientGroup.mk' _
        (inclusion (positiveRoot_le_remainder Q split c (.inr 0) 0 (by decide)) p.2)
  map_one' := by simp only [Prod.fst_one,Prod.snd_one,map_one,mul_one]
  map_mul' p q := by
    change edgeLeft Q split c (p.1*q.1)*edgeRight Q split c (p.2*q.2) = _
    change edgeLeft Q split c (p.1*q.1)*edgeRight Q split c (p.2*q.2) =
      (edgeLeft Q split c p.1 * edgeRight Q split c p.2) *
        (edgeLeft Q split c q.1 * edgeRight Q split c q.2)
    rw [map_mul,map_mul]
    exact (edge_commute Q split c q.1 p.2).mul_mul_mul_comm _ _

include c in
theorem linearEdgeMap_bijective : Function.Bijective (linearEdgeMap Q split c) := by
  constructor
  · apply (injective_iff_map_eq_one (linearEdgeMap Q split c)).mpr
    rintro ⟨a,b⟩ hab
    have hx : (a : X ⧸ Q.D)*b ∈ linearInterior Q split c := by
      change QuotientGroup.mk' ((linearInterior Q split c).subgroupOf (simpleRemainder Q split 0)) _ * QuotientGroup.mk' ((linearInterior Q split c).subgroupOf (simpleRemainder Q split 0)) _ = 1 at hab
      rw [←map_mul] at hab
      exact (QuotientGroup.eq_one_iff (N := (linearInterior Q split c).subgroupOf (simpleRemainder Q split 0)) _).mp hab
    change (a : X ⧸ Q.D)*b ∈ (linearInterior Q split c : Set (X ⧸ Q.D)) at hx
    rw [←interiorProduct_range Q split c] at hx
    obtain ⟨⟨d,e,f,g,h,t⟩,hp⟩ := hx
    have he := linearProduct_injective Q split c
      (a₁ := (a,1,1,1,1,1,b,t)) (a₂ := (1,d,e,f,g,h,1,t)) (by
        simpa only [linearFactors,V2InteriorFactors,rootProduct,OneMemClass.coe_one,
          one_mul,mul_one,mul_assoc] using hp.symm)
    have ha : a = 1 := congrArg Prod.fst he
    have hb : b = 1 := congrArg (fun z => z.2.2.2.2.2.2.1) he
    exact Prod.ext ha hb
  · intro z
    induction z using QuotientGroup.induction_on with | H x =>
      have hx := x.property
      change (x : X ⧸ Q.D) ∈ (simpleRemainder Q split 0 : Set (X ⧸ Q.D)) at hx
      rw [←linearProduct_range Q split c] at hx
      obtain ⟨⟨a,d,e,f,g,h,b,t⟩,hp⟩ := hx
      let y := rootProduct (V2InteriorFactors Q split) (d,e,f,g,h,t)
      have hy : y ∈ T1 Q split := by
        rw [T1_eq_linearInterior Q split c]
        exact rootProduct_mem _ _ (interiorFactors_le Q split c) _
      let y' : simpleRemainder Q split 0 := ⟨y,T1_le_linearRemainder Q split c hy⟩
      let a' := inclusion (positiveRoot_le_remainder Q split c (.inr 2) 0 (by decide)) a
      let b' := inclusion (positiveRoot_le_remainder Q split c (.inr 0) 0 (by decide)) b
      have he : a'*y'*b' = x := Subtype.ext (by
        simpa only [a',y',b',y,Subgroup.coe_mul,Subgroup.coe_inclusion,linearFactors,V2InteriorFactors,
          rootProduct,mul_one,mul_assoc] using hp)
      refine ⟨(a,b),?_⟩
      change QuotientGroup.mk' ((linearInterior Q split c).subgroupOf (simpleRemainder Q split 0)) a' * QuotientGroup.mk' ((linearInterior Q split c).subgroupOf (simpleRemainder Q split 0)) b' = QuotientGroup.mk' ((linearInterior Q split c).subgroupOf (simpleRemainder Q split 0)) x
      rw [←he,map_mul,map_mul]
      have hq : QuotientGroup.mk' ((linearInterior Q split c).subgroupOf (simpleRemainder Q split 0)) y' = 1 :=
        (QuotientGroup.eq_one_iff _).mpr ((T1_eq_linearInterior Q split c).le hy)
      rw [hq,mul_one]

/-- The quotient by T₁ is the direct product of the two literal Suzuki roots. -/
def linearEdgeEquiv :
    (positiveRoot Q split (.inr 2) × positiveRoot Q split (.inr 0)) ≃*
      LinearEdgeQuotient Q split c :=
  MulEquiv.ofBijective (linearEdgeMap Q split c) (linearEdgeMap_bijective Q split c)

open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII

/-- First-coordinate homomorphism of a literal positive Suzuki root. -/
def positiveSuzukiBar (j : Fin 4) : positiveRoot Q split (.inr j) →*
    Multiplicative (BinaryGaloisField (2*m+1)) :=
  (suzukiFirstCoordinate Q split 1 m c.suzuki c.suzukiBorel).comp
    (RootAction.conjugateEquiv (simpleRoot Q split 1)
      (representative (positiveWord (Q.simple 0) (Q.simple 1) (.inr j)) : X ⧸ Q.D)).toMonoidHom

include c in
theorem positiveSuzukiBar_surjective (j : Fin 4) :
    Function.Surjective (positiveSuzukiBar Q split c j) :=
  (suzukiFirstCoordinate_surjective Q split 1 m c.suzuki c.suzukiBorel).comp
    (MulEquiv.surjective _)

include c in
theorem positiveSuzukiBar_eq_one (j : Fin 4) (x : positiveRoot Q split (.inr j)) :
    positiveSuzukiBar Q split c j x = 1 ↔
      (x : X ⧸ Q.D) ∈ omegaOneAmbient (positiveRoot Q split (.inr j)) := by
  let e := MulAut.conj (representative (positiveWord (Q.simple 0) (Q.simple 1) (.inr j)) : X ⧸ Q.D)
  have he : (positiveRoot Q split (.inr j)).map e.toMonoidHom = simpleRoot Q split 1 :=
    map_comap_eq_self_of_surjective e.surjective _
  have ho : (omegaOneAmbient (positiveRoot Q split (.inr j))).map e.toMonoidHom =
      omegaOneAmbient (simpleRoot Q split 1) := by
    rw [map_omegaOneAmbient_injective e.toMonoidHom e.injective,he]
  change (suzukiFirstCoordinate Q split 1 m c.suzuki c.suzukiBorel)
    ((RootAction.conjugateEquiv (simpleRoot Q split 1) _) x) = 1 ↔ _
  rw [←MonoidHom.mem_ker,suzukiFirstCoordinate_kernel Q split 1 m c.suzuki c.suzukiBorel]
  change e (x : X ⧸ Q.D) ∈ omegaOneAmbient (simpleRoot Q split 1) ↔ _
  rw [←ho,mem_map_equiv,MulEquiv.symm_apply_apply]

include c in
theorem positiveSuzuki_phi_eq_omega (j : Fin 4) :
    phi (positiveRoot Q split (.inr j)) = omegaOneAmbient (positiveRoot Q split (.inr j)) := by
  let e := MulAut.conj (representative (positiveWord (Q.simple 0) (Q.simple 1) (.inr j)) : X ⧸ Q.D)
  let r : positiveRoot Q split (.inr j) ≃* simpleRoot Q split 1 :=
    RootAction.conjugateEquiv (simpleRoot Q split 1)
    (representative (positiveWord (Q.simple 0) (Q.simple 1) (.inr j)) : X ⧸ Q.D)
  have he : (positiveRoot Q split (.inr j)).map e.toMonoidHom = simpleRoot Q split 1 :=
    map_comap_eq_self_of_surjective e.surjective _
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [map_omegaOneAmbient_injective e.toMonoidHom e.injective,he]
  change ((frattini (positiveRoot Q split (.inr j))).map
    (positiveRoot Q split (.inr j)).subtype).map e.toMonoidHom = _
  rw [map_map]
  have hc : e.toMonoidHom.comp (positiveRoot Q split (.inr j)).subtype =
      (simpleRoot Q split 1).subtype.comp r.toMonoidHom := rfl
  rw [hc,←map_map,frattini_map_equiv r]
  exact suzuki_frattini_image Q split 1 m c.suzuki c.suzukiBorel

/-- The endpoint coordinates in the actual quotient by T₁. -/
def linearBoundary : simpleRemainder Q split 0 →*
    (positiveRoot Q split (.inr 2) × positiveRoot Q split (.inr 0)) :=
  (linearEdgeEquiv Q split c).symm.toMonoidHom.comp (QuotientGroup.mk' _)

include c in
theorem linearBoundary_product (a : positiveRoot Q split (.inr 2))
    (t : T1 Q split) (b : positiveRoot Q split (.inr 0)) :
    linearBoundary Q split c
      (inclusion (positiveRoot_le_remainder Q split c (.inr 2) 0 (by decide)) a *
       inclusion (T1_le_linearRemainder Q split c) t *
       inclusion (positiveRoot_le_remainder Q split c (.inr 0) 0 (by decide)) b) = (a,b) := by
  apply (linearEdgeEquiv Q split c).injective
  change linearEdgeEquiv Q split c ((linearEdgeEquiv Q split c).symm _) = _
  rw [MulEquiv.apply_symm_apply]
  change QuotientGroup.mk' ((linearInterior Q split c).subgroupOf (simpleRemainder Q split 0)) _ = _
  rw [map_mul,map_mul]
  have ht : QuotientGroup.mk' ((linearInterior Q split c).subgroupOf (simpleRemainder Q split 0))
      (inclusion (T1_le_linearRemainder Q split c) t) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ((T1_eq_linearInterior Q split c).le t.property)
  rw [ht,mul_one]
  rfl

include c in
theorem linearBoundary_surjective : Function.Surjective (linearBoundary Q split c) :=
  (linearEdgeEquiv Q split c).symm.surjective.comp (QuotientGroup.mk'_surjective _)

/-- The literal denominator in Fong--Seitz II, p.222. Its characteristic
property is proved separately, with the binary alternatives retained. -/
def X1 : Subgroup (X ⧸ Q.D) :=
  omegaOneAmbient (positiveRoot Q split (.inr 2)) ⊔ T1 Q split ⊔
    omegaOneAmbient (positiveRoot Q split (.inr 0))

include c in
theorem X1_le_linearRemainder : X1 Q split ≤ simpleRemainder Q split 0 :=
  sup_le (sup_le ((omegaOneAmbient_le _).trans
    (positiveRoot_le_remainder Q split c (.inr 2) 0 (by decide)))
      (T1_le_linearRemainder Q split c)) ((omegaOneAmbient_le _).trans
        (positiveRoot_le_remainder Q split c (.inr 0) 0 (by decide)))

/-- Both barred endpoint coordinates, on the literal linear radical. -/
def linearBarBoundary : simpleRemainder Q split 0 →*
    (Multiplicative (BinaryGaloisField (2*m+1)) ×
     Multiplicative (BinaryGaloisField (2*m+1))) :=
  ((positiveSuzukiBar Q split c 2).prodMap (positiveSuzukiBar Q split c 0)).comp
    (linearBoundary Q split c)

include c in
theorem linearBarBoundary_surjective : Function.Surjective (linearBarBoundary Q split c) := by
  intro p
  obtain ⟨a,ha⟩ := positiveSuzukiBar_surjective Q split c 2 p.1
  obtain ⟨b,hb⟩ := positiveSuzukiBar_surjective Q split c 0 p.2
  obtain ⟨x,hx⟩ := linearBoundary_surjective Q split c (a,b)
  refine ⟨x,?_⟩
  change Prod.map (positiveSuzukiBar Q split c 2) (positiveSuzukiBar Q split c 0) (linearBoundary Q split c x) = p
  rw [hx]
  exact Prod.ext ha hb

include c in
theorem linearBarBoundary_kernel : (linearBarBoundary Q split c).ker =
    (X1 Q split).subgroupOf (simpleRemainder Q split 0) := by
  let K := ((linearBarBoundary Q split c).ker).map (simpleRemainder Q split 0).subtype
  have hX : X1 Q split ≤ K := by
    apply sup_le (sup_le ?_ ?_) ?_
    · intro x hx
      let a : positiveRoot Q split (.inr 2) := ⟨x,omegaOneAmbient_le _ hx⟩
      let u := inclusion (positiveRoot_le_remainder Q split c (.inr 2) 0 (by decide)) a
      refine ⟨u,?_,rfl⟩
      have he := linearBoundary_product Q split c a 1 1
      simp only [map_one,mul_one] at he
      change Prod.map (positiveSuzukiBar Q split c 2) (positiveSuzukiBar Q split c 0) (linearBoundary Q split c u) = (1,1)
      rw [he]
      exact Prod.ext ((positiveSuzukiBar_eq_one Q split c 2 a).mpr hx) (map_one _)
    · intro x hx
      let t : T1 Q split := ⟨x,hx⟩
      let u := inclusion (T1_le_linearRemainder Q split c) t
      refine ⟨u,?_,rfl⟩
      have he := linearBoundary_product Q split c 1 t 1
      simp only [map_one,mul_one,one_mul] at he
      change Prod.map (positiveSuzukiBar Q split c 2) (positiveSuzukiBar Q split c 0) (linearBoundary Q split c u) = (1,1)
      rw [he]
      exact Prod.ext (map_one _) (map_one _)
    · intro x hx
      let b : positiveRoot Q split (.inr 0) := ⟨x,omegaOneAmbient_le _ hx⟩
      let u := inclusion (positiveRoot_le_remainder Q split c (.inr 0) 0 (by decide)) b
      refine ⟨u,?_,rfl⟩
      have he := linearBoundary_product Q split c 1 1 b
      simp only [map_one,one_mul] at he
      change Prod.map (positiveSuzukiBar Q split c 2) (positiveSuzukiBar Q split c 0) (linearBoundary Q split c u) = (1,1)
      rw [he]
      exact Prod.ext (map_one _) ((positiveSuzukiBar_eq_one Q split c 0 b).mpr hx)
  apply le_antisymm
  · intro x hx
    have hp := x.property
    change (x : X ⧸ Q.D) ∈ (simpleRemainder Q split 0 : Set (X ⧸ Q.D)) at hp
    rw [←linearProduct_range Q split c] at hp
    obtain ⟨⟨a,d,e,f,g,h,b,t⟩,hp⟩ := hp
    let y := rootProduct (V2InteriorFactors Q split) (d,e,f,g,h,t)
    have hy : y ∈ T1 Q split := by
      rw [T1_eq_linearInterior Q split c]
      exact rootProduct_mem _ _ (interiorFactors_le Q split c) _
    have he : inclusion (positiveRoot_le_remainder Q split c (.inr 2) 0 (by decide)) a *
        inclusion (T1_le_linearRemainder Q split c) ⟨y,hy⟩ *
        inclusion (positiveRoot_le_remainder Q split c (.inr 0) 0 (by decide)) b = x := by
      apply Subtype.ext
      simpa only [Subgroup.coe_mul,Subgroup.coe_inclusion,y,linearFactors,V2InteriorFactors,
        rootProduct,mul_one,mul_assoc] using hp
    have hbdy := linearBoundary_product Q split c a ⟨y,hy⟩ b
    rw [he] at hbdy
    change Prod.map (positiveSuzukiBar Q split c 2) (positiveSuzukiBar Q split c 0) (linearBoundary Q split c x) = (1,1) at hx
    rw [hbdy] at hx
    have haΩ := (positiveSuzukiBar_eq_one Q split c 2 a).mp (congrArg Prod.fst hx)
    have hbΩ := (positiveSuzukiBar_eq_one Q split c 0 b).mp (congrArg Prod.snd hx)
    change (x : X ⧸ Q.D) ∈ X1 Q split
    rw [←he]
    exact (X1 Q split).mul_mem
      ((X1 Q split).mul_mem ((show omegaOneAmbient (positiveRoot Q split (.inr 2)) ≤ X1 Q split from le_sup_left.trans le_sup_left) haΩ)
        ((show T1 Q split ≤ X1 Q split from le_sup_right.trans le_sup_left) hy)) ((show omegaOneAmbient (positiveRoot Q split (.inr 0)) ≤ X1 Q split from le_sup_right) hbΩ)
  · intro x hx
    exact (mem_map_iff_mem (simpleRemainder Q split 0).subtype_injective).mp (hX hx)

include c in
theorem linearPhi_le_X1 : phi (simpleRemainder Q split 0) ≤ X1 Q split := by
  have hf := Theory.GroupTheory.frattini_le_ker_of_square_image (linearBarBoundary Q split c)
    (fun x => by
      apply Prod.ext
      all_goals change 2 • _ = (0 : BinaryGaloisField (2*m+1))
      all_goals exact (two_nsmul _).trans (CharTwo.add_self_eq_zero _))
  rw [linearBarBoundary_kernel Q split c] at hf
  exact map_le_iff_le_comap.mpr hf

include c in
theorem linearDerived_le_X1 : linearDerived Q split ≤ X1 Q split := by
  let : Fact (IsPGroup 2 (simpleRemainder Q split 0)) :=
    ⟨split.isTwo.to_le inf_le_left⟩
  apply le_trans _ (linearPhi_le_X1 Q split c)
  rw [linearDerived,←map_subtype_commutator]
  exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))

include c in
theorem X1_eq_linearPhi_of_T1_le_derived (hT : T1 Q split ≤ linearDerived Q split) :
    X1 Q split = phi (simpleRemainder Q split 0) := by
  let : Fact (IsPGroup 2 (simpleRemainder Q split 0)) :=
    ⟨split.isTwo.to_le inf_le_left⟩
  have ho (j : Fin 4) :
      omegaOneAmbient (positiveRoot Q split (.inr j)) ≤ phi (simpleRemainder Q split 0) := by
    let i := inclusion (positiveRoot_le_remainder Q split c (.inr j) 0 (by simp))
    let : Fact (IsPGroup 2 (positiveRoot Q split (.inr j))) :=
      ⟨split.isTwo.to_le (positiveRoot_le_unipotent Q split c.rotation_eight _)⟩
    rw [←positiveSuzuki_phi_eq_omega Q split c j]
    have hh := map_mono (f := (simpleRemainder Q split 0).subtype)
      (frattini_map_le_of_isPGroup (p := 2) i)
    rw [map_map] at hh
    exact hh
  apply le_antisymm _ (linearPhi_le_X1 Q split c)
  apply sup_le (sup_le (ho 2) ?_) (ho 0)
  apply hT.trans
  rw [linearDerived,←map_subtype_commutator]
  exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))

include c in
theorem linearX1Normal : ((X1 Q split).subgroupOf (simpleRemainder Q split 0)).Normal := by
  rw [←linearBarBoundary_kernel Q split c]
  infer_instance

include c in
/-- The literal quotient has order q², including q=2. -/
theorem X1_quotient_card :
    Nat.card (simpleRemainder Q split 0 ⧸ (X1 Q split).subgroupOf (simpleRemainder Q split 0)) =
      (2^(2*m+1))^2 := by
  rw [←linearBarBoundary_kernel Q split c,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
      (linearBarBoundary Q split c) (linearBarBoundary_surjective Q split c)).toEquiv,
    Nat.card_prod]
  have hf : Nat.card (Multiplicative (BinaryGaloisField (2*m+1))) = 2^(2*m+1) :=
    (Nat.card_congr Multiplicative.toAdd).trans (GaloisField.card 2 (2*m+1) (by omega))
  rw [hf,pow_two]

include c in
/-- Characteristicity follows from the actual Frattini identification in
any branch supplying the whole five-root derived containment. -/
theorem X1_characteristic_of_T1_le_derived (hT : T1 Q split ≤ linearDerived Q split) :
    ((X1 Q split).subgroupOf (simpleRemainder Q split 0)).Characteristic := by
  rw [X1_eq_linearPhi_of_T1_le_derived Q split c hT]
  have he : (phi (simpleRemainder Q split 0)).subgroupOf (simpleRemainder Q split 0) =
      frattini (simpleRemainder Q split 0) := by
    apply Subgroup.ext
    intro x
    exact mem_map_iff_mem (simpleRemainder Q split 0).subtype_injective
  rw [he]
  infer_instance

include c in
/-- The printed denominator is an ordered product, not just its generated
subgroup. The proof retains the two endpoint Omega conditions. -/
theorem X1_product : (X1 Q split : Set (X ⧸ Q.D)) =
    (omegaOneAmbient (positiveRoot Q split (.inr 2)) : Set (X ⧸ Q.D)) *
    (T1 Q split : Set (X ⧸ Q.D)) *
    (omegaOneAmbient (positiveRoot Q split (.inr 0)) : Set (X ⧸ Q.D)) := by
  apply Set.Subset.antisymm
  · intro x hx
    let v : simpleRemainder Q split 0 := ⟨x,X1_le_linearRemainder Q split c hx⟩
    have hv : linearBarBoundary Q split c v = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [linearBarBoundary_kernel Q split c]
      exact hx
    have hp : x ∈ (simpleRemainder Q split 0 : Set (X ⧸ Q.D)) := v.property
    rw [←linearProduct_range Q split c] at hp
    obtain ⟨⟨a,d,e,f,g,h,b,t⟩,hp⟩ := hp
    let y := rootProduct (V2InteriorFactors Q split) (d,e,f,g,h,t)
    have hy : y ∈ T1 Q split := by
      rw [T1_eq_linearInterior Q split c]
      exact rootProduct_mem _ _ (interiorFactors_le Q split c) _
    have he : inclusion (positiveRoot_le_remainder Q split c (.inr 2) 0 (by decide)) a *
        inclusion (T1_le_linearRemainder Q split c) ⟨y,hy⟩ *
        inclusion (positiveRoot_le_remainder Q split c (.inr 0) 0 (by decide)) b = v := by
      apply Subtype.ext
      simpa only [Subgroup.coe_mul,Subgroup.coe_inclusion,y,linearFactors,V2InteriorFactors,
        rootProduct,mul_one,mul_assoc] using hp
    have hbdy := linearBoundary_product Q split c a ⟨y,hy⟩ b
    rw [he] at hbdy
    change Prod.map (positiveSuzukiBar Q split c 2) (positiveSuzukiBar Q split c 0) (linearBoundary Q split c v) = (1,1) at hv
    rw [hbdy] at hv
    refine ⟨(a : X ⧸ Q.D)*y,⟨a,
      (positiveSuzukiBar_eq_one Q split c 2 a).mp (congrArg Prod.fst hv),y,hy,rfl⟩,
      b,(positiveSuzukiBar_eq_one Q split c 0 b).mp (congrArg Prod.snd hv),?_⟩
    exact congrArg Subtype.val he
  · rintro x ⟨z,⟨a,ha,t,ht,rfl⟩,b,hb,rfl⟩
    exact (X1 Q split).mul_mem
      ((X1 Q split).mul_mem ((show omegaOneAmbient (positiveRoot Q split (.inr 2)) ≤ X1 Q split from le_sup_left.trans le_sup_left) ha)
        ((show T1 Q split ≤ X1 Q split from le_sup_right.trans le_sup_left) ht)) ((show omegaOneAmbient (positiveRoot Q split (.inr 0)) ≤ X1 Q split from le_sup_right) hb)

end Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
