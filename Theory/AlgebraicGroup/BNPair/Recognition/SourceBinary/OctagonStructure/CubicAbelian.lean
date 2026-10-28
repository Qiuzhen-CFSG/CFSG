module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicRadicalCentralizers
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.FiveRootIntervals
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SmallSections

/-!
# Abelian cubic centralizers and perpendicular rank-one groups

Suppose a Cartan element fixes one whole octagon root family and is
fixed-point-free on the other. Its centralizer in the first panel radical
is the actual product of three roots. Short root intervals make the middle
root central in this product and put its derived subgroup in that root.
If the derived subgroup were nontrivial, Cartan irreducibility would make
it the entire middle root. The first rank-one group normalizes this derived
subgroup and centralizes it by the minimum binary degree bound. Reflection
then kills the remaining commutator, a contradiction. A root of order two
uses its trivial automorphism group, so no perfectness assumption is needed.

The perpendicular root commutator consequently vanishes. Weyl transport
extends this to commutation of both entire perpendicular rank-one groups.
The source adapter constructs the separating cubic element and all local
linear markings from the same original F.1.1 pair and full amalgam map.

Source: Fong--Seitz, Groups with a (B,N)-pair of rank 2, I (1973), (6G),
printed p.49, the paragraph beginning “Now C(T)”. This proves that structural
step; the later kernel separation and terminal octagon exclusion remain.
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
  simp only [rightConjugate, comap_equiv_eq_map_symm', map_commutator]
private theorem right_bot (w : Weyl Q) :
    rightConjugate (⊥ : Subgroup (X ⧸ Q.D)) (representative w : X ⧸ Q.D) = ⊥ := by
  simp only [rightConjugate, comap_equiv_eq_map_symm', Subgroup.map_bot]

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

/-- The cubic centralizer is the literal three-root product in either orientation. -/
theorem separated_radical_centralizer_product (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)))
    (hc : ∀ w : Weyl Q,
      (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) ∧
      rootAt Q split j w ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥) :
    (simpleRemainder Q split i ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) :
        Set (X ⧸ Q.D)) =
      (rootAt Q split i (Q.simple j) : Set (X ⧸ Q.D)) *
      (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) : Set (X ⧸ Q.D)) *
      (rootAt Q split i (Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) := by
  obtain ⟨b,hb,hV⟩ := seven_list Q split hm i j hij
  have hfix (w : Weyl Q) : rootAt Q split i w ⊓
      centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = rootAt Q split i w :=
    inf_eq_left.mpr (fun _ hx => mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp (hc w).1 _ hx))
  have hzero : simpleRoot Q split j ⊓
      centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥ := by
    simpa only [rootAt_one] using (hc 1).2
  have he := ordered_root_product_conj_fixed Q split b 7 (by omega) c
  rw [rootProduct_range,orderedRoots_product Q split b 7 (by omega),hV,hb] at he
  simp only [List.map_cons,List.map_nil,hfix,hzero,(hc _).2] at he
  change (simpleRemainder Q split i : Set (X ⧸ Q.D)) ∩
      (centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) : Set (X ⧸ Q.D)) =
      ([⊥,rootAt Q split i (Q.simple j),⊥,
        rootAt Q split i (Q.simple j*Q.simple i*Q.simple j),⊥,
        rootAt Q split i (Q.simple j*Q.simple i),⊥].map
          (fun A : Subgroup (X ⧸ Q.D) => (A : Set (X ⧸ Q.D)))).prod at he
  simpa only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    coe_bot,Set.singleton_one,one_mul,mul_one,mul_assoc,Set.inf_eq_inter] using he

/-- The separating actor centralizes the full odd-family rank-one group. -/
theorem separated_rankOne_centralized
    (i : Fin 2) (c : X ⧸ Q.D)
    (hc : ∀ w : Weyl Q, c ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D))) :
    rankOne Q split i ≤ centralizer ({c} : Set (X ⧸ Q.D)) := by
  apply sup_le
  · intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp (by simpa only [rootAt_one] using hc 1) x hx)
  · intro x hx
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hc (Q.simple i)) x hx)

/-- Consequently the same rank-one group normalizes the radical centralizer. -/
theorem separated_radical_centralizer_normalized
    (i : Fin 2) (hK : simpleRemainder Q split i ≤ localKernel Q i)
    (c : X ⧸ Q.D)
    (hc : ∀ w : Weyl Q, c ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D))) :
    rankOne Q split i ≤ normalizer
      ((simpleRemainder Q split i ⊓ centralizer ({c} : Set (X ⧸ Q.D)) :
        Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) := by
  apply (le_inf ((rankOne_le_parabolic Q split i).trans
    (remainder_parabolic_normalizes Q split i hK)) ?_).trans
      inf_normalizer_le_normalizer_inf
  exact (separated_rankOne_centralized Q split i c hc).trans
    (centralizer ({c} : Set (X ⧸ Q.D))).le_normalizer

/-- The intervening root is fixed-point-free, so the nearby fixed roots commute. -/
theorem separated_distance_two_commutator (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hK : simpleRemainder Q split i ≤ localKernel Q i)
    (c : X ⧸ Q.D)
    (hc : ∀ w : Weyl Q,
      c ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) ∧
      rootAt Q split j w ⊓ centralizer ({c} : Set (X ⧸ Q.D)) = ⊥) :
    ⁅simpleRoot Q split i, rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥ := by
  apply bot_unique
  apply (le_inf (distance_two_commutator_le Q split hm i j hij hK) ?_).trans
    ((hc (Q.simple i)).2.le)
  apply (commutator_mono ?_ ?_).trans (commutator_le_self _)
  · intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp (by simpa only [rootAt_one] using (hc 1).1) x hx)
  · intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp (hc (Q.simple j*Q.simple i)).1 x hx)


private theorem inner_three_injective (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) :
    Function.Injective (fun p : rootAt Q split j (Q.simple i) ×
      rootAt Q split i (Q.simple j*Q.simple i) ×
      rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) =>
      (p.1 : X ⧸ Q.D)*(p.2.1 : X ⧸ Q.D)*(p.2.2 : X ⧸ Q.D)) := by
  obtain ⟨b,hb,_⟩ := seven_list Q split hm j i hij.symm
  have hinj : Function.Injective (rootProduct (orderedRoots Q split b 7)) := by
    intro p q he
    apply (orderedCoordinates Q split b 7 (by omega)).injective
    apply Subtype.ext
    simpa only [orderedCoordinates_apply] using he
  rw [hb] at hinj
  intro p q he
  have hh := hinj (a₁ := (1,p.1,p.2.1,p.2.2,1,1,1,PUnit.unit))
    (a₂ := (1,q.1,q.2.1,q.2.2,1,1,1,PUnit.unit)) (by
      simpa only [rootProduct, OneMemClass.coe_one, one_mul, mul_one, mul_assoc] using he)
  exact Prod.ext (congrArg (fun z => z.2.1) hh)
    (Prod.ext (congrArg (fun z => z.2.2.1) hh) (congrArg (fun z => z.2.2.2.1) hh))

/-- Fixed coordinates remove the two moving roots from the perpendicular commutator. -/
theorem separated_perpendicular_commutator_le (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hK : simpleRemainder Q split i ≤ localKernel Q i)
    (c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)))
    (hc : ∀ w : Weyl Q,
      (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) ∧
      rootAt Q split j w ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥) :
    ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ ≤
      rootAt Q split i (Q.simple j*Q.simple i) := by
  let B := rootAt Q split j (Q.simple i)
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let D := rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)
  have hcent : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ ≤
      centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) := by
    apply (commutator_mono ?_ ?_).trans (commutator_le_self _)
    · intro x hx
      exact mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp (by simpa only [rootAt_one] using (hc 1).1) x hx)
    · intro x hx
      exact mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp (hc (Q.simple j*Q.simple i*Q.simple j)).1 x hx)
  intro x hx
  obtain ⟨bc,⟨b,hb,z,hz,rfl⟩,d,hd,he⟩ :=
    distance_four_commutator_support Q split hm i j hij hK x hx
  change b*z*d = x at he
  let p : B × C × D := (⟨b,hb⟩,⟨z,hz⟩,⟨d,hd⟩)
  let pc : B × C × D :=
    (rootAction Q split j (Q.simple i) c p.1,
     rootAction Q split i (Q.simple j*Q.simple i) c p.2.1,
     rootAction Q split j (Q.simple i*Q.simple j*Q.simple i) c p.2.2)
  have hp : pc = p := by
    apply inner_three_injective Q split hm i j hij
    change ((c : X ⧸ Q.D)*b*(c : X ⧸ Q.D)⁻¹)*
      ((c : X ⧸ Q.D)*z*(c : X ⧸ Q.D)⁻¹)*
      ((c : X ⧸ Q.D)*d*(c : X ⧸ Q.D)⁻¹) = b*z*d
    calc
      _ = (c : X ⧸ Q.D)*(b*z*d)*(c : X ⧸ Q.D)⁻¹ := by group
      _ = b*z*d := by
        rw [he,←mem_centralizer_singleton_iff.mp (hcent hx),mul_inv_cancel_right]
  have hb1 : b = 1 := by
    apply mem_bot.mp
    rw [←(hc (Q.simple i)).2]
    refine ⟨hb,mem_centralizer_singleton_iff.mpr ?_⟩
    have hh := congrArg (fun t : B × C × D => (t.1 : X ⧸ Q.D)) hp
    change (c : X ⧸ Q.D)*b*(c : X ⧸ Q.D)⁻¹ = b at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hd1 : d = 1 := by
    apply mem_bot.mp
    rw [←(hc (Q.simple i*Q.simple j*Q.simple i)).2]
    refine ⟨hd,mem_centralizer_singleton_iff.mpr ?_⟩
    have hh := congrArg (fun t : B × C × D => (t.2.2 : X ⧸ Q.D)) hp
    change (c : X ⧸ Q.D)*d*(c : X ⧸ Q.D)⁻¹ = d at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  rw [hb1,hd1,one_mul,mul_one] at he
  exact he ▸ hz

/-- The outer two fixed roots have commutator in the middle fixed root. -/
theorem separated_outer_commutator_le (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hK : simpleRemainder Q split i ≤ localKernel Q i)
    (c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)))
    (hc : ∀ w : Weyl Q,
      (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) ∧
      rootAt Q split j w ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥) :
    ⁅rootAt Q split i (Q.simple j),rootAt Q split i (Q.simple j*Q.simple i)⁆ ≤
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) := by
  have hh := comap_mono (f := (MulAut.conj (representative (Q.simple j) : X ⧸ Q.D)).toMonoidHom)
    (separated_perpendicular_commutator_le Q split hm i j hij hK c hc)
  change rightConjugate _ _ ≤ rightConjugate _ _ at hh
  rw [right_comm,right_simple,right_rep,right_rep] at hh
  simpa only [mul_assoc,ssq,mul_one] using hh

/-- Both cross-commutators with the middle fixed root vanish. -/
theorem separated_middle_commutators (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hK : simpleRemainder Q split i ≤ localKernel Q i)
    (c : X ⧸ Q.D)
    (hc : ∀ w : Weyl Q,
      c ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) ∧
      rootAt Q split j w ⊓ centralizer ({c} : Set (X ⧸ Q.D)) = ⊥) :
    ⁅rootAt Q split i (Q.simple j),rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ = ⊥ ∧
    ⁅rootAt Q split i (Q.simple j*Q.simple i),rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ = ⊥ := by
  have hz := separated_distance_two_commutator Q split hm i j hij hK c hc
  have h1 := congrArg (fun A => rightConjugate A (representative (Q.simple j) : X ⧸ Q.D)) hz
  rw [right_comm,right_simple,right_rep,right_bot] at h1
  have h2 := congrArg (fun A => rightConjugate A (representative (Q.simple i) : X ⧸ Q.D)) h1
  rw [right_comm,right_rep,right_rep,right_bot] at h2
  have hs := perpendicular_root_stable Q split hm i j hij
    (representative (Q.simple i)) (representative_spec _)
  rw [right_rep] at hs
  rw [hs] at h2
  exact ⟨h1,h2⟩


private theorem three_product_sup {Y : Type*} [Group Y] (A B C K : Subgroup Y)
    (hp : (K : Set Y) = (A : Set Y)*(B : Set Y)*(C : Set Y)) : A ⊔ B ⊔ C = K := by
  have ha : A ≤ K := by
    intro a ha
    change a ∈ (K : Set Y)
    rw [hp]
    exact ⟨a,⟨a,ha,1,one_mem _,mul_one _⟩,1,one_mem _,mul_one _⟩
  have hb : B ≤ K := by
    intro b hb
    change b ∈ (K : Set Y)
    rw [hp]
    exact ⟨b,⟨1,one_mem _,b,hb,one_mul _⟩,1,one_mem _,mul_one _⟩
  have hc : C ≤ K := by
    intro c hc
    change c ∈ (K : Set Y)
    rw [hp]
    exact ⟨1,⟨1,one_mem _,1,one_mem _,one_mul _⟩,c,hc,one_mul _⟩
  apply le_antisymm (sup_le (sup_le ha hb) hc)
  intro x hx
  change x ∈ (K : Set Y) at hx
  obtain ⟨ab,⟨a,ha,b,hb,rfl⟩,c,hc,rfl⟩ := hp ▸ hx
  exact mul_mem_sup (mul_mem_sup ha hb) hc

private theorem three_product_commutator_le {Y : Type*} [Group Y]
    (A B C K D : Subgroup Y) (hp : A ⊔ B ⊔ C = K)
    (hKD : K ≤ normalizer (D : Set Y))
    (hAA : ⁅A,A⁆ ≤ D) (hBB : ⁅B,B⁆ ≤ D) (hCC : ⁅C,C⁆ ≤ D)
    (hAB : ⁅A,B⁆ ≤ D) (hCB : ⁅C,B⁆ ≤ D) (hAC : ⁅A,C⁆ ≤ D) :
    ⁅K,K⁆ ≤ D := by
  have hA : A ≤ K := hp ▸ le_sup_of_le_left le_sup_left
  have hB : B ≤ K := hp ▸ le_sup_of_le_left le_sup_right
  have hC : C ≤ K := hp ▸ le_sup_right
  have bound (T : Subgroup Y) (ha : ⁅A,T⁆ ≤ D) (hb : ⁅B,T⁆ ≤ D)
      (hc : ⁅C,T⁆ ≤ D) : ⁅K,T⁆ ≤ D := by
    rw [←hp]
    exact commutator_sup_le_of_relative_normal K _ _ _ D hKD (sup_le hA hB) hC
      (commutator_sup_le_of_relative_normal K _ _ _ D hKD hA hB ha hb) hc
  have hKA := bound A hAA (by rwa [commutator_comm]) (by rwa [commutator_comm])
  have hKB := bound B hAB hBB hCB
  have hKC := bound C hAC (by rwa [commutator_comm]) hCC
  exact bound K (by rwa [commutator_comm]) (by rwa [commutator_comm]) (by rwa [commutator_comm])

private theorem normalizes_commutator {Y : Type*} [Group Y] (A : Subgroup Y) :
    normalizer (A : Set Y) ≤ normalizer ((⁅A,A⁆ : Subgroup Y) : Set Y) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,mem_normalizer_iff_map_conj_eq.mp hg]

/-- The fixed three-root group is abelian, and the perpendicular odd roots commute.
The actual linear local action discharges the small-section argument, including degree one. -/
theorem separated_linear_radical_abelian {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hK : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) (s : HexagonStructure.RootReflection Q split i)
    {a : ℕ} (ha : 0 < a) (hF : Nat.card F = 2^a)
    (hcard : Nat.card (simpleRoot Q split i) = 2^a)
    (c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)))
    (hc : ∀ w : Weyl Q,
      (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) ∧
      rootAt Q split j w ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥) :
    IsMulCommutative ↥(simpleRemainder Q split i ⊓
      centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D))) ∧
    ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ = ⊥ := by
  let A := rootAt Q split i (Q.simple j)
  let B := rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let K := simpleRemainder Q split i ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D))
  have hp : A ⊔ B ⊔ C = K := three_product_sup A B C K
    (separated_radical_centralizer_product Q split hm i j hij c hc)
  have hA : A ≤ K := hp ▸ le_sup_of_le_left le_sup_left
  have hB : B ≤ K := hp ▸ le_sup_of_le_left le_sup_right
  have hC : C ≤ K := hp ▸ le_sup_right
  have hab (w : Weyl Q) : ⁅rootAt Q split i w,rootAt Q split i w⁆ = ⊥ := by
    have hh := congrArg (fun T => rightConjugate T (representative w : X ⧸ Q.D))
      (simpleRoot_commutator_eq_bot_of_linear Q split i μ)
    simpa only [right_comm,right_simple,right_bot] using hh
  have hAA : ⁅A,A⁆ = ⊥ := hab _
  have hBB : ⁅B,B⁆ = ⊥ := hab _
  have hCC : ⁅C,C⁆ = ⊥ := hab _
  obtain ⟨hAB,hCB⟩ := separated_middle_commutators Q split hm i j hij hK c hc
  have hAC := separated_outer_commutator_le Q split hm i j hij hK c hc
  have hKB : K ≤ centralizer (B : Set (X ⧸ Q.D)) := by
    rw [←hp]
    exact sup_le (sup_le (commutator_eq_bot_iff_le_centralizer.mp hAB)
      (commutator_eq_bot_iff_le_centralizer.mp hBB))
        (commutator_eq_bot_iff_le_centralizer.mp hCB)
  have hd : ⁅K,K⁆ ≤ B := three_product_commutator_le A B C K B hp
    (hKB.trans (Subgroup.centralizer_le_normalizer _)) (hAA ▸ bot_le) (hBB ▸ bot_le)
    (hCC ▸ bot_le) (hAB ▸ bot_le) (hCB ▸ bot_le) hAC
  have hR : rankOne Q split i ≤ normalizer (K : Set (X ⧸ Q.D)) :=
    separated_radical_centralizer_normalized Q split i hK c (fun w => (hc w).1)
  have hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer (K : Set (X ⧸ Q.D)) := by
    apply (le_inf (inf_le_left.trans ((Q.tits.B_le_standardParabolic _).trans
      (remainder_parabolic_normalizes Q split i hK))) ?_).trans inf_normalizer_le_normalizer_inf
    apply le_trans _ (centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D))).le_normalizer
    intro t ht
    let := split.abelian
    exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (mul_comm (⟨t,ht⟩ : ↥(Q.tits.B ⊓ Q.tits.N)) c))
  have hACzero : ⁅A,C⁆ = ⊥ := by
    by_cases hz : ⁅K,K⁆ = ⊥
    · exact bot_unique ((commutator_mono hA hC).trans hz.le)
    have he : ⁅K,K⁆ = B := QuadrangleStructure.rootAt_eq_of_torus_invariant Q split i μ hK
      _ _ hd hz (hH.trans (normalizes_commutator K))
    have hRB : rankOne Q split i ≤ normalizer (B : Set (X ⧸ Q.D)) := by
      rw [←he]
      exact hR.trans (normalizes_commutator K)
    have hBc : Nat.card B = 2^a := by
      change Nat.card (rightConjugate _ _) = _
      rw [card_rightConjugate,hcard]
    have hcentral : ⁅rankOne Q split i,B⁆ = ⊥ := by
      by_cases ha1 : a = 1
      · exact commutator_eq_bot_iff_le_centralizer.mpr (hRB.trans
          (normalizer_le_centralizer_of_card_two B (by simpa only [ha1,pow_one] using hBc)))
      · apply linear_small_subgroup_centralized Q split i hK μ
          s B (hB.trans inf_le_left) hRB (by omega) hF
        rw [hBc]
        exact Nat.pow_lt_pow_right (by decide) (by omega)
    have hU : ⁅simpleRoot Q split i,B⁆ = ⊥ := bot_unique
      ((commutator_mono (show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left) le_rfl).trans hcentral.le)
    have hh := congrArg (fun T => rightConjugate T (representative (Q.simple j) : X ⧸ Q.D)) hU
    change rightConjugate ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ _ = _ at hh
    rw [right_comm,right_simple,right_rep,right_bot] at hh
    simpa only [mul_assoc,ssq,mul_one] using hh
  have hz : ⁅K,K⁆ = ⊥ := bot_unique (three_product_commutator_le A B C K ⊥ hp
    (by rw [Subgroup.normalizer_eq_top]; exact le_top) hAA.le hBB.le hCC.le hAB.le hCB.le hACzero.le)
  refine ⟨le_centralizer_iff_isMulCommutative.mp (commutator_eq_bot_iff_le_centralizer.mp hz),?_⟩
  have hh := congrArg (fun T => rightConjugate T (representative (Q.simple j) : X ⧸ Q.D)) hACzero
  change rightConjugate ⁅rootAt Q split i (Q.simple j),rootAt Q split i (Q.simple j*Q.simple i)⁆ _ = _ at hh
  rw [right_comm,right_rep,right_rep,right_bot,ssq,rootAt_one] at hh
  exact hh


/-- Perpendicular commuting roots generate commuting full rank-one groups. -/
theorem perpendicular_rankOne_commutator (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hc : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ = ⊥) :
    ⁅rankOne Q split i,rightConjugate (rankOne Q split i)
      (representative (Q.simple j*Q.simple i*Q.simple j) : X ⧸ Q.D)⁆ = ⊥ := by
  let w := Q.simple j*Q.simple i*Q.simple j
  let R := rankOne Q split i
  let E := rootAt Q split i w
  let R' := rightConjugate R (representative w : X ⧸ Q.D)
  have rsup (A B : Subgroup (X ⧸ Q.D)) (v : Weyl Q) :
      rightConjugate (A ⊔ B) (representative v : X ⧸ Q.D) =
        rightConjugate A (representative v : X ⧸ Q.D) ⊔
        rightConjugate B (representative v : X ⧸ Q.D) := by
    simp only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_sup]
  have hE : rightConjugate E (representative (Q.simple i) : X ⧸ Q.D) = E :=
    perpendicular_root_stable Q split hm i j hij _ (representative_spec _)
  have hopp := congrArg (fun A => rightConjugate A (representative (Q.simple i) : X ⧸ Q.D)) hc
  rw [right_comm,right_simple,hE,right_bot] at hopp
  have hRE : ⁅R,E⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (sup_le (commutator_eq_bot_iff_le_centralizer.mp hc)
      (commutator_eq_bot_iff_le_centralizer.mp hopp))
  have hw : w*w=1 := by
    dsimp [w]
    simp only [mul_assoc,←mul_assoc (Q.simple j) (Q.simple j),
      ←mul_assoc (Q.simple i) (Q.simple i),ssq,one_mul]
  have hRU := congrArg (fun A => rightConjugate A (representative w : X ⧸ Q.D)) hRE
  rw [right_comm,right_rep,hw,rootAt_one,right_bot,commutator_comm] at hRU
  have hR'eq : R' = E ⊔ rootAt Q split i (Q.simple i*w) := by
    change rightConjugate (simpleRoot Q split i ⊔ rootAt Q split i (Q.simple i)) _ = _
    rw [rsup,right_simple,right_rep]
  have hl : longest Q = Q.simple i*Q.simple j*Q.simple i*Q.simple j*
      Q.simple i*Q.simple j*Q.simple i*Q.simple j := by
    have h0 := alternatingWord_longest Q false
    have h1 := alternatingWord_longest Q true
    rw [hm] at h0 h1
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;>
      rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · exact (hij rfl).elim
    · simpa only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,
        Bool.not_true,mul_one,mul_assoc] using h0.symm
    · simpa only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,
        Bool.not_true,mul_one,mul_assoc] using h1.symm
    · exact (hij rfl).elim
  have hword : (Q.simple i*w)*Q.simple i = (longest Q*Q.simple i)*(Q.simple i*w) := by
    rw [hl]
    dsimp [w]
    simp only [mul_assoc,←mul_assoc (Q.simple j) (Q.simple j),
      ←mul_assoc (Q.simple i) (Q.simple i),ssq,one_mul,mul_one]
  have hR's : rightConjugate R' (representative (Q.simple i) : X ⧸ Q.D) = R' := by
    rw [hR'eq,rsup,hE,right_rep,hword,rootAt_longest_simple_mul Q split hm i j hij]
  have hOppR' := congrArg (fun A => rightConjugate A (representative (Q.simple i) : X ⧸ Q.D)) hRU
  change rightConjugate ⁅simpleRoot Q split i,R'⁆ _ = _ at hOppR'
  rw [right_comm,right_simple,hR's,right_bot] at hOppR'
  exact commutator_eq_bot_iff_le_centralizer.mpr
    (sup_le (commutator_eq_bot_iff_le_centralizer.mp hRU)
      (commutator_eq_bot_iff_le_centralizer.mp hOppR'))

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
