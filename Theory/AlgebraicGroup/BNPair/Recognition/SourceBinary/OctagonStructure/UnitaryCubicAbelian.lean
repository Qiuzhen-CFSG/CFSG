module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryCubicRadical

/-!
# The cubic radical centralizer is abelian

The short-root commutator bounds, together with unique fixed coordinates,
make the middle Frattini factor central and put the outer commutator in it.
If the derived subgroup is nontrivial, full-Cartan irreducibility makes it
the whole middle factor. The simple unitary Frattini group normalizes that
factor. Its commutator with it lies in a disjoint root, so vanishes; Weyl
transport then kills the outer commutator as well. Thus the full cubic
radical centralizer is abelian.

Source: Fong--Seitz I (6F), printed p.47, first paragraph. The source
consumer discharges center irreducibility with its actual SU3/PSU3 marking,
including degree one. The later lower-central-series contradiction remains.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
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
private theorem frattini_right (j : Fin 2)
    (hfix : ∀ w : Weyl Q, rootAt Q split j w ⊓
      centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) = rootFrattiniAt Q split j w)
    (v w : Weyl Q) :
    rightConjugate (rootFrattiniAt Q split j v) (representative w : X ⧸ Q.D) =
      rootFrattiniAt Q split j (v*w) := by
  rw [←hfix, rightConjugate_inf,right_rep,
    rightConjugate_eq_self _ (normalizer_le_normalizer_centralizer _
      (cartanThreeCore_normalized Q (representative w).property)),hfix]

private theorem middle_three_injective (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) :
    Function.Injective (rootProduct [rootAt Q split j (Q.simple i),
      rootAt Q split i (Q.simple j*Q.simple i),
      rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)]) := by
  let l := [rootAt Q split j (Q.simple i),rootAt Q split i (Q.simple j*Q.simple i),
    rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)]
  have he : ∃ b, orderedRoots Q split b 4 = simpleRoot Q split i :: l := by
    rcases (show i=0 ∨ i=1 by omega) with rfl | rfl <;>
      rcases (show j=0 ∨ j=1 by omega) with rfl | rfl
    · exact (hij rfl).elim
    · exact ⟨false, by simp only [l,orderedRoots,Bool.false_eq_true,↓reduceIte,
        Bool.not_false,Bool.not_true,List.map_cons,List.map_nil,right_simple,right_rep,mul_assoc]⟩
    · exact ⟨true, by simp only [l,orderedRoots,Bool.false_eq_true,↓reduceIte,
        Bool.not_false,Bool.not_true,List.map_cons,List.map_nil,right_simple,right_rep,mul_assoc]⟩
    · exact (hij rfl).elim
  obtain ⟨b,hb⟩ := he
  have hinj : Function.Injective (rootProduct (orderedRoots Q split b 4)) := by
    intro p q he
    apply (orderedCoordinates Q split b 4 (by omega)).injective
    exact Subtype.ext (by simpa only [orderedCoordinates_apply] using he)
  rw [hb] at hinj
  intro p q he
  exact congrArg Prod.snd (hinj (a₁ := (1,p)) (a₂ := (1,q))
    (by change (1 : X ⧸ Q.D)*rootProduct l p = 1*rootProduct l q
        simpa only [one_mul] using he))

variable (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
  (hKj : simpleRemainder Q split j ≤ localKernel Q j)
  (hfree : ∀ w : Weyl Q, rootAt Q split i w ⊓
    centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) = ⊥)
  (hfix : ∀ w : Weyl Q, rootAt Q split j w ⊓
    centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) = rootFrattiniAt Q split j w)

include hm hij hKj hfree hfix in
private theorem distance_two :
    ⁅rootFrattiniAt Q split j 1,rootFrattiniAt Q split j (Q.simple i*Q.simple j)⁆ = ⊥ := by
  have hL (w) : rootFrattiniAt Q split j w ≤ rootAt Q split j w := by
    rw [←hfix]; exact inf_le_left
  have hC (w) : rootFrattiniAt Q split j w ≤ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) := by
    rw [←hfix]; exact inf_le_right
  apply bot_unique
  apply (le_inf ((commutator_mono (by simpa only [rootAt_one] using hL 1) (hL _)).trans
    (distance_two_commutator_le Q split hm j i hij.symm hKj))
      ((commutator_mono (hC 1) (hC _)).trans (commutator_le_self _))).trans
    (hfree (Q.simple j)).le

include hm hij hKj hfree hfix in
private theorem perpendicular_le :
    ⁅rootFrattiniAt Q split j 1,
      rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i)⁆ ≤
      rootFrattiniAt Q split j (Q.simple i*Q.simple j) := by
  let C := centralizer (cartanThreeCore Q : Set (X ⧸ Q.D))
  let l := [rootAt Q split i (Q.simple j),rootAt Q split j (Q.simple i*Q.simple j),
    rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)]
  have hnorm : ∀ A ∈ l, cartanThreeCore Q ≤ normalizer (A : Set (X ⧸ Q.D)) := by
    intro A hA
    simp only [l,List.mem_cons,List.not_mem_nil,or_false] at hA
    rcases hA with rfl | rfl | rfl <;>
      exact (cartanThreeCore_le Q).trans (rootAt_torus_normalizes Q split _ _)
  have he := unique_root_product_centralizer l (cartanThreeCore Q) hnorm
    (middle_three_injective Q split hm j i hij.symm)
  have he' : Set.range (rootProduct l) ∩ (C : Set (X ⧸ Q.D)) =
      (rootFrattiniAt Q split j (Q.simple i*Q.simple j) : Set (X ⧸ Q.D)) := by
    simpa only [l,List.map_cons,List.map_nil,hfree,hfix,List.prod_cons,List.prod_nil,
      coe_bot,Set.singleton_one,one_mul,mul_one] using he
  have hL (w) : rootFrattiniAt Q split j w ≤ rootAt Q split j w := by
    rw [←hfix]; exact inf_le_left
  have hC (w) : rootFrattiniAt Q split j w ≤ C := by
    rw [←hfix]; exact inf_le_right
  intro x hx
  apply he'.subset
  refine ⟨?_,(commutator_mono (hC 1) (hC _)).trans (commutator_le_self _) hx⟩
  have hs := distance_four_commutator_support Q split hm j i hij.symm hKj x
    (commutator_mono (by simpa only [rootAt_one] using hL 1) (hL _) hx)
  obtain ⟨bc,⟨b,hb,c,hc,rfl⟩,d,hd,he⟩ := hs
  refine ⟨(⟨b,hb⟩,⟨c,hc⟩,⟨d,hd⟩,PUnit.unit),?_⟩
  change b*(c*(d*1))=x
  simpa only [mul_one,mul_assoc] using he

include hm hij hKj hfree hfix in
private theorem middle_commutators :
    ⁅rootFrattiniAt Q split j (Q.simple i),
      rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i)⁆ = ⊥ ∧
    ⁅rootFrattiniAt Q split j (Q.simple i*Q.simple j),
      rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i)⁆ = ⊥ := by
  have hz := distance_two Q split hm i j hij hKj hfree hfix
  have h1 := congrArg (fun A => rightConjugate A (representative (Q.simple i) : X ⧸ Q.D)) hz
  rw [right_comm,frattini_right Q split j hfix,frattini_right Q split j hfix,
    one_mul,right_bot] at h1
  have h2 := congrArg (fun A => rightConjugate A (representative (Q.simple j) : X ⧸ Q.D)) h1
  rw [right_comm,frattini_right Q split j hfix,frattini_right Q split j hfix,right_bot] at h2
  have hs := perpendicular_root_stable Q split hm j i hij.symm
    (representative (Q.simple j)) (representative_spec _)
  rw [right_rep] at hs
  have hs' : rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i*Q.simple j) =
      rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i) := by
    unfold rootFrattiniAt
    rw [hs]
  rw [hs'] at h2
  exact ⟨h1,h2⟩

include hm hij hKj hfree hfix in
private theorem outer_le :
    ⁅rootFrattiniAt Q split j (Q.simple i),
      rootFrattiniAt Q split j (Q.simple i*Q.simple j)⁆ ≤
      rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i) := by
  have hh := comap_mono (f := (MulAut.conj (representative (Q.simple i) : X ⧸ Q.D)).toMonoidHom)
    (perpendicular_le Q split hm i j hij hKj hfree hfix)
  change rightConjugate _ _ ≤ rightConjugate _ _ at hh
  rw [right_comm,frattini_right Q split j hfix,frattini_right Q split j hfix,
    frattini_right Q split j hfix,one_mul] at hh
  simpa only [mul_assoc,ssq,mul_one] using hh



include hm hij hKj hfree hfix in
/-- The source cubic radical centralizer is abelian. The only local
representation input is irreducibility of its middle root center. -/
theorem unitary_cubic_radical_abelian
    (hcenter : ∀ w : Weyl Q, frattini (rootAt Q split j w) = center (rootAt Q split j w))
    (hirr : ∀ D : Subgroup (X ⧸ Q.D),
      D ≤ rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i) → D ≠ ⊥ →
      Q.tits.B ⊓ Q.tits.N ≤ normalizer (D : Set (X ⧸ Q.D)) →
      D = rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i)) :
    IsMulCommutative ↥(simpleRemainder Q split j ⊓
      centralizer (cartanThreeCore Q : Set (X ⧸ Q.D))) := by
  let A := rootFrattiniAt Q split j (Q.simple i)
  let B := rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i)
  let C := rootFrattiniAt Q split j (Q.simple i*Q.simple j)
  let K := simpleRemainder Q split j ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D))
  have hp : (K : Set (X ⧸ Q.D)) = (A : Set (X ⧸ Q.D))*(B : Set (X ⧸ Q.D))*(C : Set (X ⧸ Q.D)) :=
    unitary_cubic_radical_product Q split hm i j hij hfree hfix
  have hA : A ≤ K := by
    intro x hx
    change x ∈ (K : Set (X ⧸ Q.D))
    rw [hp]
    exact ⟨x,⟨x,hx,1,one_mem _,mul_one _⟩,1,one_mem _,mul_one _⟩
  have hB : B ≤ K := by
    intro x hx
    change x ∈ (K : Set (X ⧸ Q.D))
    rw [hp]
    exact ⟨x,⟨1,one_mem _,x,hx,one_mul _⟩,1,one_mem _,mul_one _⟩
  have hC : C ≤ K := by
    intro x hx
    change x ∈ (K : Set (X ⧸ Q.D))
    rw [hp]
    exact ⟨1,⟨1,one_mem _,1,one_mem _,one_mul _⟩,x,hx,one_mul _⟩
  have hjoin : A ⊔ B ⊔ C = K := by
    apply le_antisymm (sup_le (sup_le hA hB) hC)
    intro x hx
    obtain ⟨ab,⟨a,ha,b,hb,rfl⟩,c,hc,rfl⟩ := hp ▸ (show x ∈ (K : Set (X ⧸ Q.D)) from hx)
    exact mul_mem_sup (mul_mem_sup ha hb) hc
  have hself (w) : ⁅rootFrattiniAt Q split j w,rootFrattiniAt Q split j w⁆ = ⊥ := by
    unfold rootFrattiniAt
    rw [hcenter]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rintro x ⟨x,hx,rfl⟩ y ⟨y,_,rfl⟩
    exact congrArg Subtype.val ((mem_center_iff.mp hx) y)
  obtain ⟨hAB,hCB⟩ := middle_commutators Q split hm i j hij hKj hfree hfix
  have hAC := outer_le Q split hm i j hij hKj hfree hfix
  have hKB : K ≤ centralizer (B : Set (X ⧸ Q.D)) := by
    rw [←hjoin]
    exact sup_le (sup_le (commutator_eq_bot_iff_le_centralizer.mp hAB)
      (commutator_eq_bot_iff_le_centralizer.mp (hself _)))
      (commutator_eq_bot_iff_le_centralizer.mp hCB)
  have hKD : K ≤ normalizer (B : Set (X ⧸ Q.D)) := hKB.trans (Subgroup.centralizer_le_normalizer _)
  have bound (Z : Subgroup (X ⧸ Q.D)) (ha : ⁅A,Z⁆ ≤ B) (hb : ⁅B,Z⁆ ≤ B)
      (hc : ⁅C,Z⁆ ≤ B) : ⁅K,Z⁆ ≤ B := by
    rw [←hjoin]
    exact commutator_sup_le_of_relative_normal K _ _ _ B hKD (sup_le hA hB) hC
      (commutator_sup_le_of_relative_normal K _ _ _ B hKD hA hB ha hb) hc
  have hd : ⁅K,K⁆ ≤ B := by
    apply bound K
    · rw [commutator_comm]
      exact bound A (hself _ ▸ bot_le) (by rw [commutator_comm,hAB]; exact bot_le)
        (by rw [commutator_comm]; exact hAC)
    · rw [commutator_comm]
      exact bound B (hAB ▸ bot_le) (hself _ ▸ bot_le) (hCB ▸ bot_le)
    · rw [commutator_comm]
      exact bound C hAC (by rw [commutator_comm,hCB]; exact bot_le) (hself _ ▸ bot_le)
  have norm_derived (V : Subgroup (X ⧸ Q.D)) :
      normalizer (V : Set (X ⧸ Q.D)) ≤ normalizer (↑(⁅V,V⁆) : Set (X ⧸ Q.D)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,mem_normalizer_iff_map_conj_eq.mp hg]
  have hzero : ⁅A,C⁆ = ⊥ := by
    by_cases hz : ⁅K,K⁆ = ⊥
    · exact bot_unique ((commutator_mono hA hC).trans hz.le)
    have he : ⁅K,K⁆ = B := hirr _ hd hz
      ((unitary_cubic_radical_cartan_normalizes Q split j hKj).trans (norm_derived K))
    have hn : rootFrattiniAt Q split j 1 ≤ normalizer (B : Set (X ⧸ Q.D)) := by
      rw [←he]
      exact le_sup_left.trans ((unitary_cubic_radical_frattini_normalizes Q split j hKj hfix).trans
        (norm_derived K))
    have hdis : Disjoint (rootAt Q split j (Q.simple i*Q.simple j*Q.simple i))
        (rootAt Q split j (Q.simple i*Q.simple j)) := by
      apply rootAt_disjoint
      have hinv (k : Fin 2) : (Q.simple k)⁻¹ = Q.simple k := inv_eq_of_mul_eq_one_right (ssq Q k)
      simp only [mul_inv_rev,hinv,←mul_assoc]
      have hl (b : Bool) : Q.tits.wordLength (alternatingWord Q b 7) =
          Q.tits.wordLength (alternatingWord Q b 6)+1 := by
        rw [wordLength_alternatingWord Q b (by omega),wordLength_alternatingWord Q b (by omega)]
      rcases (show i=0 ∨ i=1 by omega) with rfl | rfl <;>
        rcases (show j=0 ∨ j=1 by omega) with rfl | rfl
      · exact (hij rfl).elim
      · simpa only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true,
          mul_one,←mul_assoc] using hl true
      · simpa only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true,
          mul_one,←mul_assoc] using hl false
      · exact (hij rfl).elim
    have hs : ⁅rootFrattiniAt Q split j 1,B⁆ = ⊥ := by
      apply bot_unique
      apply (le_inf ((le_normalizer_iff_commutator_le_right.mp hn).trans (map_subtype_le _))
        ((perpendicular_le Q split hm i j hij hKj hfree hfix).trans (map_subtype_le _))).trans
        (disjoint_iff.mp hdis).le
    have hh := congrArg (fun V => rightConjugate V (representative (Q.simple i) : X ⧸ Q.D)) hs
    change rightConjugate ⁅rootFrattiniAt Q split j 1,
      rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i)⁆ _ = _ at hh
    rw [right_comm,frattini_right Q split j hfix,frattini_right Q split j hfix,
      one_mul,right_bot] at hh
    simpa only [mul_assoc,ssq,mul_one] using hh
  have hKA : K ≤ centralizer (A : Set (X ⧸ Q.D)) := by
    rw [←hjoin]
    exact sup_le (sup_le (commutator_eq_bot_iff_le_centralizer.mp (hself _))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hAB)))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero))
  have hKC : K ≤ centralizer (C : Set (X ⧸ Q.D)) := by
    rw [←hjoin]
    exact sup_le (sup_le (commutator_eq_bot_iff_le_centralizer.mp hzero)
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hCB)))
      (commutator_eq_bot_iff_le_centralizer.mp (hself _))
  apply le_centralizer_iff_isMulCommutative.mp
  change K ≤ centralizer (K : Set (X ⧸ Q.D))
  nth_rw 1 [←hjoin]
  exact sup_le (sup_le (le_centralizer_iff.mp hKA) (le_centralizer_iff.mp hKB))
    (le_centralizer_iff.mp hKC)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
