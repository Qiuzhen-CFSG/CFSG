module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.LocalActions
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.OrderedProducts
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.GroupTheory.Commutator.Basic
/-!
# Root-center bounds in a class-two hexagon radical

For an ordered root interval of class at most two, successive root
quotients bound its center by the product of the root-center orders.
At each step the normal radical quotient detects the leading root
coordinate. If each simple-root center is contained in its derived
subgroup, that coordinate is central in the interval and can be removed.
The right-conjugated shorter interval then supplies the inductive bound.

For a hexagon this gives |Z(U_sj)| <= |Z(U_i)|^3 |Z(U_j)|^2.
The CFSG companion supplies the regular unitary root centers and uses
this bound to prove that [U_sj',U_sj] is nontrivial. Normality is relative
to the actual unipotent subgroup; all coordinates stay in the same
marked quotient. No perfectness assumption on the original factors is used.

Source: Fong--Seitz I (6D), printed p.42, the class-two contradiction
preceding the lower-central and Cartan estimates. The root recurrence
is Carter 2.5.10 as implemented in RootCoordinates.Recurrence.
-/

open Subgroup
open scoped Pointwise commutatorElement
public noncomputable section

private theorem center_factor_bound {G : Type*} [Group G] [Finite G]
    (U K A B N : Subgroup G) (hKU : K ≤ U) (hAU : A ≤ K) (hBU : B ≤ K)
    (hN : U ≤ normalizer (N : Set G))
    (hBN : B ≤ N) (hdis : Disjoint A N)
    (hprod : (K : Set G) = (A : Set G)*(B : Set G))
    (hAZ : (center A).map A.subtype ≤ centralizer (K : Set G)) :
    Nat.card (center K) ≤ Nat.card (center A)*Nat.card (center B) := by
  let N₀ := N.subgroupOf U
  let : N₀.Normal := normal_subgroupOf_of_le_normalizer hN
  let π := QuotientGroup.mk' N₀
  let f : A →* U ⧸ N₀ := π.comp (inclusion (hAU.trans hKU))
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro x hx
    have hxN : inclusion (hAU.trans hKU) x ∈ N₀ := (QuotientGroup.eq_one_iff _).mp hx
    exact Subtype.ext (disjoint_def.mp hdis x.property hxN)
  have hex (x : center K) : ∃ p : center A × center B,
      (p.1.val : G)*(p.2.val : G) = x.val := by
    have hxK : (x.val : G) ∈ (K : Set G) := x.val.property
    rw [hprod] at hxK
    obtain ⟨a,ha,b,hb,hab⟩ := hxK
    let a₀ : A := ⟨a,ha⟩
    let b₀ : B := ⟨b,hb⟩
    have haZ : a₀ ∈ center A := by
      rw [mem_center_iff]
      intro y
      apply hf
      simp only [map_mul]
      have hxπ : π (inclusion hKU x.val) = f a₀ := by
        have he : inclusion hKU x.val = inclusion (hAU.trans hKU) a₀ *
            (⟨b,hBU.trans hKU hb⟩ : U) := Subtype.ext hab.symm
        rw [he,map_mul,show π (⟨b,hBU.trans hKU hb⟩ : U) = 1 from
          (QuotientGroup.eq_one_iff _).mpr (hBN hb),mul_one]
        rfl
      have hc := congrArg (fun z : K => π (inclusion hKU z))
        (mem_center_iff.mp x.property (inclusion hAU y))
      simp only [map_mul,hxπ] at hc
      change f y * f a₀ = f a₀ * f y at hc
      exact hc
    have haC : a ∈ centralizer (K : Set G) := hAZ (mem_map_of_mem _ haZ)
    have hbC : b ∈ centralizer (K : Set G) := by
      have hxC : (x.val : G) ∈ centralizer (K : Set G) := by
        intro y hy
        exact congrArg Subtype.val (mem_center_iff.mp x.property ⟨y,hy⟩)
      have hh := (centralizer (K : Set G)).mul_mem
        ((centralizer (K : Set G)).inv_mem haC) hxC
      rwa [←hab,inv_mul_cancel_left] at hh
    have hbZ : b₀ ∈ center B := by
      rw [mem_center_iff]
      intro y
      apply Subtype.ext
      exact hbC y (hBU y.property)
    exact ⟨(⟨a₀,haZ⟩,⟨b₀,hbZ⟩),hab⟩
  choose f₀ hf₀ using hex
  have hinj : Function.Injective f₀ := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact (hf₀ x).symm.trans ((congrArg (fun p : center A × center B =>
      (p.1.val : G)*(p.2.val : G)) he).trans (hf₀ y))
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective f₀ hinj

open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private def classTwoConjugateEquiv (A : Subgroup (X ⧸ Q.D)) (g : X ⧸ Q.D) :
    rightConjugate A g ≃* A :=
  ((rightConjugate A g).equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr (map_comap_eq_self_of_surjective (MulAut.conj g).surjective A))

private theorem interval_center_bound
    (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
    (hc : ∀ i, center (simpleRoot Q split i) ≤ _root_.commutator (simpleRoot Q split i))
    (b : Bool) (n : ℕ) (hn : n ≤ rotationOrder Q)
    (hclass : let A := rootIntersection split (longest Q) (alternatingWord Q b n)⁻¹;
      ⁅⁅A,A⁆,A⁆ = ⊥) :
    Nat.card (center (rootIntersection split (longest Q) (alternatingWord Q b n)⁻¹)) ≤
      ((orderedRoots Q split b n).map (fun A : Subgroup (X ⧸ Q.D) => Nat.card (center A))).prod := by
  induction n generalizing b with
  | zero =>
    change Nat.card (center (rootIntersection split (longest Q) (1 : Weyl Q)⁻¹)) ≤ 1
    rw [inv_one,rootIntersection_one]
    exact le_of_eq Nat.card_unique
  | succ n ih =>
    let i : Fin 2 := if b then 1 else 0
    let s := representative (Q.simple i)
    let w := (alternatingWord Q (!b) n)⁻¹
    let A := simpleRoot Q split i
    let T := rootIntersection split (longest Q) w
    let B := rightConjugate T (s : X ⧸ Q.D)
    let K := rootIntersection split (longest Q) (w*Q.simple i)
    have hstepword : (alternatingWord Q b (n+1))⁻¹ = w*Q.simple i := by
      dsimp only [w,i]
      rw [alternatingWord,mul_inv_rev]
      congr 1
      exact inv_eq_of_mul_eq_one_right (by
        simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem _)).2)
    rw [hstepword] at hclass ⊢
    have hstep : Q.tits.wordLength (w*Q.simple i) = Q.tits.wordLength w+1 := by
      rw [←hstepword,wordLength_inv,wordLength_inv,wordLength_alternatingWord Q _ hn,
        wordLength_alternatingWord Q _ (by omega)]
    have hprod : (K : Set (X ⧸ Q.D)) = (A : Set _)*(B : Set _) :=
      rootIntersection_ascent_product Q split w i hstep s (representative_spec _)
    have hA : A ≤ K := by
      intro a ha
      change a ∈ (K : Set (X ⧸ Q.D))
      rw [hprod]
      exact ⟨a,ha,1,one_mem _,mul_one _⟩
    have hB : B ≤ K := by
      intro a ha
      change a ∈ (K : Set (X ⧸ Q.D))
      rw [hprod]
      exact ⟨1,one_mem _,a,ha,one_mul _⟩
    have hBc : ⁅⁅B,B⁆,B⁆ = ⊥ := bot_unique
      ((commutator_mono (commutator_mono hB hB) hB).trans_eq hclass)
    have hTc : ⁅⁅T,T⁆,T⁆ = ⊥ := by
      have hh := congrArg (fun R : Subgroup (X ⧸ Q.D) =>
        R.map (MulAut.conj (s : X ⧸ Q.D)).toMonoidHom) hBc
      simp only [map_commutator,Subgroup.map_bot] at hh
      have hBT : B.map (MulAut.conj (s : X ⧸ Q.D)).toMonoidHom = T :=
        map_comap_eq_self_of_surjective (MulAut.conj _).surjective _
      rwa [hBT] at hh
    have hbound := center_factor_bound split.U K A B (simpleRemainder Q split i)
      inf_le_left hA hB
      (split.U_le.trans ((Q.tits.B_le_standardParabolic _).trans
        (remainder_parabolic_normalizes Q split i (hK i))))
      (ascent_root_conjugate_le_remainder Q split w i hstep s (representative_spec _))
      (simpleRoot_disjoint_remainder Q split i) hprod (by
        apply (map_mono (f := A.subtype) (hc i)).trans
        rw [map_subtype_commutator]
        exact (commutator_mono hA hA).trans (commutator_eq_bot_iff_le_centralizer.mp hclass))
    have hcb : Nat.card (center B) = Nat.card (center T) :=
      Nat.card_congr (centerCongr (classTwoConjugateEquiv Q T (s : X ⧸ Q.D))).toEquiv
    have hrest := ih (!b) (by omega) hTc
    have hlist : ((orderedRoots Q split b (n+1)).map (fun C : Subgroup (X ⧸ Q.D) => Nat.card (center C))).prod =
        Nat.card (center A)*((orderedRoots Q split (!b) n).map
          (fun C : Subgroup (X ⧸ Q.D) => Nat.card (center C))).prod := by
      simp only [orderedRoots,List.map_cons,List.prod_cons,List.map_map]
      congr 1
      congr 1
      apply List.map_congr_left
      intro C _
      exact Nat.card_congr (centerCongr (classTwoConjugateEquiv Q C (s : X ⧸ Q.D))).toEquiv
    rw [hlist]
    rw [hcb] at hbound
    exact hbound.trans (Nat.mul_le_mul_left _ hrest)
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem center_card_conjugate (A : Subgroup (X ⧸ Q.D)) (g : X ⧸ Q.D) :
    Nat.card (center (rightConjugate A g)) = Nat.card (center A) :=
  Nat.card_congr (centerCongr (classTwoConjugateEquiv Q A g)).toEquiv

private theorem center_ordered_five (b : Bool) :
    ((orderedRoots Q split b 5).map (fun A : Subgroup (X ⧸ Q.D) => Nat.card (center A))).prod =
      Nat.card (center (simpleRoot Q split (if b then 1 else 0)))^3 *
      Nat.card (center (simpleRoot Q split (if b then 0 else 1)))^2 := by
  cases b
  · change _ = Nat.card (center (simpleRoot Q split 0))^3 * Nat.card (center (simpleRoot Q split 1))^2
    simp only [orderedRoots,List.map_cons,List.map_nil,center_card_conjugate,
      List.prod_cons,List.prod_nil,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true]
    ring
  · change _ = Nat.card (center (simpleRoot Q split 1))^3 * Nat.card (center (simpleRoot Q split 0))^2
    simp only [orderedRoots,List.map_cons,List.map_nil,center_card_conjugate,
      List.prod_cons,List.prod_nil,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true]
    ring

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

/-- If the radical has class at most two, its center is bounded by the
product of the five root centers. Only relative radical normality is used. -/
theorem radical_classTwo_center_card_bound (hhex : rotationOrder Q = 6)
    (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
    (hc : ∀ i, center (simpleRoot Q split i) ≤ _root_.commutator (simpleRoot Q split i))
    (i j : Fin 2) (hij : i ≠ j)
    (hclass : ⁅⁅simpleRemainder Q split j,simpleRemainder Q split j⁆,
      simpleRemainder Q split j⁆ = ⊥) :
    Nat.card (center (simpleRemainder Q split j)) ≤
      Nat.card (center (simpleRoot Q split i))^3 *
      Nat.card (center (simpleRoot Q split j))^2 := by
  have hb (b : Bool)
      (hcl : ⁅⁅simpleRemainder Q split (if b then 0 else 1),
        simpleRemainder Q split (if b then 0 else 1)⁆,
        simpleRemainder Q split (if b then 0 else 1)⁆ = ⊥) :
      Nat.card (center (simpleRemainder Q split (if b then 0 else 1))) ≤
        Nat.card (center (simpleRoot Q split (if b then 1 else 0)))^3 *
        Nat.card (center (simpleRoot Q split (if b then 0 else 1)))^2 := by
    have hh := interval_center_bound Q split hK hc b 5 (by omega) (by
      dsimp only
      rwa [five_interval Q split hhex b])
    rwa [five_interval Q split hhex b,center_ordered_five] at hh
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact hb false hclass
  · exact hb true hclass
  · exact (hij rfl).elim

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
