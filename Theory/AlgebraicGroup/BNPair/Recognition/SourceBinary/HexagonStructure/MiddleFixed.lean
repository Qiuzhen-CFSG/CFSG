module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.OddCartan
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.OrthogonalRoots

/-!
# Unique middle-root coordinates and the odd actor's fixed subgroup

The three middle roots are the conjugate of a reduced three-root ordered
product. Transport its unique coordinates to the literal factors
U_j^(s_i), U_i^(s_j s_i), U_j^(s_i s_j). This gives their exact product
order and lets equality under a Cartan action be tested coordinatewise.
When the odd actor fixes the smaller middle root and has no nonidentity
fixed point in the other two, its fixed subgroup in their product is
exactly the smaller root. No derived-subgroup identity is assumed.

Source: Fong--Seitz I (3G), (6E), printed pp.14--16,44. MiddleIsolation
uses both the cardinality and fixed subgroup in the actual radical.
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates GTwoSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem conjugate_three_injective (hm : rotationOrder Q = 6) (b : Bool)
    (n : X ⧸ Q.D) : Function.Injective
      (rootProduct ((orderedRoots Q split b 3).map (fun A => rightConjugate A n))) := by
  let l := orderedRoots Q split b 3
  let e := conjugateTuple l n
  intro p q hpq
  have he (z : RootTuple (l.map (fun A => rightConjugate A n))) :
      rootProduct (l.map (fun A => rightConjugate A n)) z =
        n⁻¹ * rootProduct l (e.symm z) * n := by
    simpa only [e,Equiv.apply_symm_apply] using rootProduct_conjugateTuple l n (e.symm z)
  have hp : rootProduct l (e.symm p) = rootProduct l (e.symm q) := by
    apply (MulAut.conj n⁻¹).injective
    simpa only [MulAut.conj_apply,inv_inv] using (he p).symm.trans (hpq.trans (he q))
  have hc : e.symm p = e.symm q := (orderedCoordinates Q split b 3 (by omega)).injective
    (Subtype.ext (by simpa only [orderedCoordinates_apply] using hp))
  exact e.symm.injective hc

private theorem middle_list (hm : rotationOrder Q = 6) (b : Bool) :
    let j : Fin 2 := if b then 1 else 0
    let i : Fin 2 := if b then 0 else 1
    (orderedRoots Q split b 3).map (fun A => rightConjugate A
      (representative (Q.simple i) : X ⧸ Q.D)) =
      [rootAt Q split j (Q.simple i),
       rootAt Q split i (Q.simple j*Q.simple i),
       rootAt Q split j (Q.simple i*Q.simple j)] := by
  have hr (k : Fin 2) (w : Weyl Q) :
      rightConjugate (simpleRoot Q split k) (representative w : X ⧸ Q.D) = rootAt Q split k w := rfl
  have hc (k : Fin 2) (v w : Weyl Q) :
      rightConjugate (rootAt Q split k v) (representative w : X ⧸ Q.D) = rootAt Q split k (v*w) :=
    rootAt_right Q split k v w _ (representative_spec _)
  cases b <;>
    simp only [orderedRoots,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true,
      List.map_cons,List.map_nil,hr,hc]
  · rw [orthogonal_root_stabilizer Q split hm 0 1 (by decide)]
  · rw [orthogonal_root_stabilizer Q split hm 1 0 (by decide)]

private theorem middle_product_injective (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) : Function.Injective
      (rootProduct [rootAt Q split j (Q.simple i),
       rootAt Q split i (Q.simple j*Q.simple i),
       rootAt Q split j (Q.simple i*Q.simple j)]) := by
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · have he := middle_list Q split hm true
    simp only [↓reduceIte] at he
    rw [← he]
    exact conjugate_three_injective Q split hm true _
  · have he := middle_list Q split hm false
    simp only [Bool.false_eq_true,↓reduceIte] at he
    rw [← he]
    exact conjugate_three_injective Q split hm false _
  · exact (hij rfl).elim

/-- Unique coordinates in the actual three-middle-root product. -/
def middleCoordinates (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j) :
    (rootAt Q split j (Q.simple i) ×
      rootAt Q split i (Q.simple j*Q.simple i) ×
      rootAt Q split j (Q.simple i*Q.simple j)) ≃ middleRoots Q split i j := by
  let f : (rootAt Q split j (Q.simple i) ×
      rootAt Q split i (Q.simple j*Q.simple i) ×
      rootAt Q split j (Q.simple i*Q.simple j)) → middleRoots Q split i j :=
    fun z => ⟨(z.1 : X ⧸ Q.D)*z.2.1*z.2.2,
      mul_mem (mul_mem (mem_sup_left (mem_sup_left z.1.property))
        (mem_sup_left (mem_sup_right z.2.1.property))) (mem_sup_right z.2.2.property)⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q hpq
    have hprod := congrArg Subtype.val hpq
    let l := [rootAt Q split j (Q.simple i),
      rootAt Q split i (Q.simple j*Q.simple i),
      rootAt Q split j (Q.simple i*Q.simple j)]
    have ht := middle_product_injective Q split hm i j hij
      (show rootProduct l (p.1,p.2.1,p.2.2,PUnit.unit) =
        rootProduct l (q.1,q.2.1,q.2.2,PUnit.unit) from by
          simpa only [l,f,rootProduct,mul_one,mul_assoc] using hprod)
    apply Prod.ext
    · exact congrArg (fun z : RootTuple l => z.1) ht
    · apply Prod.ext
      · exact congrArg (fun z : RootTuple l => z.2.1) ht
      · exact congrArg (fun z : RootTuple l => z.2.2.1) ht
  · intro x
    have hx := x.property
    rw [← SetLike.mem_coe, middleRoots_product Q split hm i j hij] at hx
    obtain ⟨bc,⟨b,hb,c,hc,rfl⟩,d,hd,he⟩ := hx
    exact ⟨(⟨b,hb⟩,⟨c,hc⟩,⟨d,hd⟩),Subtype.ext he⟩

@[simp] theorem middleCoordinates_apply (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (z : rootAt Q split j (Q.simple i) ×
      rootAt Q split i (Q.simple j*Q.simple i) ×
      rootAt Q split j (Q.simple i*Q.simple j)) :
    (middleCoordinates Q split hm i j hij z : X ⧸ Q.D) = (z.1 : X ⧸ Q.D)*z.2.1*z.2.2 := by
  unfold middleCoordinates
  rfl

theorem middleRoots_card (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) :
    Nat.card (middleRoots Q split i j) =
      Nat.card (simpleRoot Q split i) * Nat.card (simpleRoot Q split j)^2 := by
  rw [← Nat.card_congr (middleCoordinates Q split hm i j hij),Nat.card_prod,Nat.card_prod]
  simp only [rootAt,card_rightConjugate]
  ring

/-- The separating actor's fixed subgroup in the literal three-root section
is precisely the middle smaller root. No derived identity is used. -/
theorem middleRoots_fixed_eq (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {t : X ⧸ Q.D}
    (ht : t ∈ Q.tits.B ⊓ Q.tits.N)
    (hc : t ∈ centralizer (rootAt Q split i (Q.simple j*Q.simple i) : Set (X ⧸ Q.D)))
    (hB : rootAt Q split j (Q.simple i) ⊓ centralizer ({t} : Set (X ⧸ Q.D)) = ⊥)
    (hD : rootAt Q split j (Q.simple i*Q.simple j) ⊓ centralizer ({t} : Set (X ⧸ Q.D)) = ⊥) :
    middleRoots Q split i j ⊓ centralizer ({t} : Set (X ⧸ Q.D)) =
      rootAt Q split i (Q.simple j*Q.simple i) := by
  let B := rootAt Q split j (Q.simple i)
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let D := rootAt Q split j (Q.simple i*Q.simple j)
  let fB : MulAut B := B.normalizerMonoidHom ⟨t,rootAt_torus_normalizes Q split j _ ht⟩
  let fC : MulAut C := C.normalizerMonoidHom ⟨t,rootAt_torus_normalizes Q split i _ ht⟩
  let fD : MulAut D := D.normalizerMonoidHom ⟨t,rootAt_torus_normalizes Q split j _ ht⟩
  apply le_antisymm
  · intro x hx
    obtain ⟨⟨b,c,d⟩,he⟩ := (middleCoordinates Q split hm i j hij).surjective ⟨x,hx.1⟩
    have he' : (b : X ⧸ Q.D)*c*d = x := congrArg Subtype.val he
    have hcj : t*x*t⁻¹ = x := mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_singleton_iff.mp hx.2).symm
    have htuple : (fB b,fC c,fD d) = (b,c,d) := by
      apply (middleCoordinates Q split hm i j hij).injective
      apply Subtype.ext
      change (t*b*t⁻¹)*(t*c*t⁻¹)*(t*d*t⁻¹) = (b : X ⧸ Q.D)*c*d
      calc
        _ = t*((b : X ⧸ Q.D)*c*d)*t⁻¹ := by group
        _ = _ := by rw [he',hcj]
    have hbfix : t*(b : X ⧸ Q.D)*t⁻¹ = b := congrArg (fun z : B × C × D => (z.1 : X ⧸ Q.D)) htuple
    have hdfix : t*(d : X ⧸ Q.D)*t⁻¹ = d := congrArg (fun z : B × C × D => (z.2.2 : X ⧸ Q.D)) htuple
    have hb1 : (b : X ⧸ Q.D) = 1 := mem_bot.mp
      (hB ▸ ⟨b.property,mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hbfix).symm⟩)
    have hd1 : (d : X ⧸ Q.D) = 1 := mem_bot.mp
      (hD ▸ ⟨d.property,mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hdfix).symm⟩)
    rw [← he',hb1,hd1,one_mul,mul_one]
    exact c.property
  · intro c hcC
    exact ⟨mem_sup_left (mem_sup_right hcC),
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hc c hcC)⟩

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
