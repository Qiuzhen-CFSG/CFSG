module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiDerivedRoots
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiConstituentKernels
public import Theory.Representation.DistinctKernelGenerators

/-!
# Both exact products for the regular Suzuki derived radical

The larger q⁶ branch has a radical quotient of binary dimension 4a.
Its four nonmiddle root quotients already inject. If the middle root map
were nonzero, its irreducibility would make it injective too. The five
pairwise distinct actual Cartan kernels separate their simple images,
forcing dimension at least 5a, a contradiction. Hence the entire middle
root lies in the derived radical. Unique five-root coordinates and the
order now identify the exact ordered product with the four nonmiddle
Frattini subgroups. Combining the earlier q⁵ product gives both alternatives.

Source: Fong--Seitz I (6C), printed p.41, the Wedderburn-component step.
The natural composition-factor placement and the order-four triple
commutator contradiction remain further steps; no exclusion is asserted.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped IsMulCommutative
open Subgroup BenderSuzuki.MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- In the q⁶ branch, the whole middle root belongs to the derived radical.
If its quotient map were nonzero, five distinct simple Cartan constituents
would embed in the quotient, forcing degree at least 5a instead of 4a. -/
theorem suzuki_middle_root_le_derived_of_large_order (hhex : rotationOrder Q = 6)
    (hcore : Q.tits.B.normalCore = ⊥) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m : ℕ} (hm : 0 < m)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup m)
    (hcard : Nat.card (⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ :
      Subgroup (X ⧸ Q.D)) = 2^(6*(2*m+1))) :
    rootAt Q split i (Q.simple j*Q.simple i) ≤
      ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ := by
  let d := radicalSection Q split j hKj
  let V := simpleRemainder Q split j
  let σ := radicalHRepresentation Q split j hKj
  let F (t : Fin 5) := Additive (rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t) ⧸
    frattini (rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t)))
  let ρ (t : Fin 5) := rootAtCartanFrattiniRepresentation Q split
    (radicalRootKind i j t) (radicalRootWord Q i j t)
  let f (t : Fin 5) := radicalRootIntertwiner Q split hhex i j hij hKj t
  have hPhi : Nat.card (frattini V) = 2^(6*(2*m+1)) := by
    have he : Nat.card (⁅V,V⁆ : Subgroup (X ⧸ Q.D)) = Nat.card (frattini V) := by
      rw [←map_subtype_commutator,
        ←suzuki_radical_frattini_eq_commutator Q split hhex i j hij hm hm νi νj]
      exact Nat.card_congr ((frattini V).equivMapOfInjective V.subtype V.subtype_injective).symm.toEquiv
    exact he.symm.trans hcard
  have hcV : Nat.card V = 2^(10*(2*m+1)) := by
    rw [Nat.card_congr (radicalCoordinates Q split hhex i j hij).symm]
    simp only [Nat.card_prod,rootAt,card_rightConjugate,
      Nat.card_congr νi.toEquiv,Nat.card_congr νj.toEquiv,matrixRoot_card,←pow_add,←pow_mul]
    congr 1
    omega
  have hq : Nat.card (V ⧸ frattini V) =
      2^Module.finrank (ZMod 2) (Additive d.EffectiveCarrier) := by
    rw [←suzuki_radical_effectiveDenominator Q split j hKj]
    change Nat.card (Additive d.EffectiveCarrier) = _
    simpa only [Nat.card_zmod] using
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive d.EffectiveCarrier)
  have hdim : Module.finrank (ZMod 2) (Additive d.EffectiveCarrier) = 4*(2*m+1) := by
    have hh := (frattini V).index_mul_card
    change Nat.card (V ⧸ frattini V)*Nat.card (frattini V) = Nat.card V at hh
    rw [hq,hPhi,hcV,←pow_add] at hh
    have he := Nat.pow_right_injective (by decide : 2 ≤ 2) hh
    omega
  have hzero : f 2 = 0 := by
    by_contra hn
    have hir (t : Fin 5) : (ρ t).IsIrreducible :=
      (suzuki_radical_root_profile Q split i j hKi hKj hm hm μi μj νi νj t).1
    have hinj (t : Fin 5) : Function.Injective (f t) := by
      by_cases ht : t = 2
      · subst t
        let := hir 2
        exact (Representation.IsIrreducible.injective_or_eq_zero (f 2)).resolve_right hn
      · exact suzuki_nonmiddle_root_intertwiner_injective Q split hhex i j hij hKi hKj hm μi μj νi νj t ht
    have hcr : Representation.IsCompletelyReducible σ :=
      Representation.isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime σ (Or.inr (by
        rw [ringChar.eq (ZMod 2) 2]; exact ⟨Nat.prime_two,split.odd⟩))
    have hle := Representation.finrank_sum_le_of_distinct_kernels F ρ σ hir hcr
      (suzuki_radical_root_representation_kernels_distinct Q split hhex hcore i j hij hKi hKj hm μi μj νi νj) f hinj
    have hd (t : Fin 5) : Module.finrank (ZMod 2) (F t) = 2*m+1 := by
      have hh := (suzuki_radical_root_profile Q split i j hKi hKj hm hm μi μj νi νj t).2
      simpa only [ite_self] using hh
    simp only [hd,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hle
    change 5*(2*m+1) ≤ Module.finrank (ZMod 2) (Additive d.EffectiveCarrier) at hle
    rw [hdim] at hle
    omega
  intro x hx
  let a : rootAt Q split i (Q.simple j*Q.simple i) := ⟨x,hx⟩
  have hh := congrArg (fun g => g (Additive.ofMul (QuotientGroup.mk a))) hzero
  have hz : (QuotientGroup.mk' d.effectiveDenominator)
      (inclusion (radicalRoot_le Q split hhex i j hij 2) a) = 1 := congrArg Additive.toMul hh
  have hv := (QuotientGroup.eq_one_iff _).mp hz
  rw [suzuki_radical_effectiveDenominator Q split j hKj,
    suzuki_radical_frattini_eq_commutator Q split hhex i j hij hm hm νi νj] at hv
  rw [←map_subtype_commutator]
  exact mem_map_of_mem V.subtype hv

open scoped Pointwise
/-- The ordered source product with the full middle root and the four
nonmiddle Frattini subgroups. -/
@[expose] def radicalMiddleFrattiniProduct (i j : Fin 2) : Set (X ⧸ Q.D) :=
  (rootFrattiniAt Q split i 1 : Set (X ⧸ Q.D)) *
  (rootFrattiniAt Q split j (Q.simple i) : Set (X ⧸ Q.D)) *
  (rootAt Q split i (Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) *
  (rootFrattiniAt Q split j (Q.simple i*Q.simple j) : Set (X ⧸ Q.D)) *
  (rootFrattiniAt Q split i (Q.simple j) : Set (X ⧸ Q.D))

/-- Unique ordered coordinates identify the q⁶ derived radical with the
four root Frattini subgroups and the whole middle root, exactly as in (6C). -/
theorem suzuki_derived_large_order_product (hhex : rotationOrder Q = 6)
    (hcore : Q.tits.B.normalCore = ⊥) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m : ℕ} (hm : 0 < m)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup m)
    (hcard : Nat.card (⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ :
      Subgroup (X ⧸ Q.D)) = 2^(6*(2*m+1))) :
    ((⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) =
      radicalMiddleFrattiniProduct Q split i j := by
  let A := simpleRoot Q split i
  let B := rootAt Q split j (Q.simple i)
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let D := rootAt Q split j (Q.simple i*Q.simple j)
  let E := rootAt Q split i (Q.simple j)
  let J := ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆
  let F := frattini A × frattini B × C × frattini D × frattini E
  have hroot := suzuki_radical_root_frattini_le_derived Q split hhex i j hij hm hm νi νj
  have hA : (frattini A).map A.subtype ≤ J := by
    have hh := hroot 0
    change (frattini (rootAt Q split i 1)).map (rootAt Q split i 1).subtype ≤ J at hh
    rw [rootAt_one] at hh
    exact hh
  have hB : (frattini B).map B.subtype ≤ J := hroot 1
  have hC : C ≤ J := suzuki_middle_root_le_derived_of_large_order Q split hhex hcore i j hij hKi hKj hm μi μj νi νj hcard
  have hD : (frattini D).map D.subtype ≤ J := hroot 3
  have hE : (frattini E).map E.subtype ≤ J := hroot 4
  let f : F → J := fun z => ⟨(z.1.val : X ⧸ Q.D)*z.2.1.val*z.2.2.1*z.2.2.2.1.val*z.2.2.2.2.val,
    mul_mem (mul_mem (mul_mem (mul_mem
      (hA (mem_map_of_mem A.subtype z.1.property))
      (hB (mem_map_of_mem B.subtype z.2.1.property)))
      (hC z.2.2.1.property))
      (hD (mem_map_of_mem D.subtype z.2.2.2.1.property)))
      (hE (mem_map_of_mem E.subtype z.2.2.2.2.property))⟩
  have hf : Function.Injective f := by
    intro z y he
    have ht : (z.1.val,z.2.1.val,z.2.2.1,z.2.2.2.1.val,z.2.2.2.2.val) =
        (y.1.val,y.2.1.val,y.2.2.1,y.2.2.2.1.val,y.2.2.2.2.val) := by
      apply (radicalCoordinates Q split hhex i j hij).injective
      apply Subtype.ext
      rw [radicalCoordinates_apply,radicalCoordinates_apply]
      exact congrArg Subtype.val he
    exact Prod.ext (Subtype.ext (congrArg Prod.fst ht))
      (Prod.ext (Subtype.ext (congrArg (fun z => z.2.1) ht))
        (Prod.ext (congrArg (fun z => z.2.2.1) ht)
          (Prod.ext (Subtype.ext (congrArg (fun z => z.2.2.2.1) ht))
            (Subtype.ext (congrArg (fun z => z.2.2.2.2) ht)))))
  change Nat.card J = _ at hcard
  have hc : Nat.card F = Nat.card J := by
    have hcA : Nat.card (frattini A) = 2^(2*m+1) := by
      have hh := suzuki_rootAt_frattini_card Q split i hKi hm μi νi 1
      rw [rootAt_one] at hh
      exact hh
    change Nat.card (frattini A × frattini B × C × frattini D × frattini E) = _
    simp only [Nat.card_prod,hcA,
      show Nat.card (frattini B) = _ from suzuki_rootAt_frattini_card Q split j hKj hm μj νj _,
      show Nat.card C = (2^(2*m+1))^2 from by
        change Nat.card (rootAt Q split i (Q.simple j*Q.simple i)) = _
        rw [rootAt,card_rightConjugate,Nat.card_congr νi.toEquiv]; exact matrixRoot_card m,
      show Nat.card (frattini D) = _ from suzuki_rootAt_frattini_card Q split j hKj hm μj νj _,
      show Nat.card (frattini E) = _ from suzuki_rootAt_frattini_card Q split i hKi hm μi νi _,hcard]
    simp only [←pow_mul,←pow_add]
    congr 1
    omega
  have hsur := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf,hc⟩).surjective
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨⟨a,b,c,d,e⟩,he⟩ := hsur ⟨x,hx⟩
    have ha0 : (a.val : X ⧸ Q.D) ∈ rootFrattiniAt Q split i 1 := by
      unfold rootFrattiniAt
      rw [rootAt_one]
      exact mem_map_of_mem A.subtype a.property
    exact ⟨_,⟨_,⟨_,⟨_,ha0,_,mem_map_of_mem B.subtype b.property,rfl⟩,
      _,c.property,rfl⟩,_,mem_map_of_mem D.subtype d.property,rfl⟩,
        _,mem_map_of_mem E.subtype e.property,congrArg Subtype.val he⟩
  · rintro x ⟨abcd,⟨abc,⟨ab,⟨a,ha,b,hb,rfl⟩,c,hc,rfl⟩,d,hd,rfl⟩,e,he,rfl⟩
    have ha' : a ∈ (frattini A).map A.subtype := by
      unfold rootFrattiniAt at ha
      rw [rootAt_one] at ha
      exact ha
    exact mul_mem (mul_mem (mul_mem (mul_mem (hA ha') (hB hb)) (hC hc)) (hD hd)) (hE he)


/-- Both exact ordered derived-radical products in source (6C), together
with their orders. This does not yet assert the final Suzuki exclusion. -/
theorem suzuki_derived_product_alternatives (hhex : rotationOrder Q = 6)
    (hcore : Q.tits.B.normalCore = ⊥) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m : ℕ} (hm : 0 < m)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup m) :
    let D := ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆
    ((D : Set (X ⧸ Q.D)) = radicalRootFrattiniProduct Q split i j ∧
      Nat.card D = 2^(5*(2*m+1))) ∨
    ((D : Set (X ⧸ Q.D)) = radicalMiddleFrattiniProduct Q split i j ∧
      Nat.card D = 2^(6*(2*m+1))) := by
  dsimp only
  rcases suzuki_derived_radical_card Q split hhex i j hij hKi hKj hm μi μj νi νj with hc | hc
  · exact Or.inl ⟨suzuki_derived_small_order_product Q split hhex i j hij hKi hKj hm μi μj νi νj hc,hc⟩
  · exact Or.inr ⟨suzuki_derived_large_order_product Q split hhex hcore i j hij hKi hKj hm μi μj νi νj hc,hc⟩

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
