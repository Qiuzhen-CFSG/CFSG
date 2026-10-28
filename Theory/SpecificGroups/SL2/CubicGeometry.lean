module

public import Theory.SpecificGroups.SL2.BinaryTetrahedralQuotient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic


/-!
# Cubic-subgroup geometry of SL₂(3)

In the explicit binary tetrahedral group Q₈ ⋊ C₃, the conjugates of the
standard cubic generator by 1, I, J and IJ generate precisely the four
subgroups of order three. Small checked generator calculations show that
any two generate Q₈ ⋊ C₃ and that each cubic subgroup permutes the other
three transitively. The calculations range over elements and generator
words, never over all subsets or subgroups.

We transport this geometry through `binaryTetrahedralEquivSL` and then
through an actual equivalence with a subgroup of an arbitrary group.
Conjugation is the literal left conjugation x * y * x⁻¹ throughout.

This is the intrinsic SL₂(3) fact used in Aschbacher, *Sporadic Groups*
(1994), 47.5, printed p.263. The ambient local construction is separate.
-/

open GLS3.Chapter5.SchurPresentation Subgroup
namespace SL23CubicGeometry
private abbrev B := BinaryTetrahedral
private instance binaryFintype : Fintype B := Fintype.ofEquiv (QuaternionGroup 2 × Multiplicative (ZMod 3)) SemidirectProduct.equivProd.symm

private def gen : Fin 4 → B := ![binaryT, binaryI * binaryT * binaryI⁻¹,
  binaryJ * binaryT * binaryJ⁻¹, (binaryI * binaryJ) * binaryT * (binaryI * binaryJ)⁻¹]

private theorem gen_order (i : Fin 4) : orderOf (gen i) = 3 := by
  apply orderOf_eq_prime
  · fin_cases i <;> decide
  · fin_cases i <;> decide

private theorem cubic_elements : ∀ x : B, x ^ 3 = 1 → x ≠ 1 →
    ∃ i : Fin 4, x = gen i ∨ x = gen i ^ 2 := by decide

private theorem conjugate_generators : ∀ i j k : Fin 4, j ≠ i → k ≠ i → ∃ n : Fin 3,
    gen i ^ n.val * gen j * (gen i ^ n.val)⁻¹ = gen k ∨
    gen i ^ n.val * gen j * (gen i ^ n.val)⁻¹ = gen k ^ 2 := by decide

private theorem generator_words : ∀ i j : Fin 4, i ≠ j → ∀ t : Fin 3, ∃ a b c d : Fin 3,
    (![binaryI, binaryJ, binaryT] t) =
      gen i ^ a.val * gen j ^ b.val * gen i ^ c.val * gen j ^ d.val := by decide

private def cubic (i : Fin 4) : Subgroup B := zpowers (gen i)

private theorem cubic_card (i : Fin 4) : Nat.card (cubic i) = 3 := by
  exact (Nat.card_zpowers _).trans (gen_order i)

private theorem mem_cubic (i : Fin 4) (x : B) :
    x ∈ cubic i ↔ x = 1 ∨ x = gen i ∨ x = gen i ^ 2 := by
  change x ∈ zpowers (gen i) ↔ _
  rw [mem_zpowers_iff_mem_range_orderOf, gen_order]
  simp [show Finset.range 3 = {0, 1, 2} by decide]

private theorem cubic_injective : Function.Injective cubic := by
  intro i j hij
  have h : gen i ∈ cubic j := hij ▸ mem_zpowers (gen i)
  rw [mem_cubic] at h
  have hn : ∀ i j : Fin 4, gen i = 1 ∨ gen i = gen j ∨ gen i = gen j ^ 2 → i = j := by
    decide
  exact hn i j h

private theorem cubic_complete (X : Subgroup B) (hX : Nat.card X = 3) :
    ∃ i : Fin 4, X = cubic i := by
  have hcyc : IsCyclic X := isCyclic_of_prime_card hX
  obtain ⟨x, hx⟩ := X.isCyclic_iff_exists_zpowers_eq_top.mp hcyc
  have ho : orderOf x = 3 := by rw [← Nat.card_zpowers, hx, hX]
  obtain ⟨i, hi | hi⟩ := cubic_elements x
    (orderOf_eq_prime_iff.mp ho).1 (orderOf_eq_prime_iff.mp ho).2
  · exact ⟨i, hx.symm.trans (congrArg zpowers hi)⟩
  · refine ⟨i, (eq_of_le_of_card_ge ?_ ?_)⟩
    · rw [← hx, hi]
      exact zpowers_le.mpr ((cubic i).pow_mem (mem_zpowers (gen i)) 2)
    · rw [cubic_card, hX]

private theorem top_of_generators (H : Subgroup B) (hI : binaryI ∈ H)
    (hJ : binaryJ ∈ H) (hT : binaryT ∈ H) : H = ⊤ := by
  have hl (x : QuaternionGroup 2) : SemidirectProduct.inl x ∈ H := by
    rcases x with i | i
    · rw [← ZMod.natCast_zmod_val i, ← QuaternionGroup.a_one_pow, map_pow]
      exact H.pow_mem hI _
    · have hx : QuaternionGroup.xa i = QuaternionGroup.xa 0 * QuaternionGroup.a i := by
        simp [QuaternionGroup.xa_mul_a]
      rw [hx, map_mul]
      apply H.mul_mem hJ
      rw [← ZMod.natCast_zmod_val i, ← QuaternionGroup.a_one_pow, map_pow]
      exact H.pow_mem hI _
  have hr (k : Multiplicative (ZMod 3)) : SemidirectProduct.inr k ∈ H := by
    change ZMod 3 at k
    fin_cases k
    · exact H.one_mem
    · exact hT
    · exact H.pow_mem hT 2
  apply top_unique
  intro x _
  rw [← SemidirectProduct.inl_left_mul_inr_right x]
  exact H.mul_mem (hl x.left) (hr x.right)

private theorem cubic_sup (i j : Fin 4) (h : i ≠ j) : cubic i ⊔ cubic j = ⊤ := by
  have hm (t : Fin 3) : ![binaryI, binaryJ, binaryT] t ∈ cubic i ⊔ cubic j := by
    obtain ⟨a, b, c, d, he⟩ := generator_words i j h t
    rw [he]
    exact (cubic i ⊔ cubic j).mul_mem
      ((cubic i ⊔ cubic j).mul_mem
        ((cubic i ⊔ cubic j).mul_mem
          ((show cubic i ≤ cubic i ⊔ cubic j from le_sup_left) ((cubic i).pow_mem (mem_zpowers _) _))
          ((show cubic j ≤ cubic i ⊔ cubic j from le_sup_right) ((cubic j).pow_mem (mem_zpowers _) _)))
        ((show cubic i ≤ cubic i ⊔ cubic j from le_sup_left) ((cubic i).pow_mem (mem_zpowers _) _)))
      ((show cubic j ≤ cubic i ⊔ cubic j from le_sup_right) ((cubic j).pow_mem (mem_zpowers _) _))
  exact top_of_generators _ (hm 0) (hm 1) (hm 2)

private theorem cubic_transitive (i j k : Fin 4) (hj : j ≠ i) (hk : k ≠ i) :
    ∃ x : cubic i, (cubic j).map (MulAut.conj (x : B)).toMonoidHom = cubic k := by
  obtain ⟨n, hn⟩ := conjugate_generators i j k hj hk
  refine ⟨⟨gen i ^ n.val, (cubic i).pow_mem (mem_zpowers _) _⟩,
    eq_of_le_of_card_ge ?_ ?_⟩
  · change (zpowers (gen j)).map _ ≤ cubic k
    rw [MonoidHom.map_zpowers]
    apply zpowers_le.mpr
    change gen i ^ n.val * gen j * (gen i ^ n.val)⁻¹ ∈ cubic k
    rw [mem_cubic]
    exact Or.inr hn
  · rw [card_map_of_injective (MulAut.conj _).injective, cubic_card, cubic_card]

variable {G : Type*} [Group G]

private theorem geometry_of_injective (f : B →* G) (hf : Function.Injective f)
    (X : Subgroup G) (hXL : X ≤ f.range) (hX : Nat.card X = 3) :
    Nat.card {Y : Subgroup G // Y ≤ f.range ∧ Nat.card Y = 3 ∧ Y ≠ X} = 3 ∧
    (∀ Y : {Y : Subgroup G // Y ≤ f.range ∧ Nat.card Y = 3 ∧ Y ≠ X},
      X ⊔ Y.val = f.range) ∧
    (∀ Y W : {Y : Subgroup G // Y ≤ f.range ∧ Nat.card Y = 3 ∧ Y ≠ X},
      ∃ x : X, Y.val.map (MulAut.conj (x : G)).toMonoidHom = W.val) := by
  classical
  have complete (Y : Subgroup G) (hYL : Y ≤ f.range) (hY : Nat.card Y = 3) :
      ∃ j : Fin 4, Y = (cubic j).map f := by
    have hm : (Y.comap f).map f = Y := map_comap_eq_self hYL
    have hc : Nat.card (Y.comap f) = 3 := by
      rw [← card_map_of_injective hf, hm, hY]
    obtain ⟨j, hj⟩ := cubic_complete (Y.comap f) hc
    exact ⟨j, hm.symm.trans (congrArg (Subgroup.map f) hj)⟩
  obtain ⟨i, rfl⟩ := complete X hXL hX
  have hinj : Function.Injective (fun j => (cubic j).map f) :=
    (map_injective hf).comp cubic_injective
  let v : {j : Fin 4 // j ≠ i} →
      {Y : Subgroup G // Y ≤ f.range ∧ Nat.card Y = 3 ∧ Y ≠ (cubic i).map f} :=
    fun j => ⟨(cubic j).map f, map_le_range _ _, by
      rw [card_map_of_injective hf, cubic_card], fun he => j.property (hinj he)⟩
  have hv : Function.Bijective v := by
    constructor
    · intro j k he
      exact Subtype.ext (hinj (congrArg Subtype.val he))
    · intro Y
      obtain ⟨j, hj⟩ := complete Y.val Y.property.1 Y.property.2.1
      refine ⟨⟨j, ?_⟩, Subtype.ext hj.symm⟩
      intro he
      exact Y.property.2.2 (hj.trans (congrArg (fun t => (cubic t).map f) he))
  refine ⟨?_, ?_, ?_⟩
  · rw [← Nat.card_congr (Equiv.ofBijective v hv), Nat.card_eq_fintype_card]
    fin_cases i <;> decide
  · intro Y
    obtain ⟨j, hj⟩ := complete Y.val Y.property.1 Y.property.2.1
    have hji : j ≠ i := fun he => Y.property.2.2 (hj.trans (congrArg (fun t => (cubic t).map f) he))
    rw [hj, ← Subgroup.map_sup, cubic_sup i j hji.symm, ← MonoidHom.range_eq_map]
  · intro Y W
    obtain ⟨j, hj⟩ := complete Y.val Y.property.1 Y.property.2.1
    obtain ⟨k, hk⟩ := complete W.val W.property.1 W.property.2.1
    have hji : j ≠ i := fun he => Y.property.2.2 (hj.trans (congrArg (fun t => (cubic t).map f) he))
    have hki : k ≠ i := fun he => W.property.2.2 (hk.trans (congrArg (fun t => (cubic t).map f) he))
    obtain ⟨x, hx⟩ := cubic_transitive i j k hji hki
    refine ⟨⟨f x, mem_map_of_mem _ x.property⟩, ?_⟩
    rw [hj, hk]
    have hcomm : (MulAut.conj (f x)).toMonoidHom.comp f =
        f.comp (MulAut.conj (x : B)).toMonoidHom := by
      ext y
      simp [MulAut.conj_apply]
    rw [map_map, hcomm, ← map_map, hx]

/-- The three other cubic subgroups in an actual SL₂(3) subgroup: they each
 generate that subgroup with X, and X conjugates them transitively. -/
public theorem geometry_of_equiv (L X : Subgroup G)
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (hXL : X ≤ L) (hX : Nat.card X = 3) :
    Nat.card {Y : Subgroup G // Y ≤ L ∧ Nat.card Y = 3 ∧ Y ≠ X} = 3 ∧
    (∀ Y : {Y : Subgroup G // Y ≤ L ∧ Nat.card Y = 3 ∧ Y ≠ X}, X ⊔ Y.val = L) ∧
    (∀ Y W : {Y : Subgroup G // Y ≤ L ∧ Nat.card Y = 3 ∧ Y ≠ X},
      ∃ x : X, Y.val.map (MulAut.conj (x : G)).toMonoidHom = W.val) := by
  let f : B →* G := L.subtype.comp (binaryTetrahedralEquivSL.trans e.symm).toMonoidHom
  have hf : Function.Injective f :=
    L.subtype_injective.comp (binaryTetrahedralEquivSL.trans e.symm).injective
  have hr : f.range = L := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (binaryTetrahedralEquivSL.trans e.symm).surjective,
      ← MonoidHom.range_eq_map,
      L.range_subtype]
  have h := geometry_of_injective f hf X (hr.symm ▸ hXL) hX
  rw [hr] at h
  exact h


/-- Intrinsic cubic geometry for the literal matrix group SL₂(ZMod 3). -/
public theorem geometry
    (X : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)))
    (hX : Nat.card X = 3) :
    Nat.card {Y : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) //
      Y ≤ ⊤ ∧ Nat.card Y = 3 ∧ Y ≠ X} = 3 ∧
    (∀ Y : {Y : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) //
      Y ≤ ⊤ ∧ Nat.card Y = 3 ∧ Y ≠ X}, X ⊔ Y.val = ⊤) ∧
    (∀ Y W : {Y : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) //
      Y ≤ ⊤ ∧ Nat.card Y = 3 ∧ Y ≠ X},
      ∃ x : X, Y.val.map (MulAut.conj (x : Matrix.SpecialLinearGroup
        (Fin 2) (ZMod 3))).toMonoidHom = W.val) :=
  geometry_of_equiv ⊤ X Subgroup.topEquiv le_top hX

end SL23CubicGeometry
