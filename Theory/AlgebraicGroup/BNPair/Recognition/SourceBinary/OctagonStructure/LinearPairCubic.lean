module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.LinearPairCartan

/-!
# A cubic Cartan actor separates the two linear root families

When the first binary degree is odd and the other is even, the second
Cartan image supplies an element of order three in the actual full Cartan.
The first root-action images have order prime to three, so this element
centralizes every root in that family. The opposite root-action kernels
also have order prime to three, by the exact two-panel injection. The
regular cyclic action therefore makes the same element fixed-point-free
on every opposite root.

A single cubic element suffices for the centralizer calculation in
Fong--Seitz I (6G), printed p.49: it has the same root fixed groups as the
source plus-prime Hall subgroup. No assertion about the later rank-one
product or terminal contradiction is made here. The CFSG application
supplies both natural markings and the actual root orders.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure (rootAt)
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- Conjugating a root preserves the order of its exact Cartan action kernel. -/
theorem rootAction_kernel_card (i : Fin 2) (w : Weyl Q) :
    Nat.card (rootAction Q split i w).ker = Nat.card (cartanPanelMap Q i).ker := by
  have hi := (rootAction Q split i w).ker.card_mul_index
  have hj := (cartanPanelMap Q i).ker.card_mul_index
  rw [index_ker,Nat.card_congr (rootActionImageEquiv Q split i w).toEquiv] at hi
  rw [index_ker] at hj
  exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos) (hi.trans hj.symm)

private theorem kernel_card_coprime_three
    (i j : Fin 2) (hij : i ≠ j) (a : ℕ) (ha : Odd a)
    (μi : (Endpoint Q i ⧸ panelKernel Q i) ≃* PSL2BinaryMatrixGroup a)
    (Ti : Sylow 2 (PSL2BinaryMatrixGroup a))
    (hBi : (quotientBorel Q i).map μi.toMonoidHom = normalizer (Ti : Set _))
    (s : ∀ k, RootReflection Q split k) (hcore : Q.tits.B.normalCore = ⊥)
    (w : Weyl Q) : Nat.Coprime 3 (Nat.card (rootAction Q split j w).ker) := by
  rw [rootAction_kernel_card]
  have hd := panelKernel_card_dvd_other Q split j i hij.symm s hcore
  rw [linear_cartanImage_card Q split i a ha.pos μi Ti hBi (s i)] at hd
  exact (Nat.BinaryTorusParity.coprime_three_sub_one ha).of_dvd_right hd


/-- Every cubic Cartan element centralizes all conjugates of an odd-degree linear root. -/
theorem cubic_centralizes_odd_root
    (i : Fin 2) (a : ℕ) (ha : Odd a)
    (μi : (Endpoint Q i ⧸ panelKernel Q i) ≃* PSL2BinaryMatrixGroup a)
    (Ti : Sylow 2 (PSL2BinaryMatrixGroup a))
    (hBi : (quotientBorel Q i).map μi.toMonoidHom = normalizer (Ti : Set _))
    (s : RootReflection Q split i)
    (c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) (hc : c^3 = 1)
    (w : Weyl Q) :
    (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) := by
  let f := rootAction Q split i w
  let y : f.range := ⟨f c,⟨c,rfl⟩⟩
  have h3 : y^3 = 1 := by
    apply Subtype.ext
    change (f c)^3 = 1
    rw [←map_pow,hc,map_one]
  have hcard : Nat.card f.range = 2^a-1 := by
    rw [Nat.card_congr (rootActionImageEquiv Q split i w).toEquiv]
    exact linear_cartanImage_card Q split i a ha.pos μi Ti hBi s
  have hcop : Nat.Coprime 3 (Nat.card f.range) := by
    rw [hcard]; exact Nat.BinaryTorusParity.coprime_three_sub_one ha
  have hy : y = 1 := hcop.symm.pow_left_bijective.injective (h3.trans (one_pow 3).symm)
  have hk : c ∈ f.ker := congrArg Subtype.val hy
  change c ∈ (RootAction.action _ _ _).ker at hk
  rw [RootAction.action_kernel] at hk
  exact hk

/-- The other natural linear root has no nonidentity point fixed by a cubic Cartan element. -/
theorem cubic_fixed_free_other_root
    (i j : Fin 2) (hij : i ≠ j) (a b : ℕ) (ha : Odd a) (hb : 0 < b)
    (μi : (Endpoint Q i ⧸ panelKernel Q i) ≃* PSL2BinaryMatrixGroup a)
    (Ti : Sylow 2 (PSL2BinaryMatrixGroup a))
    (hBi : (quotientBorel Q i).map μi.toMonoidHom = normalizer (Ti : Set _))
    (μj : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL2BinaryMatrixGroup b)
    (Tj : Sylow 2 (PSL2BinaryMatrixGroup b))
    (hBj : (quotientBorel Q j).map μj.toMonoidHom = normalizer (Tj : Set _))
    (hE : IsElementaryAbelian 2 (simpleRoot Q split j))
    (hcard : Nat.card (simpleRoot Q split j) = 2^b)
    (s : ∀ k, RootReflection Q split k) (hcore : Q.tits.B.normalCore = ⊥)
    (c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) (hc : orderOf c = 3)
    (w : Weyl Q) (x : rootAt Q split j w)
    (hx : rootAction Q split j w c x = x) : x = 1 := by
  by_contra hx1
  let f := rootAction Q split j w
  let e := RootAction.conjugateEquiv (simpleRoot Q split j) (representative w)
  let := hE
  let : IsElementaryAbelian 2 (rootAt Q split j w) :=
    IsElementaryAbelian.of_injective e.toMonoidHom e.injective
  let : IsCyclic f.range := (rootActionImageEquiv Q split j w).isCyclic.mpr
    (linear_cartanImage_cyclic Q split j b hb μj Tj hBj (s j))
  have him : Nat.card f.range = 2^b-1 := by
    rw [Nat.card_congr (rootActionImageEquiv Q split j w).toEquiv]
    exact linear_cartanImage_card Q split j b hb μj Tj hBj (s j)
  have hroot : Nat.card (rootAt Q split j w) = 2^b := (Nat.card_congr e.toEquiv).trans hcard
  obtain ⟨z,hz,hu⟩ := RootAction.regular_of_card f.range.subtype f.range.subtype_injective
    hb him hroot x x hx1 hx1
  have heq : (⟨f c,⟨c,rfl⟩⟩ : f.range) = 1 := (hu _ hx).trans (hu 1 (by simp)).symm
  have hk : c ∈ f.ker := congrArg Subtype.val heq
  let cK : f.ker := ⟨c,hk⟩
  have h3 : cK^3 = 1 := Subtype.ext (by change c^3 = 1; rw [←hc,pow_orderOf_eq_one])
  have hcop := kernel_card_coprime_three Q split i j hij a ha μi Ti hBi s hcore w
  have hc1 : cK = 1 := hcop.symm.pow_left_bijective.injective (h3.trans (one_pow 3).symm)
  have hcone : c = 1 := congrArg Subtype.val hc1
  rw [hcone,orderOf_one] at hc
  omega

/-- An even-degree linear panel supplies an actual cubic element of the whole Cartan. -/
theorem exists_cubic_cartan
    (j : Fin 2) (b : ℕ) (hb : 0 < b) (heven : Even b)
    (μj : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL2BinaryMatrixGroup b)
    (Tj : Sylow 2 (PSL2BinaryMatrixGroup b))
    (hBj : (quotientBorel Q j).map μj.toMonoidHom = normalizer (Tj : Set _))
    (s : RootReflection Q split j) :
    ∃ c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)), orderOf c = 3 := by
  have hd : 3 ∣ Nat.card (cartanPanelMap Q j).range := by
    rw [linear_cartanImage_card Q split j b hb μj Tj hBj s]
    exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff b).mpr heven
  exact exists_prime_orderOf_dvd_card' 3 (hd.trans (card_range_dvd (cartanPanelMap Q j)))

/-- The opposite linear root has trivial intersection with the cubic centralizer. -/
theorem cubic_root_centralizer_eq_bot
    (i j : Fin 2) (hij : i ≠ j) (a b : ℕ) (ha : Odd a) (hb : 0 < b)
    (μi : (Endpoint Q i ⧸ panelKernel Q i) ≃* PSL2BinaryMatrixGroup a)
    (Ti : Sylow 2 (PSL2BinaryMatrixGroup a))
    (hBi : (quotientBorel Q i).map μi.toMonoidHom = normalizer (Ti : Set _))
    (μj : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL2BinaryMatrixGroup b)
    (Tj : Sylow 2 (PSL2BinaryMatrixGroup b))
    (hBj : (quotientBorel Q j).map μj.toMonoidHom = normalizer (Tj : Set _))
    (hE : IsElementaryAbelian 2 (simpleRoot Q split j))
    (hcard : Nat.card (simpleRoot Q split j) = 2^b)
    (s : ∀ k, RootReflection Q split k) (hcore : Q.tits.B.normalCore = ⊥)
    (c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) (hc : orderOf c = 3)
    (w : Weyl Q) :
    rootAt Q split j w ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have hfix : rootAction Q split j w c ⟨x,hx.1⟩ = ⟨x,hx.1⟩ := by
    apply Subtype.ext
    change (c : X ⧸ Q.D)*x*(c : X ⧸ Q.D)⁻¹ = x
    rw [← mem_centralizer_singleton_iff.mp hx.2, mul_assoc, mul_inv_cancel, mul_one]
  exact congrArg Subtype.val (cubic_fixed_free_other_root Q split i j hij a b ha hb
    μi Ti hBi μj Tj hBj hE hcard s hcore c hc w ⟨x,hx.1⟩ hfix)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure

