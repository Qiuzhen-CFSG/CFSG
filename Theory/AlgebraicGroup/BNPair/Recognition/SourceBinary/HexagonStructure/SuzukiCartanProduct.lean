module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiCartanIntersection
public import Theory.GroupTheory.NormalizedSupCard
/-!
# The full Cartan and root-action kernels in a regular Suzuki hexagon

The disjoint rank-one Cartans commute and each has order q-1. Their join
therefore has order (q-1)². Joint panel faithfulness embeds H in the product
of its two images, each also of order q-1, proving that the join is all H.
The index formula now gives order q-1 for the kernel of H on every literal
Weyl-conjugate root, so each of the five radical root kernels is nontrivial.

Source: Fong--Seitz I (6C), printed p.41, immediately after the rank-one
Cartan intersection. These are the actual actions used in the subsequent
constituent argument; the radical commutator exclusion remains to be proved.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem ambient_rankOne_cartan_card (i : Fin 2)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    {m : ℕ} (hm : 0 < m) (μ : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (ν : simpleRoot Q split i ≃* SuzukiRootSubgroup m) :
    Nat.card ((Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split i : Subgroup (X ⧸ Q.D)) =
      2^(2*m+1)-1 := by
  let e : ((Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split i : Subgroup (X ⧸ Q.D)) ≃*
      (Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split i) := {
    toFun c := ⟨⟨c,c.property.2⟩,c.property.1⟩
    invFun c := ⟨c,⟨c.property,c.val.property⟩⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  exact (Nat.card_congr e.toEquiv).trans
    (suzuki_rankOne_cartan_cyclic_card Q split i hKi hm μ ν
      (UnitarySource.actorReflection Q split i)).2

/-- The full Cartan is the internal product of the two actual rank-one
Cartans, and has order (q-1)². Joint panel faithfulness supplies the upper
bound; the proved disjoint intersection supplies the reverse bound. -/
theorem suzuki_rankOne_cartans_generate (hhex : rotationOrder Q = 6)
    (hcore : Q.tits.B.normalCore = ⊥) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m : ℕ} (hm : 0 < m)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup m) :
    (((Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split i) ⊔
      ((Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split j) = Q.tits.B ⊓ Q.tits.N) ∧
      Nat.card (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) = (2^(2*m+1)-1)^2 := by
  let H := Q.tits.B ⊓ Q.tits.N
  let C := H ⊓ rankOne Q split i
  let D := H ⊓ rankOne Q split j
  let := split.abelian
  have hnorm : D ≤ normalizer (C : Set (X ⧸ Q.D)) :=
    ((show D ≤ H from inf_le_left).trans
      ((Subgroup.le_centralizer H).trans (centralizer_le (show C ≤ H from inf_le_left)))).trans
        (_root_.centralizer_le_normalizer C)
  have hdis : Disjoint C D := disjoint_iff.mpr
    (suzuki_rankOne_cartans_disjoint Q split hhex i j hij hKi hKj hm μi μj νi νj)
  have hprod := card_sup_eq_mul_of_normalizes_of_disjoint C D hnorm hdis
  have hC := ambient_rankOne_cartan_card Q split i hKi hm μi νi
  have hD := ambient_rankOne_cartan_card Q split j hKj hm μj νj
  change Nat.card C = _ at hC
  change Nat.card D = _ at hD
  rw [hC,hD,←pow_two] at hprod
  have him (k : Fin 2) : Nat.card (cartanPanelMap Q k).range = 2^(2*m+1)-1 := by
    by_cases hk : k = i
    · subst k
      exact suzuki_cartan_panel_image_card Q split i hKi hm μi νi
    · have he : k = j := by omega
      subst k
      exact suzuki_cartan_panel_image_card Q split j hKj hm μj νj
  have hupper := Nat.card_le_card_of_injective _
    (cartanImagePair_injective Q split (UnitarySource.actorReflection Q split) hcore)
  change Nat.card H ≤ Nat.card ((cartanPanelMap Q 0).range × (cartanPanelMap Q 1).range) at hupper
  rw [Nat.card_prod,him,him,←pow_two] at hupper
  have he : C ⊔ D = H := eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left)
    (hupper.trans_eq hprod.symm)
  refine ⟨he,?_⟩
  change Nat.card H = _
  rw [←he]
  exact hprod

/-- Every conjugate root has an actual Cartan-action kernel of order q-1.
This uses the full source H, not a freely chosen abstract torus. -/
theorem suzuki_rootAction_kernel_card (hhex : rotationOrder Q = 6)
    (hcore : Q.tits.B.normalCore = ⊥) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m : ℕ} (hm : 0 < m)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup m) (k : Fin 2) (w : Weyl Q) :
    Nat.card (rootAction Q split k w).ker = 2^(2*m+1)-1 := by
  have hH := (suzuki_rankOne_cartans_generate Q split hhex hcore i j hij hKi hKj
    hm μi μj νi νj).2
  have him : Nat.card (rootAction Q split k w).range = 2^(2*m+1)-1 := by
    rw [Nat.card_congr (rootActionImageEquiv Q split k w).toEquiv]
    by_cases hk : k = i
    · subst k
      exact suzuki_cartan_panel_image_card Q split i hKi hm μi νi
    · have he : k = j := by omega
      subst k
      exact suzuki_cartan_panel_image_card Q split j hKj hm μj νj
  have hprod := (rootAction Q split k w).ker.index_mul_card
  rw [index_ker,him,hH,pow_two] at hprod
  have hpos : 0 < 2^(2*m+1)-1 := by
    rw [←ambient_rankOne_cartan_card Q split i hKi hm μi νi]
    exact Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos hprod

/-- The nontrivial kernels asserted in (6C), for all literal Weyl-conjugate
roots and hence for every factor in the five-root radical coordinates. -/
theorem suzuki_rootAction_kernel_ne_bot (hhex : rotationOrder Q = 6)
    (hcore : Q.tits.B.normalCore = ⊥) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m : ℕ} (hm : 0 < m)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup m) (k : Fin 2) (w : Weyl Q) :
    (rootAction Q split k w).ker ≠ ⊥ := by
  have hc := suzuki_rootAction_kernel_card Q split hhex hcore i j hij hKi hKj
    hm μi μj νi νj k w
  intro he
  rw [he,card_bot] at hc
  have hp : (2 : ℕ)^3 ≤ 2^(2*m+1) := Nat.pow_le_pow_right (by decide) (by omega)
  norm_num at hp
  omega

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
