module

public import Theory.GroupTheory.PairedInvolutiveExtension
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Centralizers in a paired involutive extension

For an involutive automorphism α of K, the extension of K × K by simultaneous
α and factor interchange has three distinguished involutions. Their fixed
coordinate equations identify the swap and graph-swap centralizers with
K × C₂ × C₂, and the graph centralizer with Fix(α)² × C₂ × C₂ as sets.
The same coordinates construct the extension of any α-stable subgroup D
and identify its intersection with the swap centralizer.

These formulas supply the local centralizer orders in Aschbacher--Smith,
proof of 2.4.34, printed p.548 of the 1 March 2004 manuscript.
-/

@[expose] public section
namespace Theory.GroupTheory.PairedInvolutiveExtension
variable {K : Type*} [Group K] (α : MulAut K) (hα : Function.Involutive α)
private theorem mk_eq_iff (a b c d : K) (p q r s : Bit) :
    mk α hα a b p q = mk α hα c d r s ↔ a = c ∧ b = d ∧ p = r ∧ q = s := by
  simp [mk, SemidirectProduct.ext_iff, Prod.ext_iff, and_assoc]
theorem mem_centralizer_swap_mk (a b : K) (p q : Bit) :
    mk α hα a b p q ∈ Subgroup.centralizer {swap α hα} ↔ a = b := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 : action α hα (p,q) (1,1) = (1,1) := map_one _
  simp [h1,swap, mk_mul, mk_eq_iff, mul_comm, eq_comm]
theorem mem_centralizer_graphSwap_mk (a b : K) (p q : Bit) :
    mk α hα a b p q ∈ Subgroup.centralizer {graphSwap α hα} ↔ b = α a := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  simp only [graphSwap, mk_mul, action_graphSwap]
  have h1 : action α hα (p,q) (1,1) = (1,1) := map_one _
  simp only [h1, mul_one, one_mul, mk_eq_iff, mul_comm p on, mul_comm q on, and_true]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨by rw [h, hα], h⟩
theorem mem_centralizer_graph_mk (a b : K) (p q : Bit) :
    mk α hα a b p q ∈ Subgroup.centralizer {graph α hα} ↔
      a ∈ α.fixedSubgroup ∧ b ∈ α.fixedSubgroup := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 : action α hα (p,q) (1,1) = (1,1) := map_one _
  simp [h1,graph, mk_mul, mk_eq_iff, mul_comm, MulAut.mem_fixedSubgroup, eq_comm]
theorem card_bit : Nat.card Bit = 2 := by simp [Bit, Nat.card_eq_fintype_card]
private theorem action_mem (D : Subgroup K) (hD : ∀ a ∈ D, α a ∈ D)
    (a b : K) (p q : Bit) (ha : a ∈ D) (hb : b ∈ D) :
    (action α hα (p,q) (a,b)).1 ∈ D ∧ (action α hα (p,q) (a,b)).2 ∈ D := by
  rcases bit_cases p with rfl | rfl <;> rcases bit_cases q with rfl | rfl <;>
    simp [ha, hb, hD _ ha, hD _ hb]
/-- The paired extension of an α-stable subgroup. -/
def subgroup (D : Subgroup K) (hD : ∀ a ∈ D, α a ∈ D) : Subgroup (Model α hα) where
  carrier := {x | x.left.1 ∈ D ∧ x.left.2 ∈ D}
  one_mem' := ⟨D.one_mem, D.one_mem⟩
  mul_mem' {x y} hx hy := by
    obtain ⟨hy1,hy2⟩ := action_mem α hα D hD y.left.1 y.left.2 x.right.1 x.right.2 hy.1 hy.2
    exact ⟨D.mul_mem hx.1 hy1, D.mul_mem hx.2 hy2⟩
  inv_mem' {x} hx := by
    exact action_mem α hα D hD x.left.1⁻¹ x.left.2⁻¹ x.right.1⁻¹ x.right.2⁻¹
      (D.inv_mem hx.1) (D.inv_mem hx.2)
@[simp] theorem mem_subgroup (D : Subgroup K) (hD : ∀ a ∈ D, α a ∈ D)
    (x : Model α hα) : x ∈ subgroup α hα D hD ↔ x.left.1 ∈ D ∧ x.left.2 ∈ D := Iff.rfl

/-- Coordinates of the paired extension of a stable subgroup. -/
def subgroupEquiv (D : Subgroup K) (hD : ∀ a ∈ D, α a ∈ D) :
    subgroup α hα D hD ≃ (D × D) × (Bit × Bit) where
  toFun x := ((⟨x.1.left.1,x.2.1⟩,⟨x.1.left.2,x.2.2⟩), x.1.right)
  invFun x := ⟨mk α hα x.1.1 x.1.2 x.2.1 x.2.2, x.1.1.2, x.1.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
theorem mem_centralizer_swap (x : Model α hα) :
    x ∈ Subgroup.centralizer {swap α hα} ↔ x.left.1 = x.left.2 := by
  rcases x with ⟨⟨a,b⟩,⟨p,q⟩⟩
  exact mem_centralizer_swap_mk α hα a b p q

theorem mem_centralizer_graphSwap (x : Model α hα) :
    x ∈ Subgroup.centralizer {graphSwap α hα} ↔ x.left.2 = α x.left.1 := by
  rcases x with ⟨⟨a,b⟩,⟨p,q⟩⟩
  exact mem_centralizer_graphSwap_mk α hα a b p q

theorem mem_centralizer_graph (x : Model α hα) :
    x ∈ Subgroup.centralizer {graph α hα} ↔
      x.left.1 ∈ α.fixedSubgroup ∧ x.left.2 ∈ α.fixedSubgroup := by
  rcases x with ⟨⟨a,b⟩,⟨p,q⟩⟩
  exact mem_centralizer_graph_mk α hα a b p q

/-- The swap centralizer has arbitrary first coordinate and actor bits. -/
def centralizerSwapEquiv : Subgroup.centralizer {swap α hα} ≃ K × (Bit × Bit) where
  toFun x := (x.1.left.1, x.1.right)
  invFun x := ⟨mk α hα x.1 x.1 x.2.1 x.2.2,
    (mem_centralizer_swap_mk α hα _ _ _ _).mpr rfl⟩
  left_inv x := by
    apply Subtype.ext
    exact SemidirectProduct.ext (Prod.ext rfl ((mem_centralizer_swap α hα x).mp x.2)) rfl
  right_inv _ := rfl

/-- The graph-swap centralizer has second coordinate determined by the first. -/
def centralizerGraphSwapEquiv : Subgroup.centralizer {graphSwap α hα} ≃ K × (Bit × Bit) where
  toFun x := (x.1.left.1, x.1.right)
  invFun x := ⟨mk α hα x.1 (α x.1) x.2.1 x.2.2,
    (mem_centralizer_graphSwap_mk α hα _ _ _ _).mpr rfl⟩
  left_inv x := by
    apply Subtype.ext
    exact SemidirectProduct.ext (Prod.ext rfl ((mem_centralizer_graphSwap α hα x).mp x.2).symm) rfl
  right_inv _ := rfl

/-- Both coordinates of the graph centralizer lie in the fixed subgroup. -/
def centralizerGraphEquiv : Subgroup.centralizer {graph α hα} ≃
    (α.fixedSubgroup × α.fixedSubgroup) × (Bit × Bit) where
  toFun x := ((⟨x.1.left.1, ((mem_centralizer_graph α hα x).mp x.2).1⟩,
    ⟨x.1.left.2, ((mem_centralizer_graph α hα x).mp x.2).2⟩), x.1.right)
  invFun x := ⟨mk α hα x.1.1 x.1.2 x.2.1 x.2.2,
    (mem_centralizer_graph_mk α hα _ _ _ _).mpr ⟨x.1.1.2, x.1.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_centralizer_swap : Nat.card (Subgroup.centralizer {swap α hα}) = Nat.card K * 4 := by
  rw [Nat.card_congr (centralizerSwapEquiv α hα), Nat.card_prod, Nat.card_prod, card_bit]

theorem card_centralizer_graphSwap : Nat.card (Subgroup.centralizer {graphSwap α hα}) = Nat.card K * 4 := by
  rw [Nat.card_congr (centralizerGraphSwapEquiv α hα), Nat.card_prod, Nat.card_prod, card_bit]

theorem card_centralizer_graph :
    Nat.card (Subgroup.centralizer {graph α hα}) = Nat.card α.fixedSubgroup ^ 2 * 4 := by
  rw [Nat.card_congr (centralizerGraphEquiv α hα), Nat.card_prod, Nat.card_prod, Nat.card_prod, card_bit]
  simp [pow_two]

theorem card_subgroup (D : Subgroup K) (hD : ∀ a ∈ D, α a ∈ D) :
    Nat.card (subgroup α hα D hD) = Nat.card D ^ 2 * 4 := by
  rw [Nat.card_congr (subgroupEquiv α hα D hD), Nat.card_prod, Nat.card_prod, Nat.card_prod, card_bit]
  simp [pow_two]

/-- The swap centralizer inside the paired subgroup has one coordinate in D. -/
def subgroupInfCentralizerSwapEquiv (D : Subgroup K) (hD : ∀ a ∈ D, α a ∈ D) :
    (subgroup α hα D hD ⊓ Subgroup.centralizer {swap α hα} : Subgroup (Model α hα)) ≃
      D × (Bit × Bit) where
  toFun x := (⟨x.1.left.1, x.2.1.1⟩, x.1.right)
  invFun x := ⟨mk α hα x.1 x.1 x.2.1 x.2.2, ⟨x.1.2,x.1.2⟩,
    (mem_centralizer_swap_mk α hα _ _ _ _).mpr rfl⟩
  left_inv x := by
    apply Subtype.ext
    exact SemidirectProduct.ext (Prod.ext rfl ((mem_centralizer_swap α hα x).mp x.2.2)) rfl
  right_inv _ := rfl

theorem card_subgroup_inf_centralizer_swap (D : Subgroup K) (hD : ∀ a ∈ D, α a ∈ D) :
    Nat.card (subgroup α hα D hD ⊓ Subgroup.centralizer {swap α hα} : Subgroup (Model α hα)) =
      Nat.card D * 4 := by
  rw [Nat.card_congr (subgroupInfCentralizerSwapEquiv α hα D hD), Nat.card_prod, Nat.card_prod, card_bit]
end Theory.GroupTheory.PairedInvolutiveExtension
