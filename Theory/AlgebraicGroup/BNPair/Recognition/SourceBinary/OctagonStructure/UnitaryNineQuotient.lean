module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryNineCenter
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryNineProper
import all Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryCubicFixed

/-!
# The whole-subgroup obstruction for a large irreducible unitary section

A large elementary quotient of the source nine-b subgroup has kernel of
order at most 2^b. The middle Frattini root already lies in the derived
subgroup and has precisely that order, so it equals the kernel. The
proved cubic centrality argument then puts a strictly larger subgroup in
the center. Its image in an irreducible quotient is either zero or all:
the first contradicts strictness, and the second makes X abelian despite
its nontrivial middle-root commutator.

The quotient homomorphism and its action compatibility are retained
literally. The matching original-factor module applies the result to the
actual RootSection effective quotient, including both orientations and
b=1. The sharp degree bound and irreducible-section selection remain
explicit source premises, and lower-central persistence is still needed.

Source: Fong--Seitz I (6F), printed p.47, the whole-X case of the
invariant-subgroup argument.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup
open scoped IsMulCommutative commutatorElement

/-- A nonabelian group with central kernel has no nonzero invariant central
image in an irreducible elementary quotient. -/
private theorem center_le_kernel_of_irreducible_quotient
    {K R Z : Type*} [Group K] [Group R] [Group Z] [IsElementaryAbelian 2 Z]
    (α : R →* MulAut K) (ρ : Representation (ZMod 2) R (Additive Z))
    (hirr : ρ.IsIrreducible) (f : K →* Z)
    (heq : ∀ r x, ρ r (Additive.ofMul (f x))=Additive.ofMul (f (α r x)))
    (hker : f.ker ≤ center K) (hne : ¬ IsMulCommutative K) : center K ≤ f.ker := by
  let := hirr
  let A := (center K).map f
  let W : Subrepresentation ρ := ⟨AddSubgroup.toZModSubmodule 2 A.toAddSubgroup,by
    intro r v hv
    change v.toMul ∈ A at hv
    obtain ⟨x,hx,rfl⟩ := hv
    change (ρ r (Additive.ofMul (f x))).toMul ∈ A
    rw [heq]
    exact mem_map_of_mem f (MulEquivClass.apply_mem_center (α r) hx)⟩
  rcases eq_bot_or_eq_top W with hw | hw
  · intro x hx
    have hm : Additive.ofMul (f x) ∈ W := mem_map_of_mem f hx
    rw [hw] at hm
    exact congrArg Additive.toMul hm
  · exfalso
    apply hne
    have hc : ∀ x : K, x ∈ center K := by
      intro x
      have hm : Additive.ofMul (f x) ∈ W := hw ▸ trivial
      obtain ⟨z,hz,hzx⟩ := (show f x ∈ A from hm)
      have hk : z⁻¹*x ∈ f.ker := by
        change f (z⁻¹*x)=1
        rw [map_mul,map_inv,hzx,inv_mul_cancel]
      simpa only [mul_inv_cancel_left] using (center K).mul_mem hz (hker hk)
    exact ⟨⟨fun x y => mem_center_iff.mp (hc y) x⟩⟩

open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- Order saturation identifies the kernel of any sufficiently large elementary
quotient with the literal middle Frattini root. -/
theorem unitaryNineSubgroup_large_quotient_kernel (i j : Fin 2) {b : ℕ}
    (hK : Nat.card (unitaryNineSubgroup Q split i j)=2^(9*b))
    (hM : Nat.card (rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i))=2^b)
    (hMD : rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i) ≤
      ⁅unitaryNineSubgroup Q split i j,unitaryNineSubgroup Q split i j⁆)
    {Z : Type*} [Group Z] [IsElementaryAbelian 2 Z]
    (f : unitaryNineSubgroup Q split i j →* Z) (hf : Function.Surjective f)
    (hlarge : 2^(8*b) ≤ Nat.card Z) :
    f.ker.map (unitaryNineSubgroup Q split i j).subtype =
      rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i) ∧
    ⁅unitaryNineSubgroup Q split i j,unitaryNineSubgroup Q split i j⁆ ≤
      rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i) := by
  let K := unitaryNineSubgroup Q split i j
  let M := rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i)
  have hd : ⁅K,K⁆ ≤ f.ker.map K.subtype := by
    let f₀ : K →* Z := f
    rw [←K.map_subtype_commutator]
    apply map_mono
    apply commutator_le.mpr
    intro x _ y _
    change f₀ ⁅x,y⁆=1
    rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have hc := f.ker.card_mul_index
  rw [index_ker,MonoidHom.range_eq_top.mpr hf,card_top,hK] at hc
  have hker : Nat.card f.ker ≤ 2^b := by
    apply Nat.le_of_mul_le_mul_right (c:=2^(8*b)) ?_ (by positivity)
    calc
      Nat.card f.ker*2^(8*b) ≤ Nat.card f.ker*Nat.card Z := Nat.mul_le_mul_left _ hlarge
      _ = 2^(9*b) := hc
      _ = 2^b*2^(8*b) := by rw [←pow_add]; congr 1; omega
  have he : M=f.ker.map K.subtype := eq_of_le_of_card_ge (hMD.trans hd) (by
    rw [card_map_of_injective K.subtype_injective]
    exact hker.trans_eq hM.symm)
  exact ⟨he.symm,hd.trans he.ge⟩

/-- The whole source subgroup cannot have a large irreducible elementary
quotient: its kernel would be the middle root, strictly smaller than the
center, whereas irreducibility forces the center into that kernel. -/
theorem unitaryNineSubgroup_irreducible_quotient_false
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j) {b : ℕ} (hb : 0 < b)
    (hK : Nat.card (unitaryNineSubgroup Q split i j)=2^(9*b))
    (hM : Nat.card (rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i))=2^b)
    (hMD : rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i) ≤
      ⁅unitaryNineSubgroup Q split i j,unitaryNineSubgroup Q split i j⁆)
    (hY : simpleRemainder Q split j ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) ≤
      unitaryNineSubgroup Q split i j)
    (ha : IsMulCommutative ↥(simpleRemainder Q split j ⊓
      centralizer (cartanThreeCore Q : Set (X ⧸ Q.D))))
    (hfix : ∀ w : Weyl Q, rootAt Q split j w ⊓
      centralizer (cartanThreeCore Q : Set (X ⧸ Q.D))=rootFrattiniAt Q split j w)
    (W : Subgroup (X ⧸ Q.D)) (hW : W=unitaryNineSubgroup Q split i j)
    {R Z : Type*} [Group R] [Group Z] [IsElementaryAbelian 2 Z]
    (α : R →* MulAut W) (ρ : Representation (ZMod 2) R (Additive Z))
    (hirr : ρ.IsIrreducible) (f : W →* Z) (hf : Function.Surjective f)
    (hequiv : ∀ r x, ρ r (Additive.ofMul (f x))=Additive.ofMul (f (α r x)))
    (hlarge : 2^(8*b) ≤ Nat.card Z) : False := by
  subst W
  let K := unitaryNineSubgroup Q split i j
  let M := rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i)
  obtain ⟨hker,hder⟩ := unitaryNineSubgroup_large_quotient_kernel Q split i j hK hM hMD f hf hlarge
  have hnon : 1 < Nat.card M := hM ▸ Nat.one_lt_pow (by omega) (by decide)
  have hcenter := unitaryNineSubgroup_center_gt_middle_of_derived_le Q split hm i j hij
    hY ha hfix hnon hder
  have hk : f.ker ≤ center K := by
    intro x hx
    have hm : (x : X ⧸ Q.D) ∈ M := hker.le (mem_map_of_mem K.subtype hx)
    obtain ⟨z,hz,hzx⟩ := hcenter.le hm
    exact K.subtype_injective hzx ▸ hz
  have hnc : ¬ IsMulCommutative K := by
    intro hc
    have hbot : ⁅K,K⁆=⊥ := commutator_self_eq_bot_iff.mpr hc
    have he : M=⊥ := eq_bot_iff.mpr (hbot ▸ hMD)
    rw [he,Nat.card_unique] at hnon
    omega
  have hc := center_le_kernel_of_irreducible_quotient α ρ hirr f hequiv hk hnc
  exact hcenter.not_ge ((map_mono hc).trans hker.le)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
