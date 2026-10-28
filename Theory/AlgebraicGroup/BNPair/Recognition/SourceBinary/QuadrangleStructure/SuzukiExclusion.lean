module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.AffineExclusion
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SmallSuzuki
public import Theory.SpecificGroups.Suzuki.RootSquareFibers
public import Theory.Frattini.PGroupMap
import all Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.UnequalLinearRadicals

/-!
# No linear--Suzuki quadrangle, including the small Suzuki group

The Suzuki root's Frattini subgroup has order at least q and embeds in
the Frattini subgroup of its own quadrangle remainder. Local characteristic
two and Burnside's kernel theorem give a faithful action on the remainder's
Frattini quotient. Its binary degree is at least 4*log2(q), so the whole
remainder has order at least q^5. This includes q=2, where an order-five
actor gives the same degree-four bound and a root square is nontrivial.

At the opposite linear endpoint, that square moves under reflection.
The two nontrivial linear Frattini actions give the lower bound |F|^4.
The literal three-root products therefore force 3*b <= 2*a and
3*a <= 4*b for |F|=2^a and q=2^b, which contradict b>0.
The original-factor consumer uses the full Sz(2) cover of D10, so the
small dihedral constructor is also excluded without perfectness.

The import-all edge reuses the existing internal three-root cardinality
formula while preserving its established boundary. Every action, root
and kernel is on the same marked quotient. Source: Fong--Seitz I
(4B),(4F),(5D),(6A), pp.19--24,26--28,37.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
open BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem suzuki_root_frattini_card_lower (j : Fin 2) (m : ℕ)
    (ν : simpleRoot Q split j ≃* SuzukiRootSubgroup m) :
    2^(2*m+1) ≤ Nat.card (frattini (simpleRoot Q split j)) := by
  let A := simpleRoot Q split j
  let : Fact (IsPGroup 2 A) := ⟨split.isTwo.to_le (simpleRoot_le Q split j)⟩
  by_cases hm : m = 0
  · subst m
    obtain ⟨a,ha⟩ := suzuki_root_exists_nontrivial_square 0
    have hnon : frattini A ≠ ⊥ := by
      intro hz
      have hmem := pth_power_mem_frattini_of_isPGroup (p := 2) (ν.symm a)
      rw [hz,mem_bot] at hmem
      have hh := congrArg ν hmem
      rw [map_pow,ν.apply_symm_apply,map_one] at hh
      exact ha hh
    have hh := (frattini A).one_lt_card_iff_ne_bot.mpr hnon
    change 2 ≤ Nat.card (frattini A)
    omega
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    let R := SuzukiRootSubgroup m
    let : Fact (IsPGroup 2 R) := ⟨suzukiRootSubgroup_isPGroup m hmpos⟩
    have hz : center R ≤ frattini R := by
      intro z hz
      obtain ⟨x,hx⟩ := suzukiRootSubgroup_square_surjective m hmpos ⟨z,hz⟩
      have hx' : x^2=z := hx
      rw [←hx']
      exact pth_power_mem_frattini_of_isPGroup (p := 2) x
    have hc := Nat.card_le_card_of_injective (inclusion hz) (inclusion_injective hz)
    rw [suzukiRootSubgroup_center_card m hmpos] at hc
    rw [←frattini_map_equiv ν,card_map_of_injective ν.injective] at hc
    exact hc

private theorem suzuki_remainder_frattini_card_lower
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j) (m : ℕ)
    (ν : simpleRoot Q split j ≃* SuzukiRootSubgroup m) :
    2^(2*m+1) ≤ Nat.card (frattini (simpleRemainder Q split j)) := by
  let V := simpleRemainder Q split j
  let C := rootAt Q split j (Q.simple i)
  have hCV : C ≤ V := cross_root_le_own_remainder Q split hm j i hij.symm
  let : Fact (IsPGroup 2 V) := ⟨split.isTwo.to_le inf_le_left⟩
  let : Fact (IsPGroup 2 C) := ⟨split.isTwo.to_le (hCV.trans inf_le_left)⟩
  let a : simpleRoot Q split j ≃* C :=
    ((MulAut.conj (representative (Q.simple i) : X ⧸ Q.D)).symm.subgroupMap _).trans
      (MulEquiv.subgroupCongr (by
        simp only [C,rootAt,rightConjugate,comap_equiv_eq_map_symm']; rfl))
  have hl := suzuki_root_frattini_card_lower Q split j m ν
  have he : Nat.card (frattini C) = Nat.card (frattini (simpleRoot Q split j)) := by
    rw [←frattini_map_equiv a,card_map_of_injective a.injective]
  have hle := frattini_map_le_of_isPGroup (p := 2) (inclusion hCV)
  have hc := Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)
  rw [card_map_of_injective (inclusion_injective hCV),he] at hc
  exact hl.trans hc

/-- The genuine Suzuki actor forces radical order at least q^5, also for Sz(2). -/
theorem suzuki_remainder_card_lower_all
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (hc : centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple j}) :
      Set (Q.tits.standardParabolic {Q.simple j})) ≤
      pCore 2 (Q.tits.standardParabolic {Q.simple j}))
    (m : ℕ) (μ : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (ν : simpleRoot Q split j ≃* SuzukiRootSubgroup m) :
    (2^(2*m+1))^5 ≤ Nat.card (simpleRemainder Q split j) := by
  let V := simpleRemainder Q split j
  let : Fact (IsPGroup 2 V) := ⟨split.isTwo.to_le inf_le_left⟩
  let W := V ⧸ frattini V
  let : IsElementaryAbelian 2 W := isElementaryAbelian_quotient_frattini
  let ρ := elementaryRepresentation (p := 2) (remainderFrattiniAction Q split j hVj)
  have hρ : Function.Injective ρ := by
    intro a b hab
    apply remainderFrattiniAction_injective Q split j (UnitarySource.actorReflection Q split j) hVj hc
    ext v
    exact Additive.ofMul.injective
      (congrArg (fun f : Module.End (ZMod 2) (Additive W) => f (Additive.ofMul v)) hab)
  let σ := ρ.comp μ.symm.toMonoidHom
  have hσ : Function.Injective σ := hρ.comp μ.symm.injective
  have hd : 4*(2*m+1) ≤ Module.finrank (ZMod 2) (Additive W) := by
    by_cases hm0 : m = 0
    · subst m
      have hd := Representation.BinaryPrimeDegree.orderOf_le_finrank σ hσ
        (by decide : Nat.Prime 5) (by decide : 5 ≠ 2)
        (by rw [suzukiZero_card]; decide)
      rw [Representation.BinaryPrimeDegree.orderOf_two_mod_five] at hd
      simpa using hd
    · exact Representation.Suzuki.finrank_ge (by omega : 1 ≤ m) σ hσ
  have hW : (2^(2*m+1))^4 ≤ Nat.card W := by
    have he : Nat.card W = 2 ^ Module.finrank (ZMod 2) (Additive W) := by
      change Nat.card (Additive W) = _
      simpa only [Nat.card_zmod] using
        (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W))
    rw [he,←pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hΦ := suzuki_remainder_frattini_card_lower Q split hm i j hij m ν
  calc
    (2^(2*m+1))^5 = (2^(2*m+1))^4 * 2^(2*m+1) := by ring
    _ ≤ Nat.card W * Nat.card (frattini V) := Nat.mul_le_mul hW hΦ
    _ = Nat.card V := (Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini V)).symm

/-- A linear quadrangle cannot have a Suzuki opposite endpoint, including Sz(2). -/
theorem no_linear_suzuki_quadrangle
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (hc : centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple j}) :
      Set (Q.tits.standardParabolic {Q.simple j})) ≤
      pCore 2 (Q.tits.standardParabolic {Q.simple j}))
    (ξ : rankOne Q split i ≃* SL(2,F))
    (m : ℕ) (μ : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (ν : simpleRoot Q split j ≃* SuzukiRootSubgroup m) : False := by
  let η := (localGroupEquivOfCenterless Q split i hVi ξ
    Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot).trans
      Atlas.RankOneFieldAutomorphisms.slEquivPSL
  have hri := GTwoSource.simpleRoot_card Q split i hVi η
  have hrj : Nat.card (simpleRoot Q split j) = (2^(2*m+1))^2 :=
    (Nat.card_congr ν.toEquiv).trans (ReeSource.matrixRoot_card m)
  let := Fintype.ofFinite F
  obtain ⟨n,_,hn⟩ := FiniteField.card F 2
  have hF : Nat.card F = 2^(n : ℕ) := by simpa only [Nat.card_eq_fintype_card] using hn
  have hl := suzuki_remainder_card_lower_all Q split hm i j hij hVj hc m μ ν
  rw [remainder_card_four Q split hm j i hij.symm,hri,hrj,hF,
    ←pow_mul,←pow_mul,←pow_mul,←pow_add] at hl
  have hb := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hl
  have hn' : 1 < (n : ℕ) := by omega
  obtain ⟨a,ha⟩ := suzuki_root_exists_nontrivial_square m
  have ha' : (ν.symm a)^2 ≠ 1 := by
    intro he
    have hh := congrArg ν he
    rw [map_pow,ν.apply_symm_apply,map_one] at hh
    exact ha hh
  have hu := linear_remainder_card_lower_of_opposite_square Q split hm i j hij hVi ξ hn' hF
    (ν.symm a) ha'
  rw [remainder_card_four Q split hm i j hij,hri,hrj,hF,
    ←pow_mul,←pow_mul,←pow_mul,←pow_add] at hu
  have hb' := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hu
  omega
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
