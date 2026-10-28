module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiWeights

/-!
# Actual Suzuki Cartan images and fixed-point kernels

The full odd abelian Cartan acts transitively on the nonzero vectors of the
canonical root Frattini quotient. Its action image therefore acts regularly.
Coprime Frattini faithfulness identifies its kernel with the literal panel
kernel, and the image has order q−1. The actual rank-one Cartan, also of order
q−1, embeds in that image and hence maps onto it. Thus every element of H is
a product of an element of H ∩ R_i and an element of H ∩ K_i.

Suzuki Sylow centralizers show that the first factor acts without nonidentity
fixed points on the root. Consequently a Cartan subgroup either centralizes
the entire root or has no nonidentity fixed point. All statements use the
canonical root, actual panel map, and same finite marked quotient. They need
no marking of the whole panel as Suzuki and no original-factor perfectness.

Source: Fong--Seitz I (6C), printed pp.40–41, the Cartan-kernel argument.
SuzukiKernelIntersections applies these facts to the literal centralizer
sections. These facts alone do not exclude the equal-Suzuki row.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- Oddness makes the action on the root Frattini quotient detect the exact panel kernel. -/
theorem rootCartanFrattiniAction_kernel (i : Fin 2) :
    (rootCartanFrattiniAction Q split i).ker = (cartanPanelMap Q i).ker := by
  rw [← simpleRootAction_kernel Q split i]
  ext h
  constructor
  · intro hh
    exact OddInvolutionFrattini.automorphism_eq_one_of_quotient_eq_one
      (split.isTwo.to_le (simpleRoot_le Q split i)) (simpleRootAction Q split i h)
      (split.odd.symm.of_dvd_left
        ((orderOf_map_dvd (simpleRootAction Q split i) h).trans (orderOf_dvd_natCard h))) hh
  · intro hh
    change quotientAut (frattini (simpleRoot Q split i)) (simpleRootAction Q split i h) = 1
    rw [show simpleRootAction Q split i h = 1 from hh,map_one]

/-- A nonidentity element of the actual rank-one Cartan fixes no nonidentity root element. -/
theorem suzuki_rankOne_cartan_root_fixedFree (i : Fin 2)
    {m : ℕ} (hm : 0 < m) (μ : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (ν : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    {c : X ⧸ Q.D} (hcH : c ∈ Q.tits.B ⊓ Q.tits.N)
    (hcR : c ∈ rankOne Q split i) (hc : c ≠ 1) :
    simpleRoot Q split i ⊓ centralizer ({c} : Set (X ⧸ Q.D)) = ⊥ := by
  obtain ⟨S,hS⟩ := simpleRoot_sylow_of_suzuki Q split i μ ν
  apply eq_bot_iff.mpr
  intro x hx
  apply mem_bot.mpr
  by_contra hx1
  let r : rankOne Q split i := ⟨x,(show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left) hx.1⟩
  have hr : r ∈ (S : Subgroup (rankOne Q split i)) := by rw [hS]; exact hx.1
  have hr1 : r ≠ 1 := fun he => hx1 (congrArg Subtype.val he)
  have hcS := BenderSuzuki.ZD.RankOneModelGeometry.suzuki_centralizer_le_sylow hm μ S hr hr1
    (show (⟨c,hcR⟩ : rankOne Q split i) ∈ centralizer ({r} : Set _) from
      mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.mp hx.2).symm))
  rw [hS] at hcS
  exact hc (disjoint_def.mp (unipotent_disjoint_torus split)
    (simpleRoot_le Q split i hcS) hcH)

private theorem abelian_transitive_eval_injective
    {H A : Type*} [Group H] [IsMulCommutative H] [Group A]
    (ρ : H →* MulAut A)
    (ht : ∀ x y : A, x ≠ 1 → y ≠ 1 → ∃ h, ρ h x = y)
    {x : A} (hx : x ≠ 1) : Function.Injective (fun a : ρ.range => a.val x) := by
  intro a b hab
  apply Subtype.ext
  apply MulEquiv.ext
  intro y
  by_cases hy : y = 1
  · simp only [hy,map_one]
  obtain ⟨h,rfl⟩ := ht x y hx hy
  obtain ⟨g,hg⟩ := a.property
  obtain ⟨k,hk⟩ := b.property
  have hag : a.val * ρ h = ρ h * a.val := by rw [←hg,←map_mul,←map_mul,mul_comm]
  have hbk : b.val * ρ h = ρ h * b.val := by rw [←hk,←map_mul,←map_mul,mul_comm]
  calc
    a.val (ρ h x) = ρ h (a.val x) := congrArg (fun f : MulAut A => f x) hag
    _ = ρ h (b.val x) := congrArg (ρ h) hab
    _ = b.val (ρ h x) := (congrArg (fun f : MulAut A => f x) hbk).symm

/-- The full source Cartan has exactly q−1 distinct actions on the root quotient. -/
theorem suzuki_cartan_frattini_image_card (i : Fin 2)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    {m : ℕ} (hm : 0 < m) (μ : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (ν : simpleRoot Q split i ≃* SuzukiRootSubgroup m) :
    Nat.card (rootCartanFrattiniAction Q split i).range = 2^(2*m+1)-1 := by
  classical
  let := split.abelian
  let A := simpleRoot Q split i ⧸ frattini (simpleRoot Q split i)
  let ρ := rootCartanFrattiniAction Q split i
  obtain ⟨hc,ht⟩ := suzuki_root_cartan_frattini_regular Q split i hKi hm μ ν
  let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by
    change 1 < Nat.card (simpleRoot Q split i ⧸ frattini (simpleRoot Q split i))
    rw [hc]; exact one_lt_pow₀ (by decide) (by omega))
  obtain ⟨x,hx⟩ := exists_ne (1 : A)
  let f : ρ.range → {y : A // y ≠ 1} := fun a =>
    ⟨a.val x,fun he => hx (a.val.map_eq_one_iff.mp he)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      exact abelian_transitive_eval_injective ρ ht hx (congrArg Subtype.val hab)
    · intro y
      obtain ⟨h,hh⟩ := ht x y hx y.property
      exact ⟨ρ.rangeRestrict h,Subtype.ext hh⟩
  have he := Nat.card_congr (Equiv.ofBijective f hf)
  let : Fintype A := Fintype.ofFinite A
  rw [Nat.card_eq_fintype_card (α := {y : A // y ≠ 1}),Fintype.card_subtype_compl,
    show Fintype.card {y : A // y = 1} = 1 from Fintype.card_unique,
    ← Nat.card_eq_fintype_card] at he
  exact he.trans (congrArg (· - 1) hc)

/-- The same exact order on the literal faithful-panel image. -/
theorem suzuki_cartan_panel_image_card (i : Fin 2)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    {m : ℕ} (hm : 0 < m) (μ : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (ν : simpleRoot Q split i ≃* SuzukiRootSubgroup m) :
    Nat.card (cartanPanelMap Q i).range = 2^(2*m+1)-1 := by
  let e := (QuotientGroup.quotientKerEquivRange (rootCartanFrattiniAction Q split i)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (rootCartanFrattiniAction_kernel Q split i)).trans
      (QuotientGroup.quotientKerEquivRange (cartanPanelMap Q i)))
  rw [←Nat.card_congr e.toEquiv]
  exact suzuki_cartan_frattini_image_card Q split i hKi hm μ ν

/-- The genuine rank-one Cartan maps isomorphically onto the entire Cartan image. -/
theorem suzuki_rankOne_cartan_panel_bijective (i : Fin 2)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    {m : ℕ} (hm : 0 < m) (μ : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (ν : simpleRoot Q split i ≃* SuzukiRootSubgroup m) :
    Function.Bijective ((cartanPanelMap Q i).rangeRestrict.comp
      ((rankOne Q split i).subgroupOf (Q.tits.B ⊓ Q.tits.N)).subtype) := by
  let H := Q.tits.B ⊓ Q.tits.N
  let C := (rankOne Q split i).subgroupOf H
  let f := (cartanPanelMap Q i).rangeRestrict.comp C.subtype
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_one _).mpr
    intro c hc
    have hk : (c : H) ∈ (cartanPanelMap Q i).ker := congrArg Subtype.val hc
    rw [←simpleRootAction_kernel Q split i, simpleRootAction,RootAction.action_kernel] at hk
    have hcard : 1 < Nat.card (simpleRoot Q split i) := by
      rw [Nat.card_congr ν.toEquiv,suzukiRootSubgroup_card m hm]
      exact one_lt_pow₀ (one_lt_pow₀ (by decide) (by omega)) (by decide)
    let : Nontrivial (simpleRoot Q split i) := Finite.one_lt_card_iff_nontrivial.mp hcard
    obtain ⟨x,hx⟩ := exists_ne (1 : simpleRoot Q split i)
    apply Subtype.ext
    apply Subtype.ext
    by_contra hc1
    have he := suzuki_rankOne_cartan_root_fixedFree Q split i hm μ ν c.val.property c.property hc1
    have hxC : (x : X ⧸ Q.D) ∈ centralizer ({(c.val : X ⧸ Q.D)} : Set _) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hk x x.property)
    exact hx (Subtype.ext (he.le ⟨x.property,hxC⟩))
  let e : (Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split i) ≃* C :=
    { toFun c := ⟨⟨c,c.property⟩,c.val.property⟩
      invFun c := ⟨⟨c,c.property⟩,c.val.property⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_mul' _ _ := rfl }
  have hC := (Nat.card_congr e.symm.toEquiv).trans
    (suzuki_rankOne_cartan_cyclic_card Q split i hKi hm μ ν
      (UnitarySource.actorReflection Q split i)).2
  have him := suzuki_cartan_panel_image_card Q split i hKi hm μ ν
  exact (Nat.bijective_iff_injective_and_card f).mpr ⟨hf,hC.trans him.symm⟩

/-- Every source Cartan element is a product of an actual rank-one Cartan element
and an element of the literal panel kernel. -/
theorem suzuki_cartan_factorization (i : Fin 2)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    {m : ℕ} (hm : 0 < m) (μ : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (ν : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (h : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) :
    ∃ c : (rankOne Q split i).subgroupOf (Q.tits.B ⊓ Q.tits.N),
      ∃ k : (cartanPanelMap Q i).ker, h = c.val * k.val := by
  obtain ⟨c,hc⟩ := (suzuki_rankOne_cartan_panel_bijective Q split i hKi hm μ ν).2
    ((cartanPanelMap Q i).rangeRestrict h)
  have he : cartanPanelMap Q i c.val = cartanPanelMap Q i h := congrArg Subtype.val hc
  refine ⟨c,⟨c.val⁻¹*h,?_⟩,by simp⟩
  change cartanPanelMap Q i (c.val⁻¹*h) = 1
  rw [map_mul,map_inv,he,inv_mul_cancel]

/-- A Cartan element fixing one nonidentity root element belongs to the
literal panel kernel, hence centralizes the whole root-generated group. -/
theorem suzuki_cartan_root_fixed_iff_kernel (i : Fin 2)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    {m : ℕ} (hm : 0 < m) (μ : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (ν : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (h : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)))
    (x : simpleRoot Q split i) (hx : x ≠ 1) :
    Commute (h : X ⧸ Q.D) (x : X ⧸ Q.D) ↔ h ∈ (cartanPanelMap Q i).ker := by
  constructor
  · intro hfix
    obtain ⟨c,k,he⟩ := suzuki_cartan_factorization Q split i hKi hm μ ν h
    have hk := (show (cartanPanelMap Q i).ker ≤
        (centralizer (simpleRoot Q split i : Set (X ⧸ Q.D))).subgroupOf (Q.tits.B ⊓ Q.tits.N) from by
      rw [←simpleRootAction_kernel Q split i,simpleRootAction,RootAction.action_kernel]) k.property
    have hkx : Commute (k.val : X ⧸ Q.D) (x : X ⧸ Q.D) :=
      (mem_centralizer_iff.mp hk x x.property).symm
    have hcx : Commute (c.val : X ⧸ Q.D) (x : X ⧸ Q.D) := by
      have hval : (h : X ⧸ Q.D) = (c.val : X ⧸ Q.D)*(k.val : X ⧸ Q.D) := congrArg Subtype.val he
      rw [hval] at hfix
      have hh := hfix.mul_left hkx.inv_left
      simpa only [mul_inv_cancel_right] using hh
    have hc : (c.val : X ⧸ Q.D) = 1 := by
      by_contra hc
      have hf := suzuki_rankOne_cartan_root_fixedFree Q split i hm μ ν c.val.property c.property hc
      exact hx (Subtype.ext (hf.le ⟨x.property,mem_centralizer_singleton_iff.mpr hcx.symm⟩))
    have hc' : c.val = 1 := Subtype.ext hc
    rw [he,hc',one_mul]
    exact k.property
  · intro hk
    rw [←simpleRootAction_kernel Q split i,simpleRootAction,RootAction.action_kernel] at hk
    exact (mem_centralizer_iff.mp hk x x.property).symm

/-- A Cartan subgroup either centralizes a Suzuki root or has no nonidentity
fixed point on it. The condition concerns its actual panel action. -/
theorem suzuki_cartan_subgroup_fixedFree (i : Fin 2)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    {m : ℕ} (hm : 0 < m) (μ : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (ν : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (T : Subgroup (X ⧸ Q.D)) (hTH : T ≤ Q.tits.B ⊓ Q.tits.N)
    (hTK : ¬ T ≤ localKernel Q i) :
    simpleRoot Q split i ⊓ centralizer (T : Set (X ⧸ Q.D)) = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  apply mem_bot.mpr
  by_contra hx1
  apply hTK
  intro t ht
  have hk := (suzuki_cartan_root_fixed_iff_kernel Q split i hKi hm μ ν
    ⟨t,hTH ht⟩ ⟨x,hx.1⟩ (fun he => hx1 (congrArg Subtype.val he))).mp
    (mem_centralizer_iff.mp hx.2 t ht)
  rw [cartanPanelMap_kernel] at hk
  exact hk

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
