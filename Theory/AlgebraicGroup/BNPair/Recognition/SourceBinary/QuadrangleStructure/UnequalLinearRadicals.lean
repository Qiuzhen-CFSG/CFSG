module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.QuadraticFrattini
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.OrderFormulas
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.ProfileActors
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.SimpleCoordinates

/-!
# Unequal linear quadrangles before the exact field ratio

For two actual linear root actors with |k| < |F|, the larger radical is
already elementary. If its Frattini subgroup were nonzero, Cartan
irreducibility and the three-root product would identify it with the
crossed F-root. The Frattini quotient would then have order |k|².
Reflection movement and the perfect SL₂(F) action require order at least
|F|², a contradiction.

The opposite roots in this elementary radical therefore commute. If the
other same-type roots also commuted, their entire crossed F-root would
be fixed by SL₂(F). The minimum moved dimension, together with this
fixed subgroup, would force radical order at least |F|³, again contradicting
its actual order |F||k|². Cartan irreducibility gives the exact remaining
commutator. The same degree estimate yields |F| ≤ |k|².

The smaller field may be binary; the larger actor is automatically at
least SL₂(4). No endpoint perfectness or exact field ratio is assumed.
The original-factor adapter UnequalLinearStructure supplies both actual
local markings and transports the conclusions through the full amalgam.
These are structural steps toward the unequal quadrangle row; the exact
quadratic ratio and exhaustive source selection are not asserted here.

Source: DGS, Groups and Graphs (1985), (5.7), (11.6)--(11.7),
pp.173--175; Fong--Seitz I (3G), (4B), (6A)(b); Burnside's basis theorem.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
private theorem linear_frattini_card_lower {F A V : Type*}
    [Field F] [Finite F] [CharP F 2] [Group A] [Group V] [Finite V]
    (μ : A ≃* SL(2,F)) (hp : IsPGroup 2 V) (φ : A →* MulAut V)
    (hnt : ∃ a, φ a ≠ 1) {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2^n) :
    Nat.card F ^ 2 ≤ Nat.card (V ⧸ frattini V) := by
  have hfour : 3 < Nat.card F := by
    rw [hF]
    have hh : 2^2 ≤ 2^n := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  let : Group.IsPerfect SL(2,F) := GorensteinWalter.sl2_isPerfect_of_card_gt_three F hfour
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective (f := μ.symm.toMonoidHom) μ.symm.surjective
  let : Fact (IsPGroup 2 V) := ⟨hp⟩
  let W := V ⧸ frattini V
  let : IsElementaryAbelian 2 W := isElementaryAbelian_quotient_frattini
  let β := (quotientAut (frattini V)).comp φ
  have hβ : β ≠ 1 := φ.frattini_comp_ne_one_of_isPerfect hp (by
    intro he
    obtain ⟨a,ha⟩ := hnt
    exact ha (DFunLike.congr_fun he a))
  have hntβ : ∃ a, β a ≠ 1 := by
    by_contra! hh
    exact hβ (MonoidHom.ext hh)
  let ρ := (elementaryRepresentation (p := 2) β).comp μ.symm.toMonoidHom
  have hntρ : ∃ g, ρ g ≠ 1 := by
    obtain ⟨a,ha⟩ := hntβ
    refine ⟨μ a,fun he => ha ?_⟩
    ext v : 1
    have hv := congrArg (fun f : Module.End (ZMod 2) (Additive W) =>
      f (Additive.ofMul v)) he
    change Additive.ofMul (β (μ.symm (μ a)) v) = Additive.ofMul v at hv
    change β a v = v
    simpa only [MulEquiv.symm_apply_apply] using Additive.ofMul.injective hv
  have hl := Representation.SL2.fixedCodim_top_lower ρ hntρ hn hF
  have hd := fixedCodim_add_finrank ρ ⊤
  change fixedCodim ρ ⊤ + Module.finrank (ZMod 2) (fixedSpace ρ ⊤) =
    Module.finrank (ZMod 2) (Additive W) at hd
  have hc : Nat.card W = 2 ^ Module.finrank (ZMod 2) (Additive W) := by
    change Nat.card (Additive W) = _
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W))
  have hlow : Nat.card F ^ 2 ≤ Nat.card W := by
    rw [hc,hF,←pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  exact hlow

open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem remainder_card_four (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j) :
    Nat.card (simpleRemainder Q split i) =
      Nat.card (simpleRoot Q split i) * Nat.card (simpleRoot Q split j)^2 := by
  have hprod : Nat.card (simpleRoot Q split 0) * Nat.card (simpleRoot Q split 1) =
      Nat.card (simpleRoot Q split i) * Nat.card (simpleRoot Q split j) := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · rfl
    · exact Nat.mul_comm _ _
    · exact (hij rfl).elim
  have hc := unipotent_card_simple Q split i
  rw [unipotent_card_even Q split 2 hm,hprod] at hc
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := simpleRoot Q split i))
  calc
    Nat.card (simpleRoot Q split i) * Nat.card (simpleRemainder Q split i) =
        (Nat.card (simpleRoot Q split i) * Nat.card (simpleRoot Q split j))^2 := hc.symm
    _ = _ := by ring

/-- Strictly unequal linear root orders force the larger radical to be elementary. -/
theorem unequal_linear_larger_remainder_elementary {F k : Type*}
    [Field F] [Finite F] [CharP F 2] [Field k] [Finite k] [CharP k 2]
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : rankOne Q split i ≃* SL(2,F))
    (ν : localGroup Q split j ≃* PSL(2,k))
    (hlt : Nat.card k < Nat.card F) :
    IsElementaryAbelian 2 (simpleRemainder Q split i) := by
  let ξ := (localGroupEquivOfCenterless Q split i hVi μ
    Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot).trans
      Atlas.RankOneFieldAutomorphisms.slEquivPSL
  have hri := GTwoSource.simpleRoot_card Q split i hVi ξ
  have hrj := GTwoSource.simpleRoot_card Q split j hVj ν
  have hcard := remainder_card_four Q split hm i j hij
  rw [hri,hrj] at hcard
  let V := simpleRemainder Q split i
  have hp : IsPGroup 2 V := split.isTwo.to_le inf_le_left
  let : Fact (IsPGroup 2 V) := ⟨hp⟩
  have hφ := (remainder_derived_frattini Q split hm i j hij hVi hVj
    (simpleRoot_elementary_of_linear Q split i ξ)
    (simpleRoot_elementary_of_linear Q split j ν)).2
  by_cases hz : ⁅simpleRoot Q split j,rootAt Q split j (Q.simple i)⁆ = ⊥
  · have hbot : frattini V = ⊥ := by
      apply (Subgroup.map_eq_bot_iff_of_injective _ V.subtype_injective).mp
      exact hφ.trans hz
    exact (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hbot
  · have he := cross_root_commutator_eq_of_nonzero Q split hm i j hij hVi hVj ξ hz
    have hφcard : Nat.card (frattini V) = Nat.card F := by
      calc
        Nat.card (frattini V) = Nat.card ((frattini V).map V.subtype) :=
          (card_map_of_injective V.subtype_injective).symm
        _ = Nat.card (rootAt Q split i (Q.simple j)) := by rw [hφ,he]
        _ = Nat.card F := (card_rightConjugate _ _).trans hri
    let := Fintype.ofFinite F
    obtain ⟨n,_,hn⟩ := FiniteField.card F 2
    have hF : Nat.card F = 2^(n : ℕ) := by simpa only [Nat.card_eq_fintype_card] using hn
    have hn' : 1 < (n : ℕ) := by
      have hk := Finite.one_lt_card (α := k)
      by_contra! hh
      have hh' := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hh
      rw [←hF] at hh'
      norm_num at hh'
      omega
    have hl := linear_frattini_card_lower μ hp (remainderRankOneAction Q split i hVi)
      (remainder_action_moves_root Q split hm i j hij hVi) hn' hF
    have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini V)
    change Nat.card V = Nat.card (V ⧸ frattini V) * Nat.card (frattini V) at hc
    rw [hφcard] at hc
    change Nat.card V = Nat.card F * Nat.card k ^ 2 at hcard
    have hq : Nat.card (V ⧸ frattini V) = Nat.card k ^ 2 := by
      apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := F))
      calc
        Nat.card (V ⧸ frattini V) * Nat.card F = Nat.card V := hc.symm
        _ = Nat.card k ^ 2 * Nat.card F := by rw [hcard,Nat.mul_comm]
    rw [hq] at hl
    nlinarith

/-- Unequal linear quadrangles force the two crossed-root equations and
bound the larger field by the square of the smaller, before a field ratio is supplied. -/
theorem unequal_linear_cross_roots {F k : Type*}
    [Field F] [Finite F] [CharP F 2] [Field k] [Finite k] [CharP k 2]
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : rankOne Q split i ≃* SL(2,F))
    (ν : localGroup Q split j ≃* PSL(2,k))
    (hlt : Nat.card k < Nat.card F) :
    ⁅simpleRoot Q split j,rootAt Q split j (Q.simple i)⁆ = ⊥ ∧
      ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ = rootAt Q split j (Q.simple i) ∧
      Nat.card F ≤ Nat.card k ^ 2 := by
  let ξ := (localGroupEquivOfCenterless Q split i hVi μ
    Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot).trans
      Atlas.RankOneFieldAutomorphisms.slEquivPSL
  have hri := GTwoSource.simpleRoot_card Q split i hVi ξ
  have hrj := GTwoSource.simpleRoot_card Q split j hVj ν
  have hcard := remainder_card_four Q split hm i j hij
  rw [hri,hrj] at hcard
  let V := simpleRemainder Q split i
  let := unequal_linear_larger_remainder_elementary Q split hm i j hij hVi hVj μ ν hlt
  let φ := remainderRankOneAction Q split i hVi
  let ρ := (elementaryRepresentation (p := 2) φ).comp μ.symm.toMonoidHom
  have hntρ : ∃ g, ρ g ≠ 1 := by
    obtain ⟨a,ha⟩ := remainder_action_moves_root Q split hm i j hij hVi
    refine ⟨μ a,fun he => ha ?_⟩
    ext v : 1
    have hv := congrArg (fun f : Module.End (ZMod 2) (Additive V) =>
      f (Additive.ofMul v)) he
    change Additive.ofMul (φ (μ.symm (μ a)) v) = Additive.ofMul v at hv
    change φ a v = v
    simpa only [MulEquiv.symm_apply_apply] using Additive.ofMul.injective hv
  let := Fintype.ofFinite F
  obtain ⟨n,_,hn⟩ := FiniteField.card F 2
  have hF : Nat.card F = 2^(n : ℕ) := by simpa only [Nat.card_eq_fintype_card] using hn
  have hn' : 1 < (n : ℕ) := by
    have hk := Finite.one_lt_card (α := k)
    by_contra! hh
    have hh' := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hh
    rw [←hF] at hh'
    norm_num at hh'
    omega
  have hl := Representation.SL2.fixedCodim_top_lower ρ hntρ hn' hF
  have hd := fixedCodim_add_finrank ρ ⊤
  change fixedCodim ρ ⊤ + Module.finrank (ZMod 2) (fixedSpace ρ ⊤) =
    Module.finrank (ZMod 2) (Additive V) at hd
  have hc : Nat.card V = 2 ^ Module.finrank (ZMod 2) (Additive V) := by
    change Nat.card (Additive V) = _
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V))
  have hlow : Nat.card F ^ 2 ≤ Nat.card V := by
    rw [hc,hF,←pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hbound : Nat.card F ≤ Nat.card k ^ 2 := by
    change Nat.card V = Nat.card F * Nat.card k ^ 2 at hcard
    rw [hcard] at hlow
    have hp : 0 < Nat.card F := Nat.card_pos
    nlinarith
  have hzero : ⁅simpleRoot Q split j,rootAt Q split j (Q.simple i)⁆ = ⊥ := by
    obtain ⟨ha,hb⟩ := opposite_roots_le_remainder Q split j i hij.symm
    exact bot_unique ((commutator_mono ha hb).trans
      (commutator_self_eq_bot_iff.mpr (inferInstance : IsMulCommutative V)).le)
  refine ⟨hzero,?_,hbound⟩
  apply cross_root_commutator_eq_of_nonzero Q split hm j i hij.symm hVj hVi ν
  intro hcomm
  have hcent := UnitarySource.rankOne_centralizes_cross_root Q split hm i j hij hcomm
  let f : rootAt Q split i (Q.simple j) → fixedSpace ρ ⊤ := fun a =>
    ⟨Additive.ofMul ⟨a,cross_root_le_own_remainder Q split hm i j hij a.property⟩,by
      intro g
      change Additive.ofMul (φ (μ.symm g.val) _) = _
      apply congrArg Additive.ofMul
      apply Subtype.ext
      rw [remainderRankOneAction_apply]
      have hh := mem_centralizer_iff.mp (hcent (μ.symm g.val).property) a a.property
      exact mul_inv_eq_iff_eq_mul.mpr hh.symm⟩
  have hf : Function.Injective f := by
    intro a b he
    exact Subtype.ext (congrArg (fun v : fixedSpace ρ ⊤ => (v.val.toMul : X ⧸ Q.D)) he)
  have hfix : Nat.card F ≤ Nat.card (fixedSpace ρ ⊤) := by
    have hh := Nat.card_le_card_of_injective f hf
    have he : Nat.card (rootAt Q split i (Q.simple j)) = Nat.card F :=
      (card_rightConjugate _ _).trans hri
    rwa [he] at hh
  have hfc : Nat.card (fixedSpace ρ ⊤) =
      2 ^ Module.finrank (ZMod 2) (fixedSpace ρ ⊤) := by
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ ⊤))
  have hmul : Nat.card F ^ 2 * Nat.card (fixedSpace ρ ⊤) ≤ Nat.card V := by
    rw [hfc,hF,←pow_mul,hc,←pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hcube : Nat.card F ^ 2 * Nat.card F ≤ Nat.card V :=
    (Nat.mul_le_mul_left _ hfix).trans hmul
  change Nat.card V = Nat.card F * Nat.card k ^ 2 at hcard
  rw [hcard] at hcube
  have hp : 0 < Nat.card F := Nat.card_pos
  nlinarith [sq_lt_sq₀ (Nat.zero_le (Nat.card k)) (Nat.zero_le (Nat.card F)) |>.mpr hlt]

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
