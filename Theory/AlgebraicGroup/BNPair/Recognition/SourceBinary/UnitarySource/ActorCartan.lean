module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.CartanPinning
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.CartanActions
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.FourCartanOrders
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The entire Cartan action from the actual linear root actor

For any element of H, its action on one nonidentity simple-root element
is realized by the aligned SL2 torus. Since H is abelian and this torus is
regular on the nonidentity root elements, the two actions agree on the
entire root. The faithful Cartan image is therefore exactly this actual
rank-one torus, with its full field-unit order. Its reflection inverts
that image, while fixing the true panel kernel. No identification of the
whole faithful endpoint quotient is assumed.

Applied to the two U4 root actors, these results discharge all panel-order
and inversion premises in FourCartanOrders. Only the genuine local actor
identifications and the source commuting clause are needed. The original
actor quotient maps and elementary radical supply them in
UnitarySource/ActorCartanApplication. Both orientations and the fields of
orders two and four are included; no perfectness of SL2(2) is used.

Source: Fong--Seitz I (3B), (5C), pp.13,26; II (8.1)--(8.2), p.197,
and the characteristic-two Cartan computation on p.201.
-/

public noncomputable section
open Subgroup Theory.PSL2.SemilinearCoverage
open scoped MatrixGroups IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
open RootCoordinates HexagonStructure GTwoSource ReeSource
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
variable {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
variable (i : Fin 2) (hV : simpleRemainder Q split i ≤ localKernel Q i)
variable (μ : localGroup Q split i ≃* PSL(2,F)) (s : HexagonStructure.RootReflection Q split i)
local notation "A" => alignedSimpleParameter Q split i hV μ s
local notation "t" => alignedTorusHom Q split i hV μ s

private theorem square_unit (c : F) (hc : c ≠ 0) : ∃ a : Fˣ, (a : F)^2 = c := by
  let x := (frobeniusEquiv F 2).symm c
  have hx : x^2 = c := frobeniusEquiv_symm_pow_p F 2 c
  have hx0 : x ≠ 0 := by intro hz; rw [hz,zero_pow (by decide)] at hx; exact hc hx.symm
  exact ⟨Units.mk0 x hx0,hx⟩

include split in
private theorem commute_cartan {a b : X ⧸ Q.D}
    (ha : a ∈ Q.tits.B ⊓ Q.tits.N) (hb : b ∈ Q.tits.B ⊓ Q.tits.N) : Commute a b := by
  let := split.abelian
  exact congrArg Subtype.val (mul_comm (⟨a,ha⟩ : ↥(Q.tits.B ⊓ Q.tits.N)) ⟨b,hb⟩)

/-- Every full-Cartan action on the simple root is realized by its actual
rank-one torus, because the Cartan commutes with that regular torus. -/
theorem exists_alignedTorus_same_action (h : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) :
    ∃ a : Fˣ, ∀ b : F, (h : X ⧸ Q.D)*A (.ofAdd b)*(h : X ⧸ Q.D)⁻¹ =
      t a*A (.ofAdd b)*(t a)⁻¹ := by
  have hA1 : A (.ofAdd (1:F)) ∈ simpleRoot Q split i := by
    rw [←alignedSimpleParameter_range Q split i hV μ s]
    exact ⟨_,rfl⟩
  have hc := (mem_normalizer_iff.mp (torus_normalizes_simpleRoot Q split i h.property) _).mp hA1
  rw [←alignedSimpleParameter_range Q split i hV μ s] at hc
  obtain ⟨c,hc⟩ := hc
  have hc0 : c.toAdd ≠ 0 := by
    intro hz
    have hz' : c = 1 := hz
    rw [hz',map_one] at hc
    have hh : A (.ofAdd (1:F)) = 1 := by
      have hh := congrArg (MulAut.conj (h : X ⧸ Q.D)⁻¹) hc.symm
      simpa only [MulAut.conj_apply,inv_inv,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_inv_cancel,mul_one] using hh
    have hh' := alignedSimpleParameter_injective Q split i hV μ s (hh.trans (map_one A).symm)
    exact one_ne_zero (Multiplicative.ofAdd.injective hh')
  obtain ⟨a,ha⟩ := square_unit c.toAdd hc0
  have hbase : (h : X ⧸ Q.D)*A (.ofAdd (1:F))*(h : X ⧸ Q.D)⁻¹ =
      t a*A (.ofAdd (1:F))*(t a)⁻¹ := by
    rw [alignedTorusHom_apply,alignedTorus_root,ha,mul_one]
    exact hc.symm
  refine ⟨a,fun b => ?_⟩
  by_cases hb : b = 0
  · subst b
    simp only [show Multiplicative.ofAdd (0:F) = 1 from rfl,map_one,mul_one,mul_inv_cancel]
  obtain ⟨v,hv⟩ := square_unit b hb
  have hvb : t v*A (.ofAdd (1:F))*(t v)⁻¹ = A (.ofAdd b) := by
    rw [alignedTorusHom_apply,alignedTorus_root,hv,mul_one]
  have hh := DFunLike.congr_fun
    ((commute_cartan Q split h.property (alignedTorus_mem_cartan Q split i hV μ s v)).map MulAut.conj).eq
    (A (.ofAdd (1:F)))
  have ht := DFunLike.congr_fun
    ((commute_cartan Q split (alignedTorus_mem_cartan Q split i hV μ s a)
      (alignedTorus_mem_cartan Q split i hV μ s v)).map MulAut.conj).eq (A (.ofAdd (1:F)))
  change (h:X ⧸ Q.D)*(t v*A (.ofAdd (1:F))*(t v)⁻¹)*(h:X ⧸ Q.D)⁻¹ =
    t v*((h:X ⧸ Q.D)*A (.ofAdd (1:F))*(h:X ⧸ Q.D)⁻¹)*(t v)⁻¹ at hh
  change t a*(t v*A (.ofAdd (1:F))*(t v)⁻¹)*(t a)⁻¹ =
    t v*(t a*A (.ofAdd (1:F))*(t a)⁻¹)*(t v)⁻¹ at ht
  rw [hvb,hbase] at hh
  rw [hvb] at ht
  exact hh.trans ht.symm

/-- The actual aligned rank-one torus, as elements of the full source H. -/
@[expose] def alignedCartanLift : Fˣ →* (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) where
  toFun a := ⟨t a,alignedTorus_mem_cartan Q split i hV μ s a⟩
  map_one' := Subtype.ext (map_one t)
  map_mul' a b := Subtype.ext (map_mul t a b)

@[expose] def actorCartanPanelMap : Fˣ →* (Endpoint Q i ⧸ panelKernel Q i) :=
  (cartanPanelMap Q i).comp (alignedCartanLift Q split i hV μ s)

theorem actorCartanPanelMap_injective : Function.Injective (actorCartanPanelMap Q split i hV μ s) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro a ha
  have hk : alignedCartanLift Q split i hV μ s a ∈ (simpleRootAction Q split i).ker := by
    rw [simpleRootAction_kernel]
    exact ha
  have hA1 : A (.ofAdd (1:F)) ∈ simpleRoot Q split i := by
    rw [←alignedSimpleParameter_range Q split i hV μ s]
    exact ⟨_,rfl⟩
  have hh := congrArg (fun f : MulAut (simpleRoot Q split i) =>
    (f ⟨A (.ofAdd (1:F)),hA1⟩ : X ⧸ Q.D)) hk
  change t a*A (.ofAdd (1:F))*(t a)⁻¹ = A (.ofAdd (1:F)) at hh
  rw [alignedTorusHom_apply,alignedTorus_root,mul_one] at hh
  have he : (a:F)^2 = 1 := Multiplicative.ofAdd.injective
    (alignedSimpleParameter_injective Q split i hV μ s hh)
  exact mem_bot.mpr (Units.ext (CharTwo.sq_injective (he.trans (one_pow 2).symm)))

theorem exists_actorCartanPanelMap_preimage
    (h : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) :
    ∃ a, actorCartanPanelMap Q split i hV μ s a = cartanPanelMap Q i h := by
  obtain ⟨a,ha⟩ := exists_alignedTorus_same_action Q split i hV μ s h
  have he : simpleRootAction Q split i h =
      simpleRootAction Q split i (alignedCartanLift Q split i hV μ s a) := by
    ext b
    have hb : (b : X ⧸ Q.D) ∈ (A).range := by
      rw [alignedSimpleParameter_range Q split i hV μ s]
      exact b.property
    obtain ⟨x,hx⟩ := hb
    change (h:X ⧸ Q.D)*b*(h:X ⧸ Q.D)⁻¹ = t a*b*(t a)⁻¹
    rw [←hx]
    exact ha x.toAdd
  have hk : h*(alignedCartanLift Q split i hV μ s a)⁻¹ ∈ (simpleRootAction Q split i).ker := by
    change simpleRootAction Q split i (h*(alignedCartanLift Q split i hV μ s a)⁻¹) = 1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  rw [simpleRootAction_kernel] at hk
  have hh : cartanPanelMap Q i h = actorCartanPanelMap Q split i hV μ s a := by
    change cartanPanelMap Q i h = cartanPanelMap Q i (alignedCartanLift Q split i hV μ s a)
    apply mul_inv_eq_one.mp
    simpa only [MonoidHom.mem_ker,map_mul,map_inv] using hk
  exact ⟨a,hh.symm⟩

theorem actorCartanPanelMap_range :
    (actorCartanPanelMap Q split i hV μ s).range = (cartanPanelMap Q i).range := by
  apply le_antisymm
  · rintro _ ⟨a,rfl⟩
    exact ⟨alignedCartanLift Q split i hV μ s a,rfl⟩
  · rintro _ ⟨h,rfl⟩
    exact exists_actorCartanPanelMap_preimage Q split i hV μ s h

/-- Only the root-generated local group is identified with PSL2; the entire
faithful endpoint is not an additional model hypothesis. -/
@[expose] def actorCartanImageEquiv : Fˣ ≃* (cartanPanelMap Q i).range :=
  (MonoidHom.ofInjective (actorCartanPanelMap_injective Q split i hV μ s)).trans
    (MulEquiv.subgroupCongr (actorCartanPanelMap_range Q split i hV μ s))

include hV μ s in
theorem actorCartanImage_card : Nat.card (cartanPanelMap Q i).range = Nat.card F-1 := by
  rw [←Nat.card_congr (actorCartanImageEquiv Q split i hV μ s).toEquiv,Nat.card_units]

private theorem simpleCartanAction_aligned (a : Fˣ) :
    simpleCartanAction Q split i (alignedCartanLift Q split i hV μ s a) =
      alignedCartanLift Q split i hV μ s a⁻¹ := by
  apply Subtype.ext
  change (weylCartanAction Q split (Q.simple i)
    (alignedCartanLift Q split i hV μ s a) : X ⧸ Q.D) = _
  rw [←s.class_eq,weylCartanAction_lift,normalizerCartanAction_apply]
  exact reflection_alignedTorus Q split i hV μ s a

include hV μ s in
theorem actorCartan_inversion (h : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) :
    cartanPanelMap Q i (simpleCartanAction Q split i h) = (cartanPanelMap Q i h)⁻¹ := by
  obtain ⟨a,ha⟩ := exists_actorCartanPanelMap_preimage Q split i hV μ s h
  let k := h*(alignedCartanLift Q split i hV μ s a)⁻¹
  have hk : k ∈ (cartanPanelMap Q i).ker := by
    change cartanPanelMap Q i (h*(alignedCartanLift Q split i hV μ s a)⁻¹) = 1
    rw [map_mul,map_inv,←ha]
    exact mul_inv_cancel _
  have hkfix : simpleCartanAction Q split i k = k := cartanPanelMap_kernel_le_fixed Q split i s hk
  have hprod : h = k*alignedCartanLift Q split i hV μ s a := by dsimp [k]; group
  rw [hprod,map_mul,hkfix,simpleCartanAction_aligned]
  simp only [map_mul,map_inv,show cartanPanelMap Q i k = 1 from hk,one_mul]

include hV μ s in
/-- The reflection-fixed subgroup is the true panel kernel without an
assumed marking of the full faithful endpoint. -/
theorem actorCartan_fixed_eq_kernel :
    reflectionFixed Q split i = (cartanPanelMap Q i).ker :=
  reflectionFixed_eq_kernel Q split i s (actorCartan_inversion Q split i hV μ s)

/-- The two actual local root actors force the exact U4 Cartan orders,
without independent models of the full faithful endpoint quotients. -/
theorem four_actor_cartan_cards
    {K E : Type*} [Field K] [Finite K] [CharP K 2]
    [Field E] [Finite E] [CharP E 2]
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,K))
    (μj : localGroup Q split j ≃* PSL(2,E))
    (n : ℕ) (hn : 0 < n) (hK : Nat.card K = 2^n) (hE : Nat.card E = (2^n)^2)
    (hc : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ = ⊥)
    (hcore : Q.tits.B.normalCore = ⊥) :
    Nat.card (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) = ((2^n)^2-1)*(2^n-1) ∧
      Nat.card (coreCartan Q i) = (2^n)^2-1 ∧
      Nat.card (coreCartan Q j) = 2^n-1 := by
  apply four_cartan_cards Q split hm i j hij (one_lt_pow₀ (by decide) hn.ne')
    (even_two.pow_of_ne_zero hn.ne') hc hcore
  · rw [actorCartanImage_card Q split i hVi μi (actorReflection Q split i),hK]
  · rw [actorCartanImage_card Q split j hVj μj (actorReflection Q split j),hE]
  · exact actorCartan_fixed_eq_kernel Q split i hVi μi (actorReflection Q split i)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
