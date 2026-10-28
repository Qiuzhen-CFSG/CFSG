module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiCartanAction
public import Theory.Representation.SubrepresentationLattice

/-!
# Cartan weights on actual Suzuki root quotients

The literal torus H ∩ R_i is cyclic of order q−1. Suzuki Sylow centralizers
and U ∩ H = 1 make its action on U_i faithful. Coprime Frattini faithfulness
and a free orbit force |U_i/Φ(U_i)| = q and transitivity on its nonidentity
vectors. This proves irreducibility over F₂. Conjugating by the chosen Weyl
representative transports the action and quotient to every canonical root,
with the Cartan automorphism explicitly retained.

These are the simple H-constituents needed by the five-root radical argument.
Only the actual root-generated Suzuki marking and root marking are used;
there is no whole-panel marking or original-factor perfectness assumption.
Source: Fong--Seitz I (6C), printed p.40, the Cartan-constituent step.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

@[expose] def rootCartanFrattiniAction (i : Fin 2) :
    (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) →*
      MulAut (simpleRoot Q split i ⧸ frattini (simpleRoot Q split i)) :=
  (quotientAut (frattini (simpleRoot Q split i))).comp
    (RootAction.action _ _ (torus_normalizes_simpleRoot Q split i))

theorem suzuki_root_cartan_frattini_regular (i : Fin 2)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    {m : ℕ} (hm : 0 < m) (μ : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (ν : simpleRoot Q split i ≃* SuzukiRootSubgroup m) :
    Nat.card (simpleRoot Q split i ⧸ frattini (simpleRoot Q split i)) = 2^(2*m+1) ∧
    ∀ x y : simpleRoot Q split i ⧸ frattini (simpleRoot Q split i),
      x ≠ 1 → y ≠ 1 → ∃ h, rootCartanFrattiniAction Q split i h x = y := by
  classical
  let H := Q.tits.B ⊓ Q.tits.N
  let R := rankOne Q split i
  let A := simpleRoot Q split i
  let C := H ⊓ R
  let e : C ≃* H.subgroupOf R :=
    { toFun c := ⟨⟨c,c.property.2⟩,c.property.1⟩
      invFun c := ⟨c,⟨c.property,c.val.property⟩⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_mul' _ _ := rfl }
  have hcart := suzuki_rankOne_cartan_cyclic_card Q split i hKi hm μ ν
    (UnitarySource.actorReflection Q split i)
  let : IsCyclic C := e.isCyclic.mpr hcart.1
  have hc : Nat.card C = 2^(2*m+1)-1 := (Nat.card_congr e.toEquiv).trans hcart.2
  let ψ : C →* MulAut A := RootAction.action C A
    (inf_le_left.trans (torus_normalizes_simpleRoot Q split i))
  obtain ⟨S,hS⟩ := simpleRoot_sylow_of_suzuki Q split i μ ν
  have hAc : Nat.card A = (2^(2*m+1))^2 :=
    (Nat.card_congr ν.toEquiv).trans (suzukiRootSubgroup_card m hm)
  have hA1 : 1 < Nat.card A := by rw [hAc]; exact one_lt_pow₀ (by norm_num) (by omega)
  let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp hA1
  obtain ⟨x,hx⟩ := exists_ne (1 : A)
  have hψ : Function.Injective ψ := by
    apply (injective_iff_map_eq_one _).mpr
    intro c hh
    have hfix := congrArg (fun f : MulAut A => (f x : X ⧸ Q.D)) hh
    change (c : X ⧸ Q.D)*x*(c : X ⧸ Q.D)⁻¹ = x at hfix
    let r : R := ⟨x,show (x : X ⧸ Q.D) ∈ R from (show A ≤ R from le_sup_left) x.property⟩
    have hrS : r ∈ (S : Subgroup R) := by rw [hS]; exact x.property
    have hr1 : r ≠ 1 := fun he => hx (Subtype.ext (show (x : X ⧸ Q.D) = 1 from congrArg (fun z : R => (z : X ⧸ Q.D)) he))
    have hcS := BenderSuzuki.ZD.RankOneModelGeometry.suzuki_centralizer_le_sylow
      hm μ S hrS hr1 (show (⟨c,c.property.2⟩ : R) ∈ centralizer ({r} : Set R) from
        mem_centralizer_singleton_iff.mpr (Subtype.ext (mul_inv_eq_iff_eq_mul.mp hfix)))
    rw [hS] at hcS
    have h1 : (c : X ⧸ Q.D) = 1 := disjoint_def.mp (unipotent_disjoint_torus split)
      (simpleRoot_le Q split i hcS) c.property.1
    exact Subtype.ext h1
  let : Fact (IsPGroup 2 A) := ⟨split.isTwo.to_le (simpleRoot_le Q split i)⟩
  let : IsElementaryAbelian 2 (A ⧸ frattini A) := isElementaryAbelian_quotient_frattini
  let η := (quotientAut (frattini A)).comp ψ
  have ho : Odd (Nat.card C) := Nat.coprime_two_right.mp
    ((split.odd.of_dvd_right (card_dvd_of_le (show C ≤ H from inf_le_left))).symm)
  have hη : Function.Injective η := MonoidHom.injective_frattini_action_of_coprime
    (split.isTwo.to_le (simpleRoot_le Q split i)) ψ hψ ho.coprime_two_right
  obtain ⟨v,hv⟩ := Theory.GroupAction.faithful_cyclic_odd_binary_exists_free_orbit η hη ho
  have hv1 : v ≠ 1 := by
    intro he
    have hsub : Subsingleton C := ⟨fun c d => hv (by simp [he])⟩
    have hcard := Nat.card_eq_one_iff_unique.mpr ⟨hsub,inferInstance⟩
    have hpow : 2 < 2^(2*m+1) := lt_trans (by omega) (Nat.lt_two_pow_self (n := 2*m+1))
    omega
  let f : C → {v : A ⧸ frattini A // v ≠ 1} := fun c =>
    ⟨η c v, fun h => hv1 ((η c).injective (h.trans (map_one (η c)).symm))⟩
  have hf : Function.Injective f := fun c d h => hv (congrArg Subtype.val h)
  have hlow := Nat.card_le_card_of_injective f hf
  let : Fintype (A ⧸ frattini A) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card (α := {v : A ⧸ frattini A // v ≠ 1}),
    Fintype.card_subtype_compl,
    show Fintype.card {v : A ⧸ frattini A // v = 1} = 1 from Fintype.card_unique,
    ← Nat.card_eq_fintype_card,hc] at hlow
  have hhi : Nat.card (A ⧸ frattini A) ≤ 2^(2*m+1) := suzuki_root_frattini_bound Q split i hm ν
  have hpow : 0 < 2^(2*m+1) := by positivity
  have hq : Nat.card (A ⧸ frattini A) = 2^(2*m+1) := by omega
  refine ⟨hq,?_⟩
  intro x y hx hy
  obtain ⟨c,hc,_⟩ := Theory.GroupAction.faithful_cyclic_binary_singer_regular
    η hη (by omega : 1 < 2*m+1) hc hq x y hx hy
  exact ⟨⟨c,c.property.1⟩,hc⟩

@[expose] def rootAtCartanFrattiniAction (i : Fin 2) (w : Weyl Q) :
    (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) →*
      MulAut (rootAt Q split i w ⧸ frattini (rootAt Q split i w)) :=
  (quotientAut (frattini (rootAt Q split i w))).comp (rootAction Q split i w)

/-- The quotient comparison uses the literal right-conjugation representative. -/
@[expose] def rootAtFrattiniEquiv (i : Fin 2) (w : Weyl Q) :
    (rootAt Q split i w ⧸ frattini (rootAt Q split i w)) ≃*
      (simpleRoot Q split i ⧸ frattini (simpleRoot Q split i)) :=
  QuotientGroup.congr _ _ (RootAction.conjugateEquiv (simpleRoot Q split i) (representative w))
    (frattini_map_equiv _)

set_option backward.isDefEq.respectTransparency false in
theorem rootAtFrattiniEquiv_action (i : Fin 2) (w : Weyl Q)
    (h : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)))
    (v : rootAt Q split i w ⧸ frattini (rootAt Q split i w)) :
    rootAtFrattiniEquiv Q split i w (rootAtCartanFrattiniAction Q split i w h v) =
      rootCartanFrattiniAction Q split i
        ((Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)).normalizerMonoidHom
          ⟨representative w,torus_normalizes (representative w)⟩ h)
        (rootAtFrattiniEquiv Q split i w v) := by
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (frattini (rootAt Q split i w)) v
  dsimp only [rootAtFrattiniEquiv, rootAtCartanFrattiniAction, rootCartanFrattiniAction,
    MonoidHom.comp_apply]
  rw [quotientAut_apply_mk,QuotientGroup.congr_mk',QuotientGroup.congr_mk',quotientAut_apply_mk]
  congr 1
  apply Subtype.ext
  change (representative w : X ⧸ Q.D)*((h : X ⧸ Q.D)*x*(h : X ⧸ Q.D)⁻¹)*
    (representative w : X ⧸ Q.D)⁻¹ =
    ((representative w : X ⧸ Q.D)*h*(representative w : X ⧸ Q.D)⁻¹)*
    ((representative w : X ⧸ Q.D)*x*(representative w : X ⧸ Q.D)⁻¹)*
    ((representative w : X ⧸ Q.D)*h*(representative w : X ⧸ Q.D)⁻¹)⁻¹
  group

theorem suzuki_rootAt_cartan_frattini_regular (i : Fin 2)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    {m : ℕ} (hm : 0 < m) (μ : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (ν : simpleRoot Q split i ≃* SuzukiRootSubgroup m) (w : Weyl Q) :
    Nat.card (rootAt Q split i w ⧸ frattini (rootAt Q split i w)) = 2^(2*m+1) ∧
    ∀ x y : rootAt Q split i w ⧸ frattini (rootAt Q split i w),
      x ≠ 1 → y ≠ 1 → ∃ h, rootAtCartanFrattiniAction Q split i w h x = y := by
  let e := rootAtFrattiniEquiv Q split i w
  obtain ⟨hc,ht⟩ := suzuki_root_cartan_frattini_regular Q split i hKi hm μ ν
  refine ⟨(Nat.card_congr e.toEquiv).trans hc,?_⟩
  intro x y hx hy
  obtain ⟨h,hh⟩ := ht (e x) (e y) (fun he => hx (e.map_eq_one_iff.mp he))
    (fun he => hy (e.map_eq_one_iff.mp he))
  let c := (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)).normalizerMonoidHom
    ⟨representative w,torus_normalizes (representative w)⟩
  refine ⟨c.symm h,e.injective ?_⟩
  rw [rootAtFrattiniEquiv_action]
  change rootCartanFrattiniAction Q split i (c (c.symm h)) (e x) = e y
  rwa [c.apply_symm_apply]

instance rootAt_isTwo (i : Fin 2) (w : Weyl Q) : Fact (IsPGroup 2 (rootAt Q split i w)) :=
  ⟨(split.isTwo.to_le (simpleRoot_le Q split i)).of_equiv
    (RootAction.conjugateEquiv (simpleRoot Q split i) (representative w)).symm⟩

instance rootAtFrattini_elementary (i : Fin 2) (w : Weyl Q) :
    IsElementaryAbelian 2 (rootAt Q split i w ⧸ frattini (rootAt Q split i w)) :=
  isElementaryAbelian_quotient_frattini

/-- The full Cartan action on a canonical root Frattini quotient over F₂. -/
@[expose] def rootAtCartanFrattiniRepresentation (i : Fin 2) (w : Weyl Q) :
    Representation (ZMod 2) (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))
      (Additive (rootAt Q split i w ⧸ frattini (rootAt Q split i w))) where
  toFun h := (rootAtCartanFrattiniAction Q split i w h).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by ext v; simp only [map_one]; rfl
  map_mul' h k := by ext v; simp only [map_mul]; rfl

theorem suzuki_rootAt_cartan_frattini_irreducible (i : Fin 2)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    {m : ℕ} (hm : 0 < m) (μ : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (ν : simpleRoot Q split i ≃* SuzukiRootSubgroup m) (w : Weyl Q) :
    (rootAtCartanFrattiniRepresentation Q split i w).IsIrreducible ∧
      Module.finrank (ZMod 2)
        (Additive (rootAt Q split i w ⧸ frattini (rootAt Q split i w))) = 2*m+1 := by
  obtain ⟨hc,ht⟩ := suzuki_rootAt_cartan_frattini_regular Q split i hKi hm μ ν w
  let V := rootAt Q split i w ⧸ frattini (rootAt Q split i w)
  let ρ := rootAtCartanFrattiniRepresentation Q split i w
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by
    change 1 < Nat.card (rootAt Q split i w ⧸ frattini (rootAt Q split i w))
    rw [hc]; exact one_lt_pow₀ (by norm_num) (by omega))
  have hir : ρ.IsIrreducible := by
    apply IsSimpleOrder.of_forall_eq_top
    intro S hS
    have hn : S.toSubmodule ≠ ⊥ := fun he => hS (Subrepresentation.toSubmodule_injective he)
    let : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hn
    obtain ⟨x,hx⟩ := exists_ne (0 : S.toSubmodule)
    have hx' : x.val.toMul ≠ 1 := fun he => hx (Subtype.ext (Additive.toMul.injective he))
    apply top_unique
    intro y _
    by_cases hy : y = 0
    · rw [hy]; exact S.toSubmodule.zero_mem
    obtain ⟨h,hh⟩ := ht x.val.toMul y.toMul hx' (fun he => hy (Additive.toMul.injective he))
    have he : ρ h x.val = y := Additive.toMul.injective hh
    exact he ▸ S.apply_mem_toSubmodule h x.property
  refine ⟨hir,?_⟩
  have hd := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
  rw [Nat.card_zmod] at hd
  change Nat.card V = _ at hd
  have hc' : Nat.card V = 2^(2*m+1) := hc
  rw [hc'] at hd
  exact ((Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ))) hd).symm

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
