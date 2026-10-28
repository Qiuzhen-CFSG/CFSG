module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.PerpendicularObstruction
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.BinaryCentralizers

/-!
# Binary perpendicular-root normalization from the quintic fixed group

The genuine binary Suzuki actor is C₅:C₄. Its quintic subgroup is normal,
so the whole actor normalizes the quintic centralizer in the endpoint
radical. If the root Omega centralizes the perpendicular root, the actual
reflection--involution product normalizes that root. Its quintic action
on a group of order four is trivial. The previously proved centralizer
order four now identifies the entire fixed subgroup with that root,
forcing normalization by the original simple root.

The small C₅:C₄ conjugation calculation is kernel checked in its twenty
explicit coordinates; the action and fixed subgroup are then transported
through the literal source actor. This does not assume simplicity of Sz(2).

Source: Fong--Seitz I (1973), binary case of (6H)(b), pp.53--54.
PerpendicularNonzero applies the normalization to (6.1) on the same quotient.
The earlier step proving the required Omega centralization is still needed.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open RootCoordinates HexagonStructure

private instance fiveFour_decEq : DecidableEq FiveFour.Group := fun a b =>
  decidable_of_iff (a.left = b.left ∧ a.right = b.right) SemidirectProduct.ext_iff.symm

private theorem fiveFour_fifth_conjugate :
    ∀ c r : FiveFour.Group, c^5 = 1 → c ≠ 1 →
      ∃ k : Fin 5, r*c*r⁻¹ = c^k.val := by
  decide +kernel

private theorem quintic_normalizes_centralizer {Y : Type*} [Group Y]
    (R V : Subgroup Y) (e : R ≃* FiveFour.Group) (c : R) (hc : orderOf c = 5)
    (hV : R ≤ normalizer (V : Set Y)) :
    R ≤ normalizer ((V ⊓ centralizer ({(c : Y)} : Set Y) : Subgroup Y) : Set Y) := by
  have hc5 : c^5=1 := by rw [←hc,pow_orderOf_eq_one]
  have hconj (r : R) : ∃ k : Fin 5, (r : Y)*(c : Y)*(r : Y)⁻¹ = (c : Y)^k.val := by
    obtain ⟨k,hk⟩ := fiveFour_fifth_conjugate (e c) (e r)
      (by rw [←map_pow,hc5,map_one])
      (e.map_ne_one_iff.mpr (by intro he; rw [he,orderOf_one] at hc; omega))
    refine ⟨k,?_⟩
    have hh : r*c*r⁻¹ = c^k.val := e.injective (by simpa only [map_mul,map_inv,map_pow] using hk)
    exact congrArg Subtype.val hh
  have hforward (r : R) (x : Y) (hx : x ∈ V ⊓ centralizer ({(c : Y)} : Set Y)) :
      (r : Y)*x*(r : Y)⁻¹ ∈ V ⊓ centralizer ({(c : Y)} : Set Y) := by
    refine ⟨(mem_normalizer_iff.mp (hV r.property) x).mp hx.1,?_⟩
    apply mem_centralizer_iff.mpr
    intro y hy
    have hyc : y = c := Set.mem_singleton_iff.mp hy
    subst y
    obtain ⟨k,hk⟩ := hconj r⁻¹
    have hxc : Commute (c : Y) x := mem_centralizer_iff.mp hx.2 _ (Set.mem_singleton _)
    have hh := congrArg (fun z : Y => (r : Y)*z*(r : Y)⁻¹) (hxc.pow_left k.val).eq
    rw [←hk] at hh
    simpa only [Subgroup.coe_inv,inv_inv,mul_assoc,mul_inv_cancel_left,mul_inv_cancel_right,mul_inv_cancel,mul_one] using hh
  intro r hr
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact hforward ⟨r,hr⟩ x
  · intro hx
    simpa only [Subgroup.coe_inv,inv_inv,mul_assoc,inv_mul_cancel_left,inv_mul_cancel_right,inv_mul_cancel,mul_one] using
      hforward (⟨r,hr⟩ : R)⁻¹ (r*x*r⁻¹) hx

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)
  (hV : simpleRemainder Q split i ≤ localKernel Q i)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup 0)
  (hB : (quotientBorel Q i).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)))

include hV hB in
/-- The whole binary source actor normalizes the actual quintic fixed subgroup.
This also supplies the fixed-point argument in the simultaneous-zero branch. -/
theorem binary_mover_centralizer_normalized
    (hm : rotationOrder Q = 8) (j : Fin 2) (hij : i ≠ j)
    (hcomm : ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥) :
    rankOne Q split i ≤ normalizer
      ((simpleRemainder Q split i ⊓ centralizer
        ({(frattiniMover Q split i 0 μ hB : X ⧸ Q.D)} : Set (X ⧸ Q.D)) :
          Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) := by
  exact quintic_normalizes_centralizer _ _
    ((suzukiActorEquiv Q split i 0 μ hB).trans FiveFour.suzukiZeroEquiv.symm) _
    (binary_frattiniMover_order Q split i hV μ hB hm j hij hcomm)
    ((rankOne_le_parabolic Q split i).trans (remainder_parabolic_normalizes Q split i hV))

include hV hB in
/-- In the binary row, centralization by the actual root Omega forces normalization
by the whole root. The order-five fixed group is precisely the perpendicular root. -/
theorem binary_perpendicular_normalizes_of_omega_commutes
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (j : Fin 2) (hij : i ≠ j)
    (hcomm : ⁅omegaOneAmbient (simpleRoot Q split i),rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥)
    (hlinear : Nat.card (simpleRoot Q split j) = 2)
    (hΩ : ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ = ⊥) :
    simpleRoot Q split i ≤ normalizer
      (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) : Set (X ⧸ Q.D)) := by
  let E := rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)
  let V := simpleRemainder Q split i
  let c := frattiniMover Q split i 0 μ hB
  have hEV : E ≤ V := (octagon_three_roots_le_remainder Q split hm i j hij).2.2
  have hEcard : Nat.card E = 4 := by
    change Nat.card (rightConjugate (simpleRoot Q split i)
      (representative (Q.simple j*Q.simple i*Q.simple j) : X ⧸ Q.D)) = 4
    rw [Nat.card_congr (rightConjugateEquiv (simpleRoot Q split i)
      (representative (Q.simple j*Q.simple i*Q.simple j) : X ⧸ Q.D)).symm,
      Nat.card_congr (suzukiRootEquiv Q split i 0 μ hB).toEquiv,matrixRoot_card]
    norm_num
  have ho : orderOf c = 5 := binary_frattiniMover_order Q split i hV μ hB hm j hij hcomm
  have hcn : (c : X ⧸ Q.D) ∈ normalizer (E : Set (X ⧸ Q.D)) := by
    let s := involutoryRootReflection Q split i (UnitarySource.actorReflection Q split i)
    have hs := perpendicular_root_normalizes Q split hm i j hij s.val s.class_eq
    have hu : (suzukiParameter Q split i 0 μ hB 0 1 : X ⧸ Q.D) ∈
        omegaOneAmbient (simpleRoot Q split i) := by
      rw [←suzukiOmegaParameter_range Q split i 0 μ hB]
      exact ⟨Multiplicative.ofAdd 1,rfl⟩
    exact (normalizer (E : Set (X ⧸ Q.D))).mul_mem hs
      ((Subgroup.centralizer_le_normalizer _)
        (commutator_eq_bot_iff_le_centralizer.mp hΩ hu))
  let a : MulAut E := E.normalizerMonoidHom ⟨c,hcn⟩
  have ha5 : a^5 = 1 := by
    have hh : (⟨(c : X ⧸ Q.D),hcn⟩ : normalizer (E : Set (X ⧸ Q.D)))^5 = 1 := by
      apply Subtype.ext
      exact congrArg (fun z : rankOne Q split i => (z : X ⧸ Q.D))
        (show c^5=1 by rw [←ho,pow_orderOf_eq_one])
    rw [←map_pow,hh,map_one]
  have ha : a = 1 := by
    by_contra hne
    have hb := quintic_fixed_index_ge (split.isTwo.to_le (hEV.trans inf_le_left)) a ha5 hne
    have hi := a.fixedSubgroup.index_mul_card
    rw [hEcard] at hi
    have hp := Nat.card_pos (α := a.fixedSubgroup)
    nlinarith
  let C := V ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D))
  have hEC : E ≤ C := by
    refine le_inf hEV ?_
    intro x hx
    apply mem_centralizer_iff.mpr
    intro y hy
    have hyc : y = c := Set.mem_singleton_iff.mp hy
    subst y
    have he := congrArg (fun f : MulAut E => (f ⟨x,hx⟩ : X ⧸ Q.D)) ha
    change (c : X ⧸ Q.D)*x*(c : X ⧸ Q.D)⁻¹ = x at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hEq : E = C := eq_of_le_of_card_ge hEC (by
    rw [hEcard]
    exact (binary_mover_centralizer_card Q split i hV μ hB hc hm j hij hcomm hlinear).le)
  change simpleRoot Q split i ≤ normalizer (E : Set (X ⧸ Q.D))
  rw [hEq]
  apply le_sup_left.trans
  apply quintic_normalizes_centralizer (rankOne Q split i) V
    ((suzukiActorEquiv Q split i 0 μ hB).trans FiveFour.suzukiZeroEquiv.symm) c ho
  exact (rankOne_le_parabolic Q split i).trans (remainder_parabolic_normalizes Q split i hV)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
